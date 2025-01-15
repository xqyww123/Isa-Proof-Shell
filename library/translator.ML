signature ML_TRANSLATOR = sig

end

structure ML_Translator : ML_TRANSLATOR = struct

type source = string
type typ'  = typ * source
type term' = term * source
type var = string * string option * mixfix
type var'= term' * string option * mixfix
type fact = Facts.ref * Token.src list
type      statement = (term' * term' list) list list
type attr_statement = (Attrib.binding * (term' * term' list) list) list
type structured_statement = var' list      (*vars*)
                          * statement      (*assumes*)
                          * attr_statement (*shows*)

exception Translation_Fail of string
exception Unsupported of string

datatype ast =
(* Isar Specific *)
    PROOF  of (Proof.context * ast) list
  | BRCBLK of (Proof.context * ast) list
  | FIX    of var list
  | ASSUME of structured_statement
  | THUS   of structured_statement
  | HENCE  of structured_statement
  | SHOW   of structured_statement
  | CASE   of Attrib.binding
            * (string * string option list)
  | ISAR_OBTAIN   of (binding * (binding * string option * mixfix) list)
                   * structured_statement
  | ISAR_CONSIDER of Element.obtains
  | USING  of fact list
  | DEFER  of int
  | PREFER of int
  | WITH   of fact list
  | FROM   of fact list
  | ISAR_THEN of fact list

(* The Min Lang *)
  | TACTIC of Method.text
  | UNFOLD of fact list
  | CONFIG of (Attrib.binding * fact list) list
  | RULE   of Facts.ref list
  | CRUSH  of var list (*VARS*)
  | INTRO  of var list (*VARS*)
  | ALL_INTRO
  | HAMMER of (*with*) Facts.ref list * (*without*) Facts.ref list
  | END    of (*with*) Facts.ref list * (*without*) Facts.ref list
  | NEXT   of string list (*VARS*) *
              ((*with*) Facts.ref list * (*without*) Facts.ref list)
  | HAVE     of structured_statement
  | NOTATION of Syntax.mode * (string * mixfix) list
  | LET      of (string list * string) list
  | CONSIDER of var list * structured_statement
  | DEFINE   of var' list * attr_statement * var' list
  | OPEN_MODULE of Expression.expression


type eval_steps = (Proof.context * ast) list

(** Helpers **)

fun mk_idt name = Token.make ((2,0), name) Position.none

(** Initial Phase **)

val facts = Parse.and_list1 Parse.thms1
val VARS = Parse.vars >> map (fn (v,t,s) => (Binding.name_of v,t,s))

fun structured_statement ctxt =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
    let val (stmt, ctxt') = Proof_Context.read_statement fixes assumes (map snd shows) ctxt
        val ctxt'P = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
        fun read ctxt = ` (Syntax.read_term ctxt)
     in (map2 (fn fix => fn (_,t,s) => (swap fix,t,s)) (#fixes stmt) fixes,
         map (map (apfst (read ctxt') #> apsnd (map (read ctxt'P)))) assumes,
         map (apsnd (map (apfst (read ctxt') #> apsnd (map (read ctxt'P))))) shows)
    end )

val tactic_parser = K (Method.parse >> (TACTIC o fst))

val fix_parser = K (VARS >> FIX)
fun assume_parser ctxt = structured_statement ctxt >> ASSUME
val unfold_parser = K (facts >> (UNFOLD o flat))
val using_parser  = K (facts >> (USING  o flat))
val case_parser = K ((
        Parse_Spec.opt_thm_name ":" --
      ( \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.name
                    -- Scan.repeat (Parse.maybe Parse.name) --| \<^keyword>\<open>)\<close>)
     || Parse.name >> rpair []))
      >> CASE)

fun define_parser ctxt = (Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes
      >> (fn ((a,b),c) =>
        let val (stmt, ctxt') = Proof_Context.read_statement (a @ c) [] (map #2 b) ctxt
            val ctxt'P = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
            fun read ctxt = ` (Syntax.read_term ctxt)
         in (a |> map2 (fn fix => fn (_,t,s) => (swap fix,t,s)) (take (length a) (#fixes stmt)),
             b |> map (apsnd (map (apfst (read ctxt') #> apsnd (map (read ctxt'P))))),
             c |> map2 (fn fix => fn (_,t,s) => (swap fix,t,s)) (take (length a) (#fixes stmt)) )
         |> DEFINE
        end)

exception IGNORE
fun ignore _ _ = raise IGNORE

fun TODO name _ _ = raise Unsupported name

val initial_parsers = Symtab.make [

  ("apply",      tactic_parser),
  ("apply_end",  tactic_parser),
  ("by",         tactic_parser),
  ("fix",        fix_parser),
  ("assume",     assume_parser),
  ("presume",    assume_parser),
  ("unfolding",  unfold_parser),
  ("using",      using_parser),
  ("case",       case_parser),
  ("write",      K (Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix) >> NOTATION)),
  ("let",        K (Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
                      >> LET)),
  ("define",     define_parser),
  ("supply",     K (Parse_Spec.name_facts >> CONFIG)),
  ("note",       K (Parse_Spec.name_facts >> CONFIG)),
  ("include",    K (Parse_Spec.name_facts >> CONFIG)),

  ("defer",      K (Scan.optional Parse.nat 1 >> DEFER)),
  ("prefer",     K (Scan.optional Parse.nat 1 >> DEFER)),
  ("with",       K (facts >> (WITH o flat))),
  ("from",       K (facts >> (FROM o flat))),
  ("then",       K (facts >> (ISAR_THEN o flat))),

  ("have",       (fn ctxt => structured_statement ctxt >> HAVE)),
  ("show",       (fn ctxt => structured_statement ctxt >> SHOW)),
  ("thus",       (fn ctxt => structured_statement ctxt >> THUS)),
  ("hence",      (fn ctxt => structured_statement ctxt >> HENCE)),

  ("interpret",  K (Parse.!!! Parse_Spec.locale_expression >> OPEN_MODULE)),

  ("next",       K (Scan.succeed (NEXT ([],([],[]))))),
  ("done",       K (Scan.succeed (END ([],[])))),
  (".",          K (Scan.succeed (END ([],[])))),
  ("..",         K (Scan.succeed (END ([],[])))),

  ("{",          TODO "{"),
  ("}",          TODO "}"),
  ("proof",      TODO "proof"),
  ("qed",        TODO "qed"),
  ("subgoal",    TODO "subgoal"),

  ("oops",       TODO "oops"),

  ("also",       ignore),
  ("finally",    ignore),
  ("moreover",   ignore),
  ("ultimately", ignore),
  ("print_trans_rules", ignore),

  ("help",       ignore),
  ("print_commands", ignore),
  ("print_options",  ignore),
  ("print_context",  ignore),
  ("print_theory",   ignore),
  ("print_definitions", ignore),
  ("print_syntax",      ignore),
  ("print_defn_rules",  ignore),
  ("print_abbrevs",     ignore),
  ("print_theorems",    ignore),
  ("print_locales",     ignore),
  ("print_classes",     ignore),
  ("print_locale",      ignore),
  ("print_interps",     ignore),
  ("print_attributes",  ignore),
  ("print_simpset",     ignore),
  ("print_rules",       ignore),
  ("print_methods",     ignore),
  ("print_antiquotations",    ignore),
  ("print_ML_antiquotations", ignore),
  ("locale_deps",             ignore),
  ("print_term_bindings",     ignore),
  ("print_facts",             ignore),
  ("print_cases",             ignore),
  ("print_statement",         ignore),
  ("thm",            ignore),
  ("prf",            ignore),
  ("full_prf",       ignore),
  ("prop",           ignore),
  ("term",           ignore),
  ("typ",            ignore),
  ("print_codesetup",ignore),
  ("print_context_tracing",    ignore),
  ("print_state",              ignore),
  ("welcome",                  ignore)
]


fun initial_pass toks s =
  let fun parse s ret (src::srcs) =
        let val (name,_) = Token.name_of_src src
            val parser = case Symtab.lookup initial_parsers name
                           of SOME parser => parser
                            | NONE => raise Unsupported name
            val tr = Outer_Syntax.parse_span (Toplevel.theory_of s) (fn _ => error "BUG") src
            val s' = Toplevel.command_exception false tr s
         in parse s' (parser (Toplevel.context_of s) (tl src) :: ret) srcs
        end
   in toks
  end

end

