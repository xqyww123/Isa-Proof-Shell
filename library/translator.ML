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

exception Parse_Fail of Token.src list
exception Translation_Fail of string
exception Unsupported of string

datatype ast =
(* Isar Specific *)
    PROOF  of Method.text option * (Proof.context * ast) list
  | QED    of Method.text option
  | BRCBLK of (Proof.context * ast) list
  | ENDBLK
  | FIX    of var list
  | ASSUME of structured_statement
  | THUS   of structured_statement * (Proof.context * ast) list
  | HENCE  of structured_statement * (Proof.context * ast) list
  | SHOW   of structured_statement * (Proof.context * ast) list
  | CASE   of Attrib.binding
            * (string * string option list)
  | ISAR_OBTAIN   of ( (binding * (binding * string option * mixfix) list)
                     * structured_statement)
                   * (Proof.context * ast) list
  | ISAR_CONSIDER of Element.obtains
                   * (Proof.context * ast) list
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
  | HAVE     of structured_statement * (Proof.context * ast) list
  | NOTATION of Syntax.mode * (string * mixfix) list
  | LET      of (string list * string) list
  | CONSIDER of var list * structured_statement
  | DEFINE   of var' list * attr_statement * var' list
  | OPEN_MODULE of Expression.expression * (Proof.context * ast) list

type ast' = (Proof.context * ast) list

(** Helpers **)

fun mk_idt name = Token.make ((2,0), name) Position.none

(** Initial Phase **)

val facts = Parse.and_list1 Parse.thms1
val VARS = Parse.vars >> map (fn (v,t,s) => (Binding.name_of v,t,s))

fun structured_statement F ctxt =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
    let val (stmt, ctxt') = Proof_Context.read_statement fixes assumes (map snd shows) ctxt
        val ctxt'P = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
        fun read ctxt = ` (Syntax.read_term ctxt)
     in (ctxt',
          (map2 (fn fix => fn (_,t,s) => (swap fix,t,s)) (#fixes stmt) fixes,
           map (map (apfst (read ctxt') #> apsnd (map (read ctxt'P)))) assumes,
           map (apsnd (map (apfst (read ctxt') #> apsnd (map (read ctxt'P))))) shows)
          |> F )
    end )

exception IGNORE
fun ignore _ _ = raise IGNORE

fun TODO name _ _ = raise Unsupported name

local

fun tactic_parser ctxt = Method.parse >> (pair ctxt o TACTIC o fst)
fun qed_parser ctxt = Scan.option (Method.parse >> fst) >> (pair ctxt o QED)
fun proof_parser ctxt = Scan.option (Method.parse >> fst) >> (pair ctxt o QED)

fun fix_parser ctxt = VARS >> (pair ctxt o FIX)
val assume_parser = structured_statement ASSUME
fun unfold_parser ctxt = facts >> (pair ctxt o UNFOLD o flat)
fun using_parser  ctxt = facts >> (pair ctxt o USING  o flat)
fun case_parser   ctxt = (
        Parse_Spec.opt_thm_name ":" --
      ( \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.name
                    -- Scan.repeat (Parse.maybe Parse.name) --| \<^keyword>\<open>)\<close>)
     || Parse.name >> rpair []))
      >> (pair ctxt o CASE)

fun define_parser ctxt = (Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes
      >> (fn ((a,b),c) =>
        let val (stmt, ctxt') = Proof_Context.read_statement (a @ c) [] (map #2 b) ctxt
            val ctxt'P = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
            fun read ctxt = ` (Syntax.read_term ctxt)
         in (a |> map2 (fn fix => fn (_,t,s) => (swap fix,t,s)) (take (length a) (#fixes stmt)),
             b |> map (apsnd (map (apfst (read ctxt') #> apsnd (map (read ctxt'P))))),
             c |> map2 (fn fix => fn (_,t,s) => (swap fix,t,s)) (take (length a) (#fixes stmt)) )
         |> DEFINE
         |> pair ctxt'
        end)

fun config_parser ctxt = Parse_Spec.name_facts >> (pair ctxt o CONFIG)
fun parser' p ctxt = p >> pair ctxt

in

val initial_parsers = Symtab.make [

  ("apply",      tactic_parser),
  ("proof",      proof_parser),
  ("qed"  ,      qed_parser),
  ("apply_end",  tactic_parser),
  ("by",         tactic_parser),
  ("fix",        fix_parser),
  ("assume",     assume_parser),
  ("presume",    assume_parser),
  ("unfolding",  unfold_parser),
  ("using",      using_parser),
  ("case",       case_parser),
  ("write",      parser' (Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
                      >> NOTATION) ),
  ("let",        parser' (Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
                      >> LET) ),
  ("define",     define_parser),
  ("supply",     config_parser),
  ("note",       config_parser),
  ("include",    config_parser),

  ("defer",      parser' (Scan.optional Parse.nat 1 >> DEFER)),
  ("prefer",     parser' (Scan.optional Parse.nat 1 >> DEFER)),
  ("with",       parser' (facts >> (WITH o flat))),
  ("from",       parser' (facts >> (FROM o flat))),
  ("then",       parser' (facts >> (ISAR_THEN o flat))),

  ("have",       structured_statement (HAVE  o rpair [])),
  ("show",       structured_statement (SHOW  o rpair [])),
  ("thus",       structured_statement (THUS  o rpair [])),
  ("hence",      structured_statement (HENCE o rpair [])),

  ("interpret",  parser' (Parse.!!! Parse_Spec.locale_expression >> (OPEN_MODULE o rpair []))),

  ("next",       parser' (Scan.succeed (NEXT ([],([],[]))))),
  ("done",       parser' (Scan.succeed (END ([],[])))),
  (".",          parser' (Scan.succeed (END ([],[])))),
  ("..",         parser' (Scan.succeed (END ([],[])))),

  ("{",          parser' (Scan.succeed (BRCBLK []))),
  ("}",          parser' (Scan.succeed ENDBLK)),
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

end

datatype blk_behv = OPEN_BLK

val initial_pass : Toplevel.state * Token.src list -> ast' =
  let fun chk_end (ret, []) = ret
        | chk_end (ret, [eof]) =
            if Token.is_eof eof then ret else raise Parse_Fail [[eof]]
        | chk_end (_, src) = raise Parse_Fail [src]

      fun parse (_, []) = raise Parse_Fail []
        | parse (s, src::srcs) =
        let val (name,_) = Token.name_of_src src
            val parser = case Symtab.lookup initial_parsers name
                           of SOME parser => parser
                            | NONE => raise Unsupported name
            val tr = Outer_Syntax.parse_span (Toplevel.theory_of s) (fn _ => error "BUG") src
            val s' = Toplevel.command_exception false tr s

            fun BLK F =
              let val (ast, s_srcs'') = parse (s', srcs)
               in parse s_srcs'' |> apfst (fn L => F ast :: L)
              end

         in case chk_end (parser (Toplevel.context_of s) (tl src))
         of ast as (_, END _) => ([ast], (s', srcs))
          | ast as (_, QED _) => ([ast], (s', srcs))
          | ast as (_, ENDBLK) => ([ast], (s', srcs))
          | (ctxt, HAVE  (smt, _)) => BLK (fn ast => (ctxt, HAVE  (smt, ast)))
          | (ctxt, THUS  (smt, _)) => BLK (fn ast => (ctxt, THUS  (smt, ast)))
          | (ctxt, HENCE (smt, _)) => BLK (fn ast => (ctxt, HENCE (smt, ast)))
          | (ctxt, SHOW  (smt, _)) => BLK (fn ast => (ctxt, SHOW  (smt, ast)))
          | (ctxt, OPEN_MODULE (expr, _)) => BLK (fn ast => (ctxt, OPEN_MODULE (expr, ast)))
          | (ctxt, PROOF (txt, _)) =>
              let val (ast, s_srcs'') = parse (s', srcs)
                  fun chk [] = error "proof is not ended by `qed`"
                    | chk [(_, QED _)] = ()
                    | chk _ = error "proof is not ended by `qed`"
               in chk ast
                ; ([(ctxt, PROOF (txt, ast))], s_srcs'')
              end
          | (ctxt, BRCBLK _) =>
              BLK (fn ast =>
                let fun chk [] = error "`{` is not ended by `}`"
                      | chk [(_, ENDBLK)] = ()
                      | chk _  = error "`{` is not ended by `}`"
                 in chk ast
                  ; (ctxt, BRCBLK ast)
                end)
          | other => parse (s', srcs) |> apfst (fn L => other :: L)
        end
   in parse
   #> (fn (ret, (_, [])) => ret
        | (_, (_, toks)) => raise Parse_Fail toks)
  end

end

