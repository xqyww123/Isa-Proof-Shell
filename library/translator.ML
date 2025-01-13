signature ML_TRANSLATOR = sig

end

structure ML_Translator : ML_TRANSLATOR = struct


type source = string
type typ'  = typ * source
type term' = term * source
type var = (string * string option * mixfix)
type fact = (Facts.ref * Token.src list)

datatype ast =
    TACTIC of Method.text
  | PROOF  of (Proof.context * ast) list
  | BRCBLK of (Proof.context * ast) list
  | FIX    of var list
  | ASSUME of var list         (*vars*)
            * (term' * term' list) list list  (*assumes*)
            * (Attrib.binding * (term' * term' list) list) list  (*shows*)
  | CASE   of Attrib.binding
            * (string * string option list)

  | UNFOLD of fact list
  | RULE   of Facts.ref list
  | CRUSH  of var list (*VARS*)
  | INTRO  of var list (*VARS*)
  | ALL_INTRO
  | HAMMER of (*with*) Facts.ref list * (*without*) Facts.ref list
  | END    of (*with*) Facts.ref list * (*without*) Facts.ref list
  | NEXT   of string list (*VARS*) *
              ((*with*) Facts.ref list * (*without*) Facts.ref list)
  | HAVE   of var list         (*vars*)
            * (Attrib.binding * (term' * term' list) list)  (*assumes*)
            * (Attrib.binding * (term' * term' list) list)  (*shows*)

  | DEFER  of int
  | PREFER of int


type eval_steps = (Proof.context * ast) list


(** Initial Phase **)

val facts = Parse.and_list1 Parse.thms1

val VARS = Parse.vars >> map (fn (v,t,s) => (Binding.name_of v,t,s))
fun structured_statement ctxt =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
    let val (stmt, ctxt') = Proof_Context.read_statement fixes assumes (map snd shows) ctxt
        val ctxt'P = Proof_Context.set_mode (Proof_Context.mode_pattern) ctxt'
        fun read ctxt = ` (Syntax.read_term ctxt)
     in (map (fn (v,t,s) => (Binding.name_of v,t,s)) fixes,
         map (map (apfst (read ctxt') #> apsnd (map (read ctxt'P)))) assumes,
         map (apsnd (map (apfst (read ctxt') #> apsnd (map (read ctxt'P))))) shows)
    end )

val tactic_parser = K (Method.parse >> (TACTIC o fst))

val fix_parser = K (VARS >> FIX)
fun assume_parser ctxt = structured_statement ctxt >> ASSUME
val unfold_parser = K (facts >> (UNFOLD o flat))
val case_parser = K ((
        Parse_Spec.opt_thm_name ":" --
      ( \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.name
                    -- Scan.repeat (Parse.maybe Parse.name) --| \<^keyword>\<open>)\<close>)
     || Parse.name >> rpair []))
      >> CASE)

exception IGNORE
fun ignore _ _ = raise IGNORE

exception Unsupported
fun TODO _ _ = raise Unsupported
fun unsupported _ _ = raise Unsupported

val initial_parsers = Symtab.make [
  ("apply",      tactic_parser),
  ("apply_end",  tactic_parser),
  ("by",         tactic_parser),
  ("fix",        fix_parser),
  ("assume",     assume_parser),
  ("unfolding",  unfold_parser),
  ("case",       case_parser),

  ("defer",      K (Scan.optional Parse.nat 1 >> DEFER)),
  ("prefer",     K (Scan.optional Parse.nat 1 >> DEFER)),

  ("next",       K (Scan.succeed (NEXT ([],([],[]))))),
  ("done",       K (Scan.succeed (END ([],[])))),
  (".",          K (Scan.succeed (END ([],[])))),
  ("..",         K (Scan.succeed (END ([],[])))),

  ("{",          TODO),
  ("}",          TODO),
  ("proof",      TODO),
  ("qed",        TODO),
  ("subgoal",    TODO),

  ("oops",       TODO),
  ("sorry",      unsupported),

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

