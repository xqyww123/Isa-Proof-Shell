signature IPS_PROOF = sig

type stack
type state
type operation = state -> state
type command = operation parser

exception OPR_FAIL of string

type with_clause = (bool (*with or without*) * string (*name*) * thm) list
type opt_var_names = string option list option

(* options *)

val atomize_goals : bool Config.T
val END_completes_all_NEXT : bool Config.T

(* Operations *)

val INIT : Proof.context -> thm -> state
val INIT': Proof.state -> state

datatype intros_mode = ALL_SUBGOALS | SINGLE_GOAL of binding list option
val INTRO : intros_mode -> operation
val INTRO_CMD : command

val apply : context_tactic -> Time.time option -> stack -> stack
val apply_method : Method.method -> Time.time option -> stack -> stack
val APPLY_CMD : command

val crush_timeout : int Config.T
val CRUSH : intros_mode * with_clause -> operation
val CRUSH_CMD : command

val UNFOLD : thm list -> operation
val UNFOLD_CMD : command

val INDUCT : bool * ((binding option * (term * bool)) option list list *
              (((string * typ) list list * term option list) * thm list option))
          -> opt_var_names
          -> state -> state
val INDUCT_CMD : command

val CASE_SPLIT : bool * (term option list list * thm option) -> opt_var_names -> operation
val CASE_SPLIT_CMD : command

val record_history : string -> operation
val restore_history : string -> operation

val HAVE : (bstring * Token.src list) option -> string -> operation
val HAVE_CMD : command

val CONSIDER : (
               (binding * string option * mixfix) list
             * (binding * string option * mixfix) list
             * (string * string list) list list
             * ((binding * Token.src list) * (string * string list) list) list
             ) list
          -> operation
val CONSIDER_CMD : command

val HAMMER : Sledgehammer.fact_override -> operation
val HAMMER_CMD : command

val END : Sledgehammer.fact_override -> operation
val END_CMD : command

val NXT : opt_var_names -> Sledgehammer.fact_override -> operation
val NXT_CMD : command

val LET : (term list * term) list -> operation
val LET_CMD : command

val PRINT : operation
val PRINT_CMD : command

val RULE : (Facts.ref * Token.src list) list -> (Facts.ref * Token.src list) list -> operation
val RULE_CMD : command

(* Toplevel *)

val parse_cmds : string -> operation
val PROVE : operation -> Proof.context -> thm -> thm

val METHOD : string -> Method.method

end

structure IPS_Proof : IPS_PROOF = struct

(** Preliminaries **)

val assm_N = "assm"
fun assm_name i = assm_N ^ string_of_int i

(* options *)

val atomize_goals = Attrib.setup_config_bool \<^binding>\<open>min_shell_atomize_goals\<close> (K true)
val END_completes_all_NEXT = Attrib.setup_config_bool \<^binding>\<open>END_completes_all_NEXT\<close> (K true)

(*only for printing*)
type variables = (string * typ) list
type local_facts = (string * term list) list
type pctxt = variables * local_facts
datatype tree = PROP  of pctxt * term (*goal*)
              | BUNDL of pctxt * tree list

type param = exn
datatype endblk_type = T_END | T_NXT
datatype frame = HHF   of thm (*a local_facts bundle node, represented as a Hereditary Harrop Formula*)
                        * pctxt
               | MAGIC of (Proof.context -> thm * pctxt * frame list * param -> Proof.context * frame list)
                        * (param -> tree -> tree)
                        * param
               | ENDBLK of endblk_type

val trivial_goal = Goal.protect 0 @{thm TrueI}
exception NO_PARAM

type stack = Proof.context * (frame list)
  (*invariant: the head must be an HHF*)

type state = stack              (*current stack*)
           * stack Symtab.table (*history*)
           * int                (*cache id*)

type operation = state -> state
type command = operation parser

exception BROKEN_INVARIANT

exception OPR_FAIL of string

(* Helpers *)

fun is_protected (\<^Const>\<open>Pure.prop\<close> $ _) = true
  | is_protected (\<^Const>\<open>Pure.imp\<close> $ _ $ X) = is_protected X
  | is_protected (\<^Const>\<open>Pure.all _\<close> $ Abs (_,_, X)) = is_protected X
  | is_protected _ = false

fun mk_binding long_name =
  let val names = Long_Name.explode long_name
      fun mk [] = error "BUG"
        | mk [x] = Binding.name x
        | mk (q::L) = Binding.qualify_name true (mk L) q
   in case names
   of "local"::L => mk L
    | L => mk L
  end

(* Common Syntax *)

type with_clause = (bool (*with or without*) * string (*name*) * thm) list

val with_parser =
        Scan.repeat (   ((Parse.$$$ "WITH"    >> K true ) -- Scan.repeat Parse.thm  )
                     || ((Parse.$$$ "WITHOUT" >> K false) --  Scan.repeat Parse.thm ) )
     >> maps (uncurry (map o pair))

val orverride_parser =
        Scan.repeat (   (Parse.$$$ "WITH"    |-- Scan.repeat Parse.thm >> rpair [])
                     || (Parse.$$$ "WITHOUT" |-- Scan.repeat Parse.thm >>  pair []) )
     >> (fn LL => fold_rev (fn (A,D) => fn (A',D') => (A @ A', D @ D') ) LL ([],[])
               |> (fn (A,D) => {add = A, del = D, only = false}))

fun name_of_ref (Facts.Named ((name,_), _)) = name
  | name_of_ref (Facts.Fact _) = ""

fun read_with ctxt with_lems =
      maps (fn (flag, fact) =>
        let val name = name_of_ref (fst fact)
         in Attrib.eval_thms ctxt [fact]
         |> map (fn th => (flag, name, th) )
        end ) with_lems

fun apply_WITH with_lems =
  fold (fn (flag, name, thm) =>
    Context.proof_map (Phi_Sledgehammer_Solver.with_rule flag name thm)) with_lems

(** Basic Operations **)

structure IPS_Data = Proof_Data (
  type T = ( int Unsynchronized.ref (*counter for fixed premise*)
           * int Unsynchronized.ref (*facts counter*)
           * string                 (*hash used for caching proof*) ) option
  val init = K NONE
)

fun init_ctxt c st = IPS_Data.put (
        SOME (Unsynchronized.ref 0,
              Unsynchronized.ref 0,
              Hasher.term (Thm.prop_of st))
        ) c

fun INIT c st =
  let val facts = Proof_Context.facts_of c;
      val local_facts =
        Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of c)] facts
          |> map (apsnd (map Thm.prop_of))

      val (vars, _) = Variable.constraints_of c
      val vars' = Vartab.fold (fn ((N,~1),T) => (fn L => (N,T) :: L)
                                | _ => I) vars []

   in ((init_ctxt c st, [HHF (st, (vars',local_facts)), ENDBLK T_END]), Symtab.empty, 0)
  end
fun INIT'  st = INIT (Proof.context_of st) (#goal (Proof.simple_goal st))

fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

(* Modus Ponens *)
fun norm_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), Envir.norm_type tyenv T)) tyenv)

fun norm_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.norm_type tyenv TY),
                    Envir.norm_term (Envir.Envir {maxidx = ~1, tenv=tenv,tyenv=tyenv}) TM
                                |> Envir.eta_contract)) tenv)

fun norm_env' (TY,TM) = (norm_tyenv TY, norm_tenv TY TM)
fun certify_tyvars ctxt = TVars.map (K (Context.cases Thm.global_ctyp_of Thm.ctyp_of ctxt))
fun certify_tmvars ctxt = Vars.map (K (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt))
fun certify_vars ctxt (ty, tm) = (certify_tyvars ctxt ty, certify_tmvars ctxt tm)
fun norm_env ctxt (Envir.Envir {tenv, tyenv, ...}) = certify_vars ctxt (norm_env' (tyenv, tenv))

fun MP ctxt thAB thA =
  let val thAB = beta_eta_contract thAB
      val thA  = beta_eta_contract thA
      val LHS = Thm.cprop_of thAB
             |> Thm.dest_arg1

      fun qnum (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, A)) = 1 + qnum A
        | qnum _ = 0
      val diff = qnum (Thm.term_of LHS) - qnum (Thm.prop_of thA)
      val (thAB', thA') =
          if diff <= 0
          then (Thm.instantiate (Thm.match (LHS, Thm.cprop_of thA)) thAB |> beta_eta_contract,
                thA)
          else let
              val frees = Term.declare_term_frees (Thm.prop_of thA)
                              (Term.declare_term_frees (Thm.term_of LHS) Name.context)
              val names = Name.invent frees "x" diff 
              val (fixes, LHS') = fold_map (fn name => Thm.dest_abs_fresh name o Thm.dest_arg)
                                           names LHS
              val thA = Thm.incr_indexes (Thm.maxidx_of thAB + 1) thA
              val inst = Unify.smash_unifiers (Context.Proof ctxt)
                                              [(Thm.term_of LHS', Thm.prop_of thA)]
                                              (Envir.empty (Thm.maxidx_of thA + 1))
                     |> Seq.pull
                     |> (fn SOME (ret, _) => ret
                          | NONE => raise THM ("unification fail", 1, [thAB, thA]))
                     |> norm_env (Context.Proof ctxt)
              val thAB = Thm.instantiate inst thAB |> beta_eta_contract
              val thA  = Thm.instantiate inst thA  |> beta_eta_contract
                                                   |> fold_rev Thm.forall_intr fixes

           in (thAB, thA)
          end

   in Thm.implies_elim thAB' thA'
  end

fun join_lstR pr = AList.join (op =) (fn _ => fn (_,x) => x) pr
fun join_lstL pr = AList.join (op =) (fn _ => fn (x,_) => x) pr

(* Helpers II *)

fun elim_conjs ctxt =
  let fun elim thm =
      case Thm.prop_of thm
        of \<^Const>\<open>Pure.conjunction\<close> $ _ $ _ =>
            elim (MP ctxt @{thm Pure.conjunctionD1} thm) @
            elim (MP ctxt @{thm Pure.conjunctionD2} thm)
         | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.conj\<close> $ _ $ _) =>
            elim (MP ctxt @{thm HOL.conjunct1} thm) @
            elim (MP ctxt @{thm HOL.conjunct2} thm)
         | _ => [thm]
   in elim
  end

fun wraps ctxt ths = ths
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm TAG_def[symmetric]})))
      |> foldr1 (fn (A,B) => MP ctxt (MP ctxt @{thm conjI} A) B)

val is_tagged =
  let fun chk (\<^Const>\<open>Trueprop\<close> $ X) = chk X
        | chk (\<^Const>\<open>TAG _\<close> $ _) = true
        | chk (\<^Const>\<open>HOL.conj\<close> $ A $ B) = chk A andalso chk B
        | chk (\<^Const>\<open>Pure.imp\<close> $ A $ B) = chk A orelse chk B
        | chk (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, X)) = chk X
        | chk _ = false
   in chk
  end

fun is_Trueprop (\<^Const>\<open>Trueprop\<close> $ _) = true
  | is_Trueprop _ = false

fun is_tagged_Trueprop x = is_Trueprop x andalso is_tagged x

fun remove_TAG_premises ctxt th =
  let fun conv ctxt ctm =
        let val tm = Thm.term_of ctm
         in if exists is_tagged (Logic.strip_imp_prems tm)
          then case tm
            of \<^Const>\<open>Pure.imp\<close> $ X $ _ =>
                if is_tagged_Trueprop X
                then (case X
                  of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>conj\<close> $ _ $ _) =>
                      (Conv.rewr_conv @{thm BNF_Fixpoint_Base.conj_imp_eq_imp_imp}
                       then_conv conv ctxt) ctm
                   | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>TAG _\<close> $ _) =>
                      (Conv.arg1_conv (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm TAG_def}))
                       then_conv conv ctxt) ctm)
                else Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) ctm
             | \<^Const>\<open>Pure.all _\<close> $ Abs (_, _, _) =>
                  Conv.abs_conv (fn (_,ctxt) => conv ctxt) ctxt ctm
          else Conv.all_conv ctm
        end
   in if exists is_tagged (Thm.prems_of th)
      then Conv.fconv_rule (conv ctxt) th
      else th
  end

fun unwrap_conjs' ctxt th = th
      |> elim_conjs ctxt
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv @{thm TAG_def})))

fun unwrap_conjs ctxt th =
      if is_Trueprop (Thm.prop_of th) andalso is_tagged (Thm.prop_of th)
      then unwrap_conjs' ctxt th
      else raise THM ("Not tagged", 0, [th])

(*
fun unwrap ctxt th = th
      |> unwrap_conjs ctxt
      |> map (remove_TAG_premises ctxt)
*)

(* Maintain *)

(*primary is the newer. The newer is appended to the list*)
fun cat_pctxt (vs',hs') (vs,hs)
      = (join_lstR (vs', vs), join_lstL (hs', hs))
(*
fun append_print pctxt' (PROP (pctxt, goal))
      = (PROP  (cat_pctxt pctxt' pctxt, goal))
  | append_print pctxt' (BUNDL (pctxt, goal))
      = (BUNDL (cat_pctxt pctxt' pctxt, goal))
*)
fun prepend_print pctxt' (PROP (pctxt, goal))
      = (PROP  (cat_pctxt pctxt pctxt', goal))
  | prepend_print pctxt' (BUNDL (pctxt, goal))
      = (BUNDL (cat_pctxt pctxt pctxt', goal))

fun maintain (c,[]) = (c,[])
  | maintain (origin as (ctxt, HHF (st, pctxt) :: L)) =
    ( case Thm.nprems_of st
        of 0 => (case L
            of [] => origin
             | (HHF (st1, pctxt') :: L') =>
                  maintain (ctxt, HHF (MP ctxt st1 st, cat_pctxt pctxt pctxt') :: L')
             | (MAGIC (cb,_,param) :: L') =>
                  (case cb ctxt (st, pctxt, L', param) of (ctxt', S) => maintain (ctxt', S) )
             | ENDBLK _ :: _ => origin )
         | _ => origin)
  | maintain (_, MAGIC _ :: _) = raise BROKEN_INVARIANT
  | maintain (_, ENDBLK _ :: _) = raise BROKEN_INVARIANT


fun need_intro st =
  let fun need' (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _) = true
        | need' (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _) = true
        | need' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = need' X
        | need' (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) = true
        | need' (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) = true
        | need' _ = false
   in case Thm.prop_of st
        of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ _) => need' G
         | _ => false
  end

(*fix local variables & facts*)
datatype intros_mode = ALL_SUBGOALS | SINGLE_GOAL of binding list option

fun strip_meta_hhf term =
  let fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
        | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
        | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
            strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | strip (V,P) X = (rev V, rev P, X)
   in strip ([],[]) term end

fun INTRO'' F mode (origin as (ctxt, HHF (st0, pctxt) :: L)) =
   (case Thm.nprems_of st0
      of 0 => origin
       | _ => if Thm.nprems_of st0 > 1 orelse need_intro st0
              then let val st = st0
                             |> Seq.REPEAT (Thm.biresolution NONE true
                                      [(false, @{thm allI}), (false, @{thm impI})] 1)
                             |> Seq.hd

                       val (foc, st') = Subgoal.focus_prems ctxt 1
                                          ((case mode of ALL_SUBGOALS => NONE
                                                       | SINGLE_GOAL bs => bs)
                                           |> (fn NONE => Thm.prop_of st
                                                       |> Logic.dest_implies |> fst
                                                       |> strip_meta_hhf
                                                       |> #1 |> map #1
                                                       |> (fn L => fold_map Name.variant L
                                                                        (Variable.names_of ctxt))
                                                       |> #1
                                                       |> map Binding.name
                                                       |> SOME
                                                | some => some))
                                          st
                       val PRT = K (prepend_print pctxt
                                  o prepend_print (map (
                                         snd
                                      #> Thm.term_of
                                      #> Term.dest_Free
                                      #> apfst (Variable.revert_fixed (#context foc)
                                   )) (#params foc), []) )
                       val (st'', (pctxt', ctxt')) = F (st', foc)
                       fun CB ctxt'' (st'',_,S,_) =
                        let val st'3 = singleton (Proof_Context.export ctxt'' ctxt') st''
                         in (ctxt, HHF (
                                   Subgoal.retrofit ctxt'' ctxt (#params foc) (#asms foc) 1 st'3 st
                                |> Seq.hd,
                              ([],[])) :: S)
                         |> mode = ALL_SUBGOALS ? INTRO'' F mode
                        end
                    in if Thm.nprems_of st0 > 1
                    then (ctxt', HHF (st'', pctxt') :: ENDBLK T_NXT :: MAGIC (CB,PRT,NO_PARAM) :: L)
                    else (ctxt', HHF (st'', pctxt') :: MAGIC (CB,PRT,NO_PARAM) :: L)
                   end
              else (ctxt, HHF (st0, pctxt) :: L)
    )
  | INTRO'' _ _ _ = raise BROKEN_INVARIANT

val INTRO' = INTRO'' (fn (st, foc) =>
  let val ctxt = #context foc
      val SOME (ii,_,_) = IPS_Data.get ctxt
      val i = !ii
      val _ = ii := i + 1
   in ctxt
   |> Proof_Context.note_thms "" ((Binding.name (assm_name i), []),
                                  map (fn th => ([th], [])) (#prems foc))
   |> apfst (apsnd (map Thm.prop_of) #> single #> pair [])
   |> pair st
  end )

fun raw_apply tac timeout (ctxt, HHF (st, facts) :: L) =
    ( case (case timeout
              of SOME time => Timeout.apply time Seq.pull (tac (ctxt, st))
               | NONE      => Seq.pull (tac (ctxt, st)) )
        of NONE => raise OPR_FAIL "Fail to apply the tactic"
         | SOME (Seq.Result (ctxt', st'), _) => (ctxt', HHF (st', facts) :: L)
         | SOME (Seq.Error E, _) => raise OPR_FAIL (E ()) )
  | raw_apply _ _ _ = raise BROKEN_INVARIANT

fun apply' tac timeout s = maintain (raw_apply tac timeout s)

fun apply tac time s = apply' tac time s
      handle Timeout.TIMEOUT _ => raise OPR_FAIL "Timeout"

fun apply_method meth timeout s = apply (meth []) timeout s


fun record_history name (s,his,ID) = (s, Symtab.update (name,s) his,ID)
fun restore_history name (_,his,ID) =
    case Symtab.lookup his name
      of NONE => raise OPR_FAIL ("history " ^ name ^ " not found")
       | SOME s => (s, his,ID)

fun SKIP_SUCCESS F (SK as (_, HHF (st,_) :: _)) =
        if Thm.no_prems st then SK else F SK
  | SKIP_SUCCESS F SK = F SK
fun OPR (f : stack -> stack) ((S,TAB,ID) : state) : state
  = (f S, TAB, ID+1)
fun OPR_ID (f : int -> stack -> stack) ((S,TAB,ID) : state) : state
  = (f ID S, TAB, ID+1)

fun CONTEXTUAL_CMD (parser : Proof.context -> command)
                   (toks : Token.src)
  = ((fn (s:state) => fst (parser (#1 (#1 s)) toks) s), [])


val INTRO = OPR o INTRO'
val VARS_KWD = (Parse.$$$ "VARS" || Parse.$$$ "vars")
val VARS = VARS_KWD |-- Scan.repeat Parse.binding
val VARS_FOR_SINGLE_GOAL = Scan.option VARS >> SINGLE_GOAL
val IN = (Parse.$$$ "IN" || Parse.$$$ "in")

val INTRO_CMD = VARS_FOR_SINGLE_GOAL >> INTRO
val INTRO_ALL_CMD = Scan.succeed (INTRO ALL_SUBGOALS)

val SOLVED_GOAL = \<^prop>\<open>True\<close>

fun print_stack [] = PROP (([], []), SOLVED_GOAL)
  | print_stack (S::L) =
      let fun prt t [] = t
            | prt t (HHF (st, pctxt) :: L) =
                let val goals = case Thm.prems_of st
                                  of [] => raise BROKEN_INVARIANT
                                   | (_::prems) => prems
    
                    val nodes = map (fn goal => PROP (([],[]), goal)) goals
                 in prt (BUNDL (pctxt, t::nodes)) L
                end
            | prt t (MAGIC (_, PRT, param) :: L) = prt (PRT param t) L
            | prt t (ENDBLK _ :: L) = prt t L
          fun prt0 (HHF (st, pctxt)) = PROP (pctxt, Thm.prop_of st)
            | prt0 _ = raise BROKEN_INVARIANT
       in prt (prt0 S) L
      end

val collect_context =
  let fun collect V F (PROP  ((V',F'),term)) = (V @ V', F @ F', term)
        | collect V F (BUNDL ((V',F'),chil)) = collect (V @ V') (F @ F') (hd chil)
   in collect [] []
  end

fun fold_all_names f (PROP ((V,F),_)) x =
      x |> fold (f o fst) V |> fold (f o fst) F
  | fold_all_names f (BUNDL ((V,F), chil)) x =
      x |> fold (f o fst) V |> fold (f o fst) F
        |> fold (fold_all_names f) chil

fun quanlifiers_of tree =
  let fun merge [] L = L
        | merge [_] L = L
        | merge (h::L') L = merge L' (insert (op =) h L)
   in fold_all_names (merge o Long_Name.explode) tree []
  end

(** Interfaces **)


(*fun INTRO_ALL (ctxt, HHF (st, facts) :: L) = *)


(* APPLY *)

fun APPLY text =
      OPR (fn SK as (ctxt, _) =>
        apply_method (Method.evaluate_runtime text ctxt) NONE SK)

val APPLY_CMD = Method.parse >> (fn (m,_) => APPLY m)

(* UNFOLD *)

fun UNFOLD' prep_thms raw_defs (ctxt, HHF (st, pctxt) :: S) =
  let val defs = prep_thms ctxt raw_defs
      val st' = Local_Defs.unfold_goals ctxt defs st
   in (ctxt, HHF (st', pctxt) :: S)
  end
  | UNFOLD' _ _ _ = raise BROKEN_INVARIANT

fun simp_name name =
  if String.isPrefix "local." name
  then String.substring (name, 6, size name - 6)
  else name


fun UNFOLD_FACT' prep_thms raw_defs fact_names (ctxt, SK as HHF (st, pctxt) :: S) =
  let val defs = prep_thms ctxt raw_defs
      val fact_names = if member (op =) fact_names "*"
                       then collect_context (print_stack SK)
                         |> #2
                         |> map (#1 #> simp_name)
                       else fact_names
      val facts = map ( Proof_Context.get_thms ctxt
                     #> map ( Local_Defs.unfold ctxt defs ) ) fact_names
   in ctxt
   |> Proof_Context.note_thmss "" ( map (rpair [] o Binding.name) fact_names
                                      ~~ map (single o rpair []) facts)
   |-> (fn new_facts =>
     rpair (HHF (st, cat_pctxt ([], map (apsnd (map Thm.prop_of)) new_facts) pctxt) :: S))
  end
  | UNFOLD_FACT' _ _ _ _ = raise BROKEN_INVARIANT

val UNFOLD = OPR o UNFOLD' (K I)
val UNFOLD_CMD = Parse.thms1 -- Scan.option (IN |-- Scan.repeat1 Parse.name) >> (
      fn (defs, NONE)       => OPR (UNFOLD' Attrib.eval_thms defs)
       | (defs, SOME facts) => OPR (UNFOLD_FACT' Attrib.eval_thms defs facts) )


(* INIT PROCESS *)

fun TRY_STANDARD (SK as (ctxt, HHF (st, _) :: _)) =
 (let val thy = Proof_Context.theory_of ctxt
      val [\<^Const>\<open>Trueprop\<close> $ goal] = Thm.prems_of st
      val Const(name, _) = head_of goal
      fun pass [] = []
        | pass ["class", x] = [x]
        | pass (h::L) = h :: pass L
      fun qchk [] = false
        | qchk ["class", _] = true
        | qchk (_::L) = qchk L
      val idts = Long_Name.explode name
      val name' = if qchk idts then Long_Name.implode (pass idts) else name
   in if Locale.defined thy name'
    then apply' (CONTEXT_TACTIC (Classical.standard_tac ctxt [])) NONE SK
    else SK
  end handle Bind => SK )
  | TRY_STANDARD _ = raise BROKEN_INVARIANT

val INIT_PROCESS = TRY_STANDARD

local
(*
fun read_trrules thy raw_rules =
  let
    val ctxt = Proof_Context.init_global thy;
    val read_root =
      #1 o dest_Type o Proof_Context.read_type_name {proper = true, strict = false} ctxt;
  in
    raw_rules
    |> map (Syntax.map_trrule (fn (r, s) => Syntax_Phases.parse_ast_pattern ctxt (read_root r, s)))
  end;

val trrules = read_trrules \<^theory> [
      Syntax.Parse_Rule (("logic", "(a \<le> b) \<le> c"), ("logic", "a \<le> b \<and> b \<le> c")),
      Syntax.Parse_Rule (("logic", "(a < b) < c"), ("logic", "a < b \<and> b < c")),
      Syntax.Parse_Rule (("logic", "a = b = c"), ("logic", "a = b \<and> b = c")),
      Syntax.Parse_Rule (("logic", "a \<longleftrightarrow> b \<longleftrightarrow> c"), ("logic", "a \<longleftrightarrow> b \<and> b \<longleftrightarrow> c"))
  ]
*)

val term_qchk = exists_subterm (
      fn Const(\<^const_name>\<open>less\<close>, _) $ (Const(\<^const_name>\<open>less\<close>, _) $ A $ B) $ C => true
       | Const(\<^const_name>\<open>less_eq\<close>, _) $ (Const(\<^const_name>\<open>less_eq\<close>, _) $ A $ B) $ C => true
       | Const("HOL.eq", _) $ (Const("HOL.eq", _) $ A $ B) $ C => true
       | Const("HOL.iff", _) $ A $ (Const("HOL.iff", _) $ B $ C) => true
       | _ => false )


fun term_check tm =
  if term_qchk tm
  then let
      fun maptm (Const(\<^const_name>\<open>less\<close>, _) $ (Const(\<^const_name>\<open>less\<close>, T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const(\<^const_name>\<open>less\<close>, T1) $ A $ B)
                          $ (Const(\<^const_name>\<open>less\<close>, T1) $ B $ C)
        | maptm (Const(\<^const_name>\<open>less_eq\<close>, _) $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ A $ B)
                          $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ B $ C)
        | maptm (Const("HOL.eq", _) $ (Const("HOL.eq", T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const("HOL.eq", T1) $ A $ B)
                          $ (Const("HOL.eq", T1) $ B $ C)
        | maptm (Const("HOL.iff", _) $ (Const("HOL.iff", T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const("HOL.iff", T1) $ A $ B)
                          $ (Const("HOL.iff", T1) $ B $ C)
        | maptm (origin as (A $ B)) =
            let val A' = maptm A
                val B' = maptm B
             in if pointer_eq (A', A) andalso pointer_eq (B', B)
                then origin
                else A' $ B'
            end
        | maptm (origin as Abs (N,T,X)) =
            let val X' = maptm X
             in if pointer_eq (X', X)
                then origin
                else Abs (N, T, X')
            end
        | maptm X = X
   in maptm tm
  end
  else tm

in

fun INIT_SYNTAX ctxt = ctxt
  |> Proof_Context.notation false Syntax.mode_default [
      (Const (\<^const_name>\<open>less_eq\<close>, dummyT), Mixfix (Input.string "(_/ \<le> _)", [51, 51], 50, Position.no_range)),
      (Const (\<^const_name>\<open>less\<close>,    dummyT), Mixfix (Input.string "(_/ < _)",     [51, 51], 50, Position.no_range))
    ]
  |> Proof_Context.notation true Syntax.mode_default [
      (Const (\<^const_name>\<open>less_eq\<close>, dummyT), Mixfix (Input.string "(_/ \<le> _)", [50, 51], 50, Position.no_range)),
      (Const (\<^const_name>\<open>less\<close>,    dummyT), Mixfix (Input.string "(_/ < _)",     [50, 51], 50, Position.no_range))
    ]
  |> Context.proof_map (Syntax_Phases.term_check ~200 "a < b < c" (K (map term_check)))

end

(* Crush *)

val crush_timeout = Attrib.setup_config_int \<^binding>\<open>crush_timeout\<close> (K 10) (*in seconds*)

fun CRUSH' _ _ (ctxt, []) = (ctxt, [])
  | CRUSH' prep_with (imode, raw_with_lems) (s as (ctxt, _)) =
  let val with_lems = prep_with ctxt raw_with_lems
      val ctxt = apply_WITH with_lems ctxt
      val time = Config.get ctxt crush_timeout
              |> Time.fromSeconds
   in
   (( raw_apply (CONTEXT_TACTIC (Clasimp.auto_tac ctxt)) (SOME time) s
      handle Timeout.TIMEOUT _ => 
      raw_apply (CONTEXT_TACTIC (Clasimp.clarsimp_tac ctxt 1)) (SOME time) s)
      handle OPR_FAIL E =>
                (case s of (_, HHF (st, _) :: _) =>
                                if need_intro st then s else raise OPR_FAIL E
                         | _ => raise OPR_FAIL E )
           | Timeout.TIMEOUT _ =>
                raise OPR_FAIL "Timeout")
   |> SKIP_SUCCESS (INTRO' imode)
  end

val CRUSH = OPR o (CRUSH' (K I))

val CRUSH_CMD =
      ( Scan.optional (VARS >> (SINGLE_GOAL o SOME)) ALL_SUBGOALS
     -- with_parser )
     >> (OPR o CRUSH' read_with)

(* INDUCT & CASE *)

type opt_var_names = string option list option
exception CASE_NAME of opt_var_names

fun map2_opt _ [] [] = []
  | map2_opt f [] (y :: ys) = f NONE y :: map2_opt f [] ys
  | map2_opt f (x :: xs) (y :: ys) = f x y :: map2_opt f xs ys
  | map2_opt _ _ _ = raise ListPair.UnequalLengths

fun CASES' ADDITIONAL_NOTES tac first_vars (SK as (ctxt0, HHF (st00, _) :: _)) =
  apply' tac NONE SK |> (fn (ctxt, SK as HHF (rule, pctxt0) :: REMAIN_SK) =>
   let val cases = Proof_Context.dest_cases (SOME ctxt0) ctxt
       val used_qualifiers = quanlifiers_of (print_stack SK)
       val cases = Name.variant_list used_qualifiers (map #1 cases)
                ~~ map #2 cases
       fun CB initial rule cases
              ctxt' (lem, _, SK, param) =
        let val rule' =
                if initial then rule
                else lem
                  |> is_protected (Thm.prop_of lem) ? Goal.conclude
                  |> singleton (Proof_Context.export ctxt' ctxt)
                  |> not initial ? MP ctxt rule
         in case cases
         of [] =>
            (ctxt, HHF (rule', pctxt0) :: SK)
          | ((name, kase) :: remaining_cases) =>
        let val opt_case_name = case param of CASE_NAME param => param
                                            | NO_PARAM => NONE
                                            | _ => raise BROKEN_INVARIANT
            val name = if Char.isAlpha (String.sub (name, 0)) then name
                       else "case_" ^ name
            val kase = case kase
                  of Rule_Cases.Case {fixes, assumes, binds, cases} =>
                     Rule_Cases.Case {
                       fixes = (
                         case opt_case_name
                           of SOME fixes' =>
                              map2_opt (fn NONE => I
                                         | SOME name => fn (_, T) => (Binding.name name, T)
                                       ) fixes' fixes
                            | _ => fold_map (fn (B,T) => fn names =>
                              let val name = Binding.name_of B
                                  val name = if Name.is_internal name then Name.dest_internal name
                                                                      else name
                                  (* val (name, names) = if name = ""
                                                      then Name.variant "case" names
                                                      else (name, names) *)
                                  (* val (name, names) = Name.variant name names *)
                               in ((Binding.name name,T), names)
                              end ) fixes (Variable.names_of ctxt)
                              |> #1 ),
                       assumes = map_index (fn (i,(N,tms)) =>
                                    if N = "" then ("prem" ^ string_of_int i, tms)
                                              else (N, tms) ) assumes,
                       binds=binds,
                       cases=cases
                     }

            val Rule_Cases.Case {fixes, cases, binds, ...} = kase
            val _ = if null cases then () else error "XQY: Unsupported! #1"

            
            val (asms, ctxt) = Proof_Context.apply_case kase ctxt

            fun is_case x t =
                x = Rule_Cases.case_conclN andalso not (Term.exists_subterm Term.is_Var t);
            val goal =
               (if exists (fn ((x, _), SOME t) => is_case x t | _ => false) binds
                then Vartab.lookup (Variable.binds_of ctxt) (Rule_Cases.case_conclN, 0)
                  |> (fn SOME (\<^Type>\<open>bool\<close>, goal) => HOLogic.mk_Trueprop goal
                       | _ => error "BUG 0ejOD0qNRfaTJCrbK7lH3w")
                  |> Thm.cterm_of ctxt
                else Thm.cprop_of st00
                  |> Thm.dest_arg1)
                  |> Goal.init

            val binding = Binding.name name
            val bindings = map (rpair [] o Binding.qualify_name true binding o fst) asms

            fun export is_G asms =
                let val (A,B) = Assumption.assume_export is_G asms
                 in (A #> Thm.permute_prems 0 (length asms) ,B)
                end
         in ctxt
         |> fold_burrow ( Assumption.add_assms export
                        o map (Thm.cterm_of ctxt) ) (map #2 asms)
         |-> (fn thms =>
           let val tagged = maps (filter (is_tagged_Trueprop o Thm.prop_of)) thms
               val thms   = map (filter_out (is_tagged_Trueprop o Thm.prop_of)) thms
               val notes = bindings ~~ thms
                        |> filter_out (null o snd)
                        |> map (apsnd (map (fn th => ([remove_TAG_premises ctxt th], []))))
            in Proof_Context.note_thmss "" (ADDITIONAL_NOTES ctxt tagged @ notes)
           end )
         |-> (fn thms =>
        let val pctxt' = (map (apfst Binding.name_of) fixes, map (apsnd (map Thm.prop_of)) thms)
         in if null remaining_cases
         then rpair ( HHF (goal, pctxt')
                 :: MAGIC (CB false rule' remaining_cases, K I, NO_PARAM)
                 :: SK)
         else rpair ( HHF (goal, pctxt')
                 :: ENDBLK T_NXT
                 :: MAGIC (CB false rule' remaining_cases, K I, NO_PARAM)
                 :: SK)
        end )
        end
        end
    in CB true rule cases ctxt (Drule.dummy_thm, ([],[]), REMAIN_SK, CASE_NAME first_vars)
   end
     | _ => raise BROKEN_INVARIANT)
  | CASES' _ _ _ _ = raise BROKEN_INVARIANT

(* Syntax *)

local (*copied from $ISABELLE_HOME/src/Tools/induct.ML*)

val arbitraryN = "arbitrary";
val takingN = "taking";
val ruleN = "rule";

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ arbitraryN || Args.$$$ takingN || Args.$$$ Induct.typeN ||
    Args.$$$ Induct.predN || Args.$$$ Induct.setN || Args.$$$ ruleN) -- Args.colon)) scan;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val inst' = Scan.lift (Args.$$$ "_") >> K NONE ||
  Args.term >> (SOME o rpair false) ||
  Scan.lift (Args.$$$ "(") |-- (Args.term >> (SOME o rpair true)) --|
    Scan.lift (Args.$$$ ")");

val def_inst =
  ((Scan.lift (Args.binding --| (Args.$$$ "\<equiv>" || Args.$$$ "==")) >> SOME)
      -- (Args.term >> rpair false)) >> SOME ||
    inst' >> Option.map (pair NONE);

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

val arbitrary = Scan.optional (Scan.lift (Args.$$$ arbitraryN -- Args.colon) |--
  Parse.and_list1' (Scan.repeat (unless_more_args free))) [];

val taking = Scan.optional (Scan.lift (Args.$$$ takingN -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_pred =
  named_rule Induct.typeN (Args.type_name {proper = false, strict = false}) get_type ||
  named_rule Induct.predN (Args.const {proper = false, strict = false}) get_pred ||
  named_rule Induct.setN (Args.const {proper = false, strict = false}) get_pred ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

val induct_rule = rule Induct.lookup_inductT Induct.lookup_inductP;
val cases_rule = rule Induct.lookup_casesT Induct.lookup_casesP >> single_rule;


val ind_synt' =
      (Scan.lift (Args.mode Induct.no_simpN) --
      (Parse.and_list' (Scan.repeat (unless_more_args def_inst)) --
        (arbitrary -- taking -- Scan.option induct_rule)))

fun ind_synt ctxt toks = case ind_synt' (ctxt, toks) of (x, (_, toks)) => (x,toks)

val case_synt' =
      (Scan.lift (Args.mode Induct.no_simpN) --
        (Parse.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule))

fun case_synt ctxt toks = case case_synt' (ctxt, toks) of (x, (_, toks)) => (x,toks)

in

fun INDUCT' (no_simp, (insts, ((arbitrary, taking), opt_rule))) first_vars (ctxt, SK) =
  let val (_, facts, _) = collect_context (print_stack SK)
      val facts = map (fn (name, _) => (name, Proof_Context.get_thms ctxt name)) facts
      
      val dirty_frees = fold (fold (fn NONE => I
                                     | SOME (_, (X, _)) => Term.add_frees X)) insts []
                     |> fold (curry (merge (op =))) arbitrary
      val dirty = member (op =) dirty_frees

      val tamper_facts = map (apsnd (map (` ( Term.exists_subterm (fn Free f => dirty f
                                                                    | _ => false)
                                            o Thm.prop_of)))) facts
                      |> filter (exists fst o snd)
      val tamper_fact' = maps (map_filter (fn (true, x) => SOME x | _ => NONE) o snd) tamper_facts

      val tac = Induct.induct_context_tactic (not no_simp) insts arbitrary taking opt_rule
                  (if null tamper_fact' then [] else [wraps ctxt tamper_fact']) 1

      fun update_tampered ctxt th =
        let val ths = unwrap_conjs ctxt th
            fun burrow' [] _ = []
              | burrow' ((true , _ ) :: L) (th::ths) = th :: burrow' L ths
              | burrow' ((false, th) :: L) (    ths) = th :: burrow' L ths
              | burrow' _ _ = error "BUG"
            fun burrow'2 [] ths = ths
              | burrow'2 ((true , _) :: L) (_ ::ths) = burrow'2 L ths
              | burrow'2 ((false, _) :: L) (    ths) = burrow'2 L ths
              | burrow'2 _ _ = error "BUG"
            fun burrow [] [] = []
              | burrow ((N, L) :: L') ths = (N, burrow' L ths) :: burrow L' (burrow'2 L ths)
              | burrow _ _ = error "BUG"
            val tamper_facts'' = burrow tamper_facts ths
         in map (fn (B,ths) => ((mk_binding B, []), [(ths,[])]) ) tamper_facts''
        end
   in CASES' (maps o update_tampered) tac first_vars (ctxt, SK)
  end

fun CASE_SPLIT' (no_simp, (insts, opt_rule)) =
  let val tac = Induct.cases_context_tactic (not no_simp) insts opt_rule [] 1
   in CASES' (K (K [])) tac
  end

val OPT_VARS = Scan.option (VARS_KWD |-- Scan.repeat (Parse.maybe Parse.name))

val INDUCT = OPR oo INDUCT'
val INDUCT_CMD = CONTEXTUAL_CMD (fn ctxt =>
         ind_synt (Context.Proof ctxt) -- OPT_VARS
      >> (fn ((no_simp, (insts, ((arbitrary, taking), opt_rule))), vars) =>
          INDUCT (no_simp, (insts, ((arbitrary, taking), opt_rule))) vars ))

val CASE_SPLIT = OPR oo CASE_SPLIT'
val CASE_SPLIT_CMD = CONTEXTUAL_CMD (fn ctxt =>
         case_synt (Context.Proof ctxt) -- OPT_VARS
      >> (fn ((no_simp, (insts, opt_rule)), vars) =>
          CASE_SPLIT (no_simp, (insts, opt_rule)) vars) )

end

(* RULE *)

fun RULE'_i rules facts =
  apply' (fn s => CONTEXT_TACTIC (HEADGOAL (Classical.rule_tac (#1 s) rules facts)) s) NONE

fun RULE' [] raw_facts (SK as (ctxt, _)) =
  let val facts = Attrib.eval_thms ctxt raw_facts
   in RULE'_i [] facts SK
  end
  | RULE' raw_rules raw_facts (ctxt, HHF (st, pctxt) :: SK) =
  let val facts = Attrib.eval_thms ctxt raw_facts
      val rules = maps (fn raw_rule =>
            let val name = name_of_ref (fst raw_rule)
             in map (fn rule0 =>
                  let open Phi_Sledgehammer_Solver
                      val rule = rule0 OF facts
                   in case infer_type_of_rule name rule0
                   of T_ELIM => (true, rule)
                    | T_DEST => (true, Tactic.make_elim rule)
                    | _      => (false, rule)
                  end
                ) (Attrib.eval_thms ctxt raw_rules)
            end ) raw_rules
   in st
   |> Thm.biresolution NONE false rules 1
   |> Seq.pull
   |> (fn SOME (st', _) => (ctxt, HHF (st', pctxt) :: SK)
        | NONE => raise OPR_FAIL "Fail to apply the rules" )
   |> maintain
  end
  | RULE' _ _ _ = raise BROKEN_INVARIANT

val RULE = OPR oo RULE'
val RULE_CMD = let open Parse
      in Scan.optional thms1 []
      -- Scan.optional (($$$ "with" || $$$ "WITH") |-- thms1) [] >> uncurry RULE
     end


(* HAVE *)

fun HAVE' _ _ (ctxt, []) = (ctxt, [])
  | HAVE' raw_name expr (ctxt, HHF (G,pctxt) :: S) =
      let val SOME (_, jj, _) = IPS_Data.get ctxt
          val name = Option.map (fn (name, raw_attrs) =>
                        (Binding.name name,
                         raw_attrs |> map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt ) ) ) raw_name
                  |> (fn SOME some => some
                       | NONE => let val b = Binding.name ("fact" ^ string_of_int (!jj))
                                     val _ = (jj := !jj + 1)
                                  in (b, [])
                                 end)
          val goal_term = Syntax.read_prop ctxt expr
          val goal = Goal.init (Thm.cterm_of ctxt goal_term)
          fun CB ctxt' (st',(*pctxt'*) _,S, _) =
            let val lems = Goal.conclude st'
                        |> singleton (Proof_Context.export ctxt' ctxt)
                        |> elim_conjs ctxt
                val ((name,lems), ctxt'') =
                        Proof_Context.note_thms "" (name, [(lems,[])]) ctxt
             in (ctxt'', HHF (G, cat_pctxt ([], [(name, map Thm.prop_of lems)]) pctxt) :: S)
            end
          fun PRT _ t = BUNDL (pctxt, [t, print_stack [HHF (G,([],[]))]])
       in (ctxt, HHF (goal, ([],[])) :: ENDBLK T_END :: MAGIC (CB, PRT, NO_PARAM) :: S)
      end
  | HAVE' _ _ _ = raise BROKEN_INVARIANT

val HAVE = OPR oo HAVE'

val HAVE_CMD =
        Scan.option (Parse.name -- Parse.opt_attribs --| \<^keyword>\<open>:\<close>) --
        Parse.term
     >> (fn (name, expr) => HAVE name expr)

(* OBTAIN *)

fun atomize_term ctxt =
      Object_Logic.atomize_term ctxt
  #> (fn X => if Term.fastype_of X = \<^Type>\<open>bool\<close>
              then X
              else raise OPR_FAIL "Fail to atomize the proposition into HOL")


(* can be cached *)
(*
fun mk_obtain_rule ctxt CN EN =
  let val TS = List.tabulate (EN, fn i =>
                  (i, TVar (("'x" ^ string_of_int i, 0), \<^sort>\<open>type\<close>)))
      fun var TS name = Var((name,0), (map #2 TS) ---> \<^Type>\<open>bool\<close>)
                     |> fold (fn (i,_) => fn X => X $ Bound (EN - 1 - i)) TS
      val C = HOLogic.mk_Trueprop (var [] "C")
      val PS = List.tabulate (CN, fn i => var TS ("P" ^ string_of_int i))
      fun import_vars ctxt th =
        let val ((_, [th']), ctxt') = ctxt |> Variable.set_body false |> Variable.import true [th];
         in (ctxt', th') end;

   in foldr1 (fn (A,B) => \<^Const>\<open>conj\<close> $ A $ B) PS
   |> fold_rev (fn (i,T) => fn X => \<^Const>\<open>Ex T\<close> $ Abs ("x" ^ string_of_int i, T, X)) TS
   |> (fn X => Logic.mk_implies (HOLogic.mk_Trueprop X, C))
   |> Thm.cterm_of ctxt
   |> Thm.trivial
   |> import_vars ctxt
   |-> (fn ctxt' => fn th => th
   |> Seq.REPEAT (Thm.biresolution NONE true [(true, @{thm exE}), (true, @{thm conjE})] 1)
   |> Seq.hd
   |> Thm.permute_prems 0 1
   |> singleton (Variable.export ctxt' ctxt))
  end
*)

(* can be cached *)
fun mk_consider_rule ctxt DNF_SPEC =
  let fun var TS name =
        let val EN = length TS
         in Var((name,0), (map #2 TS) ---> \<^Type>\<open>bool\<close>)
         |> fold (fn (i,_) => fn X => X $ Bound (EN - 1 - i)) TS
        end
      fun mk_conj_clause (ii, (EN,CN)) =
        let val TS = List.tabulate (EN, fn i =>
                      (i, TVar (("'x" ^ string_of_int ii ^ "'" ^ string_of_int i, 0), \<^sort>\<open>type\<close>)))
            val PS = List.tabulate (CN, fn i =>
                      var TS ("P"  ^ string_of_int ii ^ "'" ^ string_of_int i))
         in foldr1 (fn (A,B) => \<^Const>\<open>conj\<close> $ A $ B) PS
         |> fold_rev (fn (i,T) => fn X =>
                      \<^Const>\<open>Ex T\<close> $ Abs ("x" ^ string_of_int ii ^ "'" ^ string_of_int i, T, X)) TS
        end
      fun import_vars ctxt th =
        let val ((_, [th']), ctxt') = ctxt |> Variable.set_body false |> Variable.import true [th];
         in (ctxt', th')
        end
      val C = HOLogic.mk_Trueprop (var [] "C")
   in map_index mk_conj_clause DNF_SPEC
   |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
   |> (fn X => Logic.mk_implies (HOLogic.mk_Trueprop X, C))
   |> Thm.cterm_of ctxt
   |> Thm.trivial
   |> import_vars ctxt
   |-> (fn ctxt' => fn th => th
   |> Seq.REPEAT (REPEAT_DETERM_SOME (Thm.biresolution NONE true
              [(true, @{thm exE}), (true, @{thm conjE}), (true, @{thm disjE})]))
   |> Seq.hd
   |> Thm.permute_prems 0 ~1
   |> singleton (Variable.export ctxt' ctxt))
  end

(*
val elim_Ex = @{lemma \<open>Ex (\<lambda>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
                   by (unfold Ex_def, blast)}
val conjD1 = @{lemma \<open>conj A B \<Longrightarrow> A\<close> by (unfold conj_def, blast)}
val conjD2 = @{lemma \<open>conj A B \<Longrightarrow> B\<close> by (unfold conj_def, blast)}
*)

(*
local val prop_def = @{thm prop_def}
   in val protect_goal   = Conv.gconv_rule (Conv.rewr_conv (Thm.symmetric prop_def))
      val unprotect_goal = Conv.gconv_rule (Conv.rewr_conv prop_def)
end
*)

(* raw_decls raw_fixes raw_prems raw_statements *)

fun CONSIDER' raw_dnf (ctxt0, HHF (st0, pctxt0) :: S) =
  let val SOME (_, jj, _) = IPS_Data.get ctxt0
      fun parse (raw_decls, raw_fixes, raw_prems, raw_statements) ctxt =
        let val raw_props = map snd raw_statements
      
            val binders = map fst raw_statements
                       |> map (apsnd (map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt )))
      
            val (binders, nn) =
                  fold_map (fn (B,AT) => fn N =>
                      if Binding.is_empty B
                      then ((Binding.name ("fact" ^ string_of_int N), AT), N+1)
                      else ((B,AT),N)) binders (!jj)
            val _ = jj := nn
      
            val ({vars, propss, binds, result_binds, ...}, params_ctxt) =
                    Proof_Context.read_stmt (raw_decls @ raw_fixes) (raw_prems @ raw_props) ctxt
            val (decls, fixes) = chop (length raw_decls) vars ||> map #2;
            val (premss, conclss) = chop (length raw_prems) propss;
            val propss' = (map o map) (Logic.close_prop fixes (flat premss)) conclss
                       |> flat
                       |> map (atomize_term ctxt)
            val AS = map (Thm.cterm_of ctxt o HOLogic.mk_Trueprop) propss'
      
            val goal = propss'
                    |> foldr1 (fn (A, B) => \<^Const>\<open>conj\<close> $ A $ B)
                    |> fold_rev (fn (_, t) => fn T =>
                          \<^Const>\<open>Ex \<open>Term.type_of (snd t)\<close>\<close> $ Term.lambda_name t T
                        ) decls
      
            val cparams = map (Thm.cterm_of params_ctxt o #2 o #2) decls
         in ((cparams,
             (length decls, length propss'),
             (decls,
              fixes,
              AS,
              raw_props,
              binds,
              binders),
             (goal,
              result_binds)),
             params_ctxt)
        end
      val (conj_clauses, params_ctxt) = fold_map parse raw_dnf ctxt0
      val rule0 = mk_consider_rule ctxt0 (map #2 conj_clauses)

      val goal = map (#1 o #4) conj_clauses
              |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
              |> (fn X => HOLogic.Trueprop $ X)
              |> Thm.cterm_of params_ctxt
              |> Goal.init
              |> singleton (Variable.export params_ctxt ctxt0)
      val goal_binds = map (#2 o #4) conj_clauses
              |> foldl1 (AList.merge (op =) (op aconv))
      val ctxt_rule = params_ctxt
                   |> fold Variable.bind_term goal_binds

      val subgoals = map (fn (_, _, (decls, fixes, AS, raw_props, _, binders), _) =>
              print_stack [HHF (st0, (  map (apsnd Term.fastype_of o snd) decls
                                      @ map (apsnd Term.fastype_of) fixes,
                                     map (Binding.name_of o fst) binders ~~
                                        (unflat raw_props (map Thm.term_of AS)) ))] ) conj_clauses
      fun PRT0 sgs _ t = BUNDL (pctxt0, t :: sgs)
      fun CB _ _ [] _  _ = raise BROKEN_INVARIANT
        | CB initial sgs
             ((cparams, _, (decls, fixes, AS, raw_props, binds, binders), _) :: remain_clauses)
             ctxt' (lem, _, S, _) =
            let val rule' = lem
                         |> Goal.conclude
                         |> singleton (Proof_Context.export ctxt' ctxt0)
                         |> initial ? MP ctxt0 rule0
                fun export a b =
                    let val (A,B) = Obtain.obtain_export ctxt0 rule' cparams a b 
                        fun export_thm thm =
                          let val protected = is_protected (Thm.prop_of thm)
                           in thm
                           |> protected? Goal.conclude
                           |> A
                           |> protected? Goal.protect 0
                          end
                     in (export_thm,B)
                    end
                val (lems', ctxt'') = Proof_Context.add_fixes (map #1 decls) ctxt0
                                   |> snd
                                   |> fold (Variable.bind_term o apsnd (Logic.close_term fixes)) binds
                                   |> Assumption.add_assms export AS
                val lems'' = binders ~~ map (map (fn X => ([X],[]))) (unflat raw_props lems')
                val (new_facts, ctxt'3) = Proof_Context.note_thmss "" lems'' ctxt''
                val pctxt'3 = (map (apsnd Term.fastype_of o snd) decls,
                               map (apsnd (map Thm.prop_of)) new_facts)
                           |> null remain_clauses ? (fn X => cat_pctxt X pctxt0)
             in (ctxt'3, HHF (st0, pctxt'3)
                          :: (case remain_clauses
                                of [] => S
                                 |  _ =>    ENDBLK T_NXT
                                         :: MAGIC (CB false (tl sgs) remain_clauses,
                                                   PRT0 (tl sgs),
                                                   NO_PARAM)
                                         :: S))
            end

   in (ctxt_rule,
          HHF (goal,([],[]))
       :: ENDBLK (case conj_clauses of [_] => T_END | _ => T_NXT)
       :: MAGIC (CB true subgoals conj_clauses, PRT0 subgoals, NO_PARAM) :: S)
  end
  | CONSIDER' _ _ = raise BROKEN_INVARIANT

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));

val CONSIDER = OPR o CONSIDER'
fun CONSIDER_CMD toks = (
     Parse.enum1 "|"
        (Scan.optional (Parse.vars --| Parse.where_) []
          -- structured_statement
        >> (fn (vs,(a,b,c)) => (vs,a,b,c)))
     >> CONSIDER) toks

(* CONSIDER *)

(*
val elim_disj = @{lemma \<open>disj P Q \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> (Q \<Longrightarrow> C) \<Longrightarrow> C\<close>
                     by (unfold disj_def, blast)}


fun CONSIDER' raw_terms (ctxt, HHF (st,facts,IA) :: SK) =
  let val terms = Syntax.read_props ctxt raw_terms
               |> map (atomize_term ctxt)
      val goal  = foldr1 (fn (A, B) => \<^Const>\<open>HOL.disj\<close> $ A $ B ) terms
               |> HOLogic.mk_Trueprop
               |> Thm.cterm_of ctxt
               |> Goal.init

      val SOME (ii, _, _) = IPS_Data.get ctxt
      val binder = Binding.name (assm_name (!ii))
      val _ = ii := (!ii) + 1

      fun CB ctxt' (lem, facts', _, S) =
        let val lem = Goal.conclude lem
            val st' = Method.insert_tac ctxt' [lem] 1 st
                   |> Seq.hd
                   |> REPEAT_DETERM (eresolve_tac ctxt' [elim_Ex] 1)
                   |> Seq.hd
         in (ctxt', HHF (st', facts' @ facts, IA) :: S)
         |> INTRO'' (fn foc =>
            let val lem = case #prems foc
                            of [lem] => lem
                             | _ => error "5ViUXLLqRB+AA9ffsaEPDQ"
                fun split th =
                  case Thm.prop_of th
                    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
                        MP conjD1 th :: split (MP conjD2 th)
                     | _ => [th]
                val facts = binders ~~ map (map (fn X => ([X],[]))) (unflat raw_props (split lem))
             in #context foc
             |> Proof_Context.note_thmss "" facts
             |> apfst (map (apsnd (map Thm.prop_of)))
            end)
        end
      fun PRT t = BUNDL ([], [], [t, print_stack [HHF (st,facts,IA)]])
               |> augment_print (map (apsnd Term.fastype_of o snd) (#vars stmt),
                                 [])
   in (ctxt, HHF (goal, [], false) :: ENDBLK :: MAGIC (CB, PRT) :: SK)
  end

*)
(* HAMMER *)

fun HAMMER_i override step_id (ctxt, HHF (s,facts) :: S) =
  let val SOME (_, _, ID_BASE) = IPS_Data.get ctxt
      val ID = ID_BASE ^ "/" ^ step_id
      val s' = Phi_Sledgehammer_Solver.auto override (SOME ID) ctxt s
   in maintain (ctxt, HHF (s', facts) :: S)
  end
  | HAMMER_i _ _ _ = raise BROKEN_INVARIANT

fun HAMMER_all override step_id =
  let val ID_BASE = step_id ^ "/"
      fun loop j (stack as (_, HHF (s,_) :: _)) =
        if Thm.no_prems s then stack
        else HAMMER_i override (ID_BASE ^ string_of_int j) stack
          |> loop (j+1)
        | loop _ _ = raise BROKEN_INVARIANT
   in loop 0
  end

fun HAMMER override = OPR_ID (HAMMER_i override o string_of_int)
val HAMMER_CMD = orverride_parser >> HAMMER

(* END *)

fun END' param SH_override T jj ID (stack as (_, HHF _ :: _)) =
  let val ID_BASE = if jj = 0 then string_of_int ID 
                    else string_of_int ID ^ "+" ^ string_of_int jj
      val (ctxt, SK'1) = HAMMER_all SH_override ID_BASE stack
   in case SK'1
   of HHF s :: ENDBLK T' :: SK' =>
        if T = T_NXT andalso T' = T_NXT
        then (case SK'
          of MAGIC (CB, PRT, _) :: SK'' =>
              maintain (ctxt, HHF s :: MAGIC (CB, PRT, param) :: SK'')
           | _ => maintain (ctxt, HHF s :: SK') )
        else if T = T' then maintain (ctxt, HHF s :: SK')
        else if T = T_END andalso T' = T_NXT andalso Config.get ctxt END_completes_all_NEXT
        then maintain (ctxt, HHF s :: SK')
          |> END' param SH_override T_END (jj+1) ID
        else raise OPR_FAIL (
                "This block should be closed by the " ^
                (case T' of T_END => "END" | T_NXT => "NEXT" | T_CASE => "CASE") ^
                " command.")
    | _ => raise BROKEN_INVARIANT
  end
  | END' _ _ _ _ _ _ = raise BROKEN_INVARIANT

fun END SH_override = OPR_ID (END' NO_PARAM SH_override T_END 0)
fun NXT param SH_override = OPR_ID (END' (CASE_NAME param) SH_override T_NXT 0)
val END_CMD  = orverride_parser >> END
val NXT_CMD  = OPT_VARS -- orverride_parser >> uncurry NXT 

(* LET *)

local

fun gen_bind prep_terms raw_binds ctxt =
    let
      fun prep_bind (raw_pats, t) ctxt1 =
        let
          val T = Term.fastype_of t;
          val ctxt2 = Variable.declare_term t ctxt1;
          val pats = prep_terms (Proof_Context.set_mode Proof_Context.mode_pattern ctxt2) T raw_pats;
          val binds = Proof_Context.simult_matches ctxt2 (t, pats);
        in (binds, ctxt2) end;

      val ts = prep_terms ctxt dummyT (map snd raw_binds);
      val (binds, ctxt') = apfst flat (fold_map prep_bind (map fst raw_binds ~~ ts) ctxt);
      val binds' = map #1 binds ~~ Variable.exportT_terms ctxt' ctxt (map #2 binds);

      val ctxt'' =
        ctxt
        |> fold Variable.declare_term (map #2 binds')
        |> fold Proof_Context.bind_term binds';
      val _ = Variable.warn_extra_tfrees ctxt ctxt'';
    in ctxt'' end

fun read_terms ctxt T =
  map (Syntax.parse_term ctxt #> Type.constraint T) #> Syntax.check_terms ctxt;

in

fun LET' prep_terms raw_binds (ctxt, S) =
      (gen_bind prep_terms raw_binds ctxt, S)

val LET = OPR o LET' (fn ctxt => fn _ => map (Proof_Context.cert_term ctxt))
val LET_CMD =
  (Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
    >> (OPR o LET' read_terms))


end

(* CHOOSE -- Instantiate Existential Quantification *)

fun CHOOSE' prep_terms raw_terms (ctxt, HHF (st, pctxt) :: SK) =
  let val terms = prep_terms ctxt raw_terms
      val rules = map (fn X => @{thm exI}
                            |> Drule.infer_instantiate ctxt [(("x",0), Thm.cterm_of ctxt X)] ) terms
      val st' = fold (fn rule => fn st => rule RS st) rules st
   in (ctxt, HHF (st', pctxt) :: SK)
  end
  | CHOOSE' _ _ _ = raise BROKEN_INVARIANT

val CHOOSE = OPR o CHOOSE' (K I)
val CHOOSE_CMD = Scan.repeat1 Parse.term >> (OPR o CHOOSE' Syntax.read_terms)

(* PRINT *)

fun fixes_is_outdated ctxt var_name =
  Name.is_skolem var_name andalso Variable.revert_fixed ctxt var_name = var_name

fun contains_outdated_fixes ctxt term =
  let val vars = Term.add_free_names term []
   in exists (fixes_is_outdated ctxt) vars
  end

fun ap2_3 f (a,b,c) = (a, f b, c)

fun pretty_state ctxt tree =
  let open Pretty
      val atom_goals = Config.get ctxt atomize_goals
      val prt_typ = Syntax.pretty_typ ctxt
      val prt_term= Syntax.pretty_term ctxt o (atom_goals ? Object_Logic.atomize_term ctxt)
      fun prt_bundle (vars, facts, term) =
        let val prems = Logic.strip_imp_prems term
            val name = str o simp_name
            val tails =
                 (if null vars   then [] else [keyword1 "fixed variables"])
                @ map (fn (N,T) => item [str N, brk 1, str "::", brk 1, prt_typ  T]) vars
                @ (if null facts then [] else [keyword1 "contextual facts"])
                @ map (fn (N,[])  => item [name N, brk 1, str ":", brk 1, str "<empty>"]
                        | (N,[T]) => item [name N, brk 1, str ":", brk 1, prt_term T]
                        | (N,TS)  => item [name N, brk 1, str ":", brk 1, chunks (map prt_term TS)]
                      ) facts
         in case prems
         of [] => str "All goals are proven!"
          | [goal] => chunks ( block [keyword1 "goal: ", prt_term goal] :: tails)
          | _  => chunks (
              keyword1 "goals: " ::
              map (fn X => item [prt_term X]) prems
              @ tails)
        end
   in collect_context tree
   |> ap2_3 (map (apsnd (filter_out (contains_outdated_fixes ctxt)))
          #> filter_out (null o snd))
   |> prt_bundle
  end

fun PRINT (state as ((ctxt,SK), _, ID)) =
  let open Pretty
   in Pretty.writeln (chunks [
        block [keyword1 "proof state after step ", str (string_of_int ID)],
        pretty_state ctxt (print_stack SK)
      ])
    ; state
  end
val PRINT_CMD = Scan.succeed PRINT

(** Toplevel **)

(* Interfaces *)

val CMDS = Symtab.make [
      ("end",     END_CMD),
      ("next",    NXT_CMD),
      ("consider",CONSIDER_CMD),
      ("have",    HAVE_CMD),
      ("END",     END_CMD),
      ("NEXT",    NXT_CMD),
      ("CONSIDER",CONSIDER_CMD),
      ("HAVE",    HAVE_CMD),
      ("CASE_SPLIT", CASE_SPLIT_CMD),
      ("INDUCT",  INDUCT_CMD),
      ("CRUSH",   CRUSH_CMD),
      ("INTRO",   INTRO_CMD),
      ("ALL_INTRO",INTRO_ALL_CMD),
      ("HAMMER",  HAMMER_CMD),
      ("PRINT",   PRINT_CMD),
      ("RULE",    RULE_CMD),
      ("LET",     LET_CMD),
      ("let",     LET_CMD),
      ("APPLY",   APPLY_CMD),
      ("apply",   APPLY_CMD),
      ("UNFOLD",  UNFOLD_CMD),
      ("CHOOSE",  CHOOSE_CMD)
    ]

val keywords = let open Keyword
      in empty_keywords
      |> add_keywords
         [ (("where", \<^here>), quasi_command_spec),
           (("::",    \<^here>), quasi_command_spec),
           ((":",     \<^here>), quasi_command_spec),
           ((",",     \<^here>), quasi_command_spec),
           (("and",   \<^here>), quasi_command_spec),
           (("in",   \<^here>), quasi_command_spec),
           (("when",  \<^here>), quasi_command_spec),
           (("if",    \<^here>), quasi_command_spec),
           (("obtains",\<^here>),quasi_command_spec),
           (("shows", \<^here>), quasi_command_spec),
           (("fixes", \<^here>), quasi_command_spec),
           (("defines",\<^here>),quasi_command_spec),
           (("shows", \<^here>), quasi_command_spec),
           (("constrains",\<^here>),quasi_command_spec),
           (("assumes",\<^here>),quasi_command_spec),
           (("notes", \<^here>), quasi_command_spec),
           (("includes",\<^here>),quasi_command_spec),
           (("|",     \<^here>), quasi_command_spec),
           (("(",     \<^here>), quasi_command_spec),
           ((")",     \<^here>), quasi_command_spec),
           (("[",     \<^here>), quasi_command_spec),
           (("]",     \<^here>), quasi_command_spec),
           (("?",     \<^here>), quasi_command_spec),
           (("=",     \<^here>), quasi_command_spec),
           (("for",   \<^here>), quasi_command_spec),
           (("WITH",  \<^here>), quasi_command_spec),
           (("WITHOUT",\<^here>),quasi_command_spec),
           (("IN",    \<^here>), quasi_command_spec),
           (("VARS",  \<^here>), quasi_command_spec),

           (("END",   \<^here>), command_spec (thy_end, [])),
           (("end",   \<^here>), command_spec (thy_end, [])),
           (("NEXT",  \<^here>), command_spec (thy_end, [])),
           (("CONSIDER",\<^here>),command_spec (prf_asm_goal, [])),
           (("HAVE",  \<^here>), command_spec (prf_goal, [])),
           (("CASE_SPLIT",  \<^here>), command_spec (prf_goal, [])),
           (("INDUCT",\<^here>), command_spec (prf_goal, [])),
           (("CRUSH", \<^here>), command_spec (prf_goal, [])),
           (("INTRO", \<^here>), command_spec (prf_goal, [])),
           (("ALL_INTRO", \<^here>), command_spec (prf_goal, [])),
           (("HAMMER",\<^here>), command_spec (prf_goal, [])),
           (("PRINT", \<^here>), command_spec (prf_goal, [])),
           (("RULE",  \<^here>), command_spec (prf_goal, [])),
           (("LET",   \<^here>), command_spec (prf_goal, [])),
           (("APPLY", \<^here>), command_spec (prf_goal, [])),
           (("UNFOLD",\<^here>), command_spec (prf_goal, [])),
           (("CHOOSE",\<^here>), command_spec (prf_goal, []))
         ]
     end

fun parse_cmds source =
  let val pos = Position.make {
                  line=1, offset=1, end_offset=1,
                  props={label="", file="#MINSHELL SCRIPT", id="no_id"} }
      val src = Symbol_Pos.explode (source, pos)
      val toks = Token.tokenize keywords {strict = false} src

      fun split ret []  [] = ret
        | split ret buf [] = rev (Token.eof :: buf) :: ret
        | split ret buf (x::L) =
            if Token.is_command x
            then split (case buf of [] => ret
                           | _ => rev (Token.eof :: buf) :: ret) [x] L
            else if Token.is_ignored x
            then split ret buf L
            else split ret (x::buf) L

      val cmds = split [] [] toks
              |> map (fn (h::toks) =>
                    case Symtab.lookup CMDS (Token.content_of h)
                      of SOME parser => fst (parser toks)
                       | NONE => error ("Bad Command " ^ Token.content_of h) )
   in fold_rev I cmds
  end

fun PROVE tr ctxt st =
      INIT ctxt st
   |> OPR (apfst INIT_SYNTAX)
   |> OPR INIT_PROCESS
   |> tr
   |> (fn ((ctxt', S  as [HHF (st',_)]),_,_) =>
          let val st'' = singleton (Proof_Context.export ctxt' ctxt) st'
           in Pretty.writeln (pretty_state ctxt' (print_stack S));
              st''
          end
        | ((ctxt', S), _, _) =>
           (Pretty.writeln (pretty_state ctxt' (print_stack S));
            error "incomplete MINSHELL script") )

fun METHOD_i tr : Method.method = CONTEXT_METHOD (fn _ => fn (ctxt,st) =>
  if Thm.no_prems st
  then Seq.single (Seq.Result (ctxt, st))
  else Seq.make (fn () =>
        SOME (Seq.Result (ctxt, PROVE tr ctxt st), Seq.empty)))

val METHOD = METHOD_i o parse_cmds

val _ = Theory.setup (
  Method.setup \<^binding>\<open>min_script\<close> (
    Scan.peek (fn _ => Parse.embedded >> (fn src => fn _ =>
        METHOD src)))
  ""
)

end