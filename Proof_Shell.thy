text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[ML_debugger, ML_exception_trace]]

definition \<open>TAG X \<equiv> X\<close>

ML_file \<open>./library/proof.ML\<close>

notepad
begin

  let ?x = \<open>1::nat\<close>
  let ?y = \<open>?x\<close>

end

supply
interpret
print_facts
  write
  define

lemma
  \<open>False\<close>
  ML_val \<open>
let val ((a,b),c) = Parse.read_embedded \<^context>
                (Thy_Header.get_keywords \<^theory>)
                ((Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes)
                (Input.string "a where \<open>a = (1::nat)\<close>")
    val s = Proof.init \<^context>
    val s' = Proof.define_cmd a c b s
    val ctxt' = Proof.context_of s'
 in Proof_Context.get_thms ctxt' "a_def"
end
\<close>


end