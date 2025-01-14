text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[ML_debugger, ML_exception_trace]]

definition \<open>TAG X \<equiv> X\<close>

ML_file \<open>./library/proof.ML\<close>

interpret
print_facts
write

end