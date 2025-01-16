theory Translation_Test
  imports Main MS_Translator HOL.Transcendental HOL.Groups_Big
begin

declare [[ML_debugger, ML_exception_debugger, ML_exception_trace]]

lemma "n choose k \<le> n choose (n div 2)"

  ML_val \<open>@{Isar.goal}\<close>
     
ML_val \<open>ML_Translator.translate' @{Isar.state}
"proof -\n\
    \have \"k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n\" by linarith\n\
    \consider \"2*k \<le> n\" | \"2*k \<ge> n\" \"k \<le> n\" | \"k > n\" by linarith\n\
    \thus ?thesis\n\
    \proof cases\n\
      \case 1\n\
      \thus ?thesis by (intro binomial_mono) linarith+\n\
    \next\n\
      \case 2\n\
      \thus ?thesis by (intro binomial_antimono) simp_all\n\
    \qed (simp_all add: binomial_eq_0)\n\
  \qed"
\<close>


end