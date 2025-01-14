theory MS_Test_Divisibility
  imports "HOL-Algebra.Divisibility" Proof_Shell
begin


theorem factorial_condition_two: (* Jacobson theorem 2.22 *)
  "divisor_chain_condition_monoid G \<and> gcd_condition_monoid G \<longleftrightarrow> factorial_monoid G"
apply (min_script \<open>
  RULE iffI
  CRUSH
  USE_THY divisor_chain_condition_monoid "G" END
  USE_THY gcd_condition_monoid "G" END
  NEXT
\<close>)
proof (rule iffI, clarify)
  assume dcc: "divisor_chain_condition_monoid G"
    and gc: "gcd_condition_monoid G"
  interpret divisor_chain_condition_monoid "G" by (rule dcc)
  interpret gcd_condition_monoid "G" by (rule gc)
  show "factorial_monoid G"
    by (simp add: factorial_condition_one[symmetric], rule, unfold_locales)
next
  assume "factorial_monoid G"
  then interpret factorial_monoid "G" .
  show "divisor_chain_condition_monoid G \<and> gcd_condition_monoid G"
    by rule unfold_locales
qed














lemma (in factorial_monoid) properfactor_fmset_ne:
  assumes pf: "properfactor G a b"
    and "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "fmset G as \<noteq> fmset G bs"
  using properfactorE [OF pf] assms divides_as_fmsubset by force

subsection \<open>Irreducible Elements are Prime\<close>

lemma (in factorial_monoid) irreducible_prime:
  assumes pirr: "irreducible G p" and pcarr: "p \<in> carrier G"
  shows "prime G p"
  thm irreducibleE
  
  apply (min_script \<open>
  APPLY (insert pirr)
  RULE irreducibleE
  RULE primeI
  HAMMER
  CONSIDER c where ccarr: "c \<in> carrier G" and abpc: "a \<otimes> b = p \<otimes> c" END
\<close>)



  using pirr
proof (elim irreducibleE, intro primeI)
  fix a b
  assume acarr: "a \<in> carrier G"  and bcarr: "b \<in> carrier G"
    and pdvdab: "p divides (a \<otimes> b)"
    and pnunit: "p \<notin> Units G"
  assume irreduc[rule_format]:
    "\<forall>b. b \<in> carrier G \<and> properfactor G b p \<longrightarrow> b \<in> Units G"
  from pdvdab obtain c where ccarr: "c \<in> carrier G" and abpc: "a \<otimes> b = p \<otimes> c"
    by (rule dividesE)
  obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    using wfactors_exist [OF acarr] by blast
  obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfs: "wfactors G bs b"
    using wfactors_exist [OF bcarr] by blast
  obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfs: "wfactors G cs c"
    using wfactors_exist [OF ccarr] by blast
  note carr[simp] = pcarr acarr bcarr ccarr ascarr bscarr cscarr
  from pirr cfs  abpc have "wfactors G (p # cs) (a \<otimes> b)"
    by (simp add: wfactors_mult_single)
  moreover have  "wfactors G (as @ bs) (a \<otimes> b)"
    by (rule wfactors_mult [OF afs bfs]) fact+
  ultimately have "essentially_equal G (p # cs) (as @ bs)"
    by (rule wfactors_unique) simp+
  then obtain ds where "p # cs <~~> ds" and dsassoc: "ds [\<sim>] (as @ bs)"
    by (fast elim: essentially_equalE)
  then have "p \<in> set ds"
    by (metis \<open>mset (p # cs) = mset ds\<close> insert_iff list.set(2) perm_set_eq) 
  with dsassoc obtain p' where "p' \<in> set (as@bs)" and pp': "p \<sim> p'"
    unfolding list_all2_conv_all_nth set_conv_nth by force
  then consider "p' \<in> set as" | "p' \<in> set bs" by auto
  then show "p divides a \<or> p divides b"
    using afs bfs divides_cong_l pp' wfactors_dividesI
    by (meson acarr ascarr bcarr bscarr pcarr)
qed


end