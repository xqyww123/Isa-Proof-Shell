theory MS_Test_Word
  imports Proof_Shell "HOL-Library.Type_Length"
begin

subsection \<open>Preliminaries\<close>

lemma signed_take_bit_decr_length_iff:
  \<open>signed_take_bit (LENGTH('a::len) - Suc 0) k = signed_take_bit (LENGTH('a) - Suc 0) l
    \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by (min_script \<open> CASE_SPLIT "LENGTH('a)" END \<close>)

subsection \<open>Fundamentals\<close>

subsubsection \<open>Type definition\<close>

quotient_type (overloaded) 'a word = int / \<open>\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a::len) l\<close>
  morphisms rep Word by (auto intro!: equivpI reflpI sympI transpI)

hide_const (open) rep \<comment> \<open>only for foundational purpose\<close>
hide_const (open) Word \<comment> \<open>only for code generation\<close>


subsubsection \<open>Basic arithmetic\<close>

instantiation word :: (len) comm_ring_1
begin

lift_definition zero_word :: \<open>'a word\<close>
  is 0 .

lift_definition one_word :: \<open>'a word\<close>
  is 1 .

lift_definition plus_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>(+)\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_add_cong)

lift_definition minus_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>(-)\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_diff_cong)

lift_definition uminus_word :: \<open>'a word \<Rightarrow> 'a word\<close>
  is uminus
  by (auto simp add: take_bit_eq_mod intro: mod_minus_cong)

lift_definition times_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>(*)\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_mult_cong)

instance
  by (standard; transfer) (simp_all add: algebra_simps)

end

context
  includes lifting_syntax
  notes
    power_transfer [transfer_rule]
    transfer_rule_of_bool [transfer_rule]
    transfer_rule_numeral [transfer_rule]
    transfer_rule_of_nat [transfer_rule]
    transfer_rule_of_int [transfer_rule]
begin

lemma power_transfer_word [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (^) (^)\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) of_bool of_bool\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) numeral numeral\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) int of_nat\<close>
  by transfer_prover

lemma [transfer_rule]:
  \<open>((=) ===> pcr_word) (\<lambda>k. k) of_int\<close>
proof -
  have \<open>((=) ===> pcr_word) of_int of_int\<close>
    by transfer_prover
  then show ?thesis by (simp add: id_def)
qed

lemma [transfer_rule]:
  \<open>(pcr_word ===> (\<longleftrightarrow>)) even ((dvd) 2 :: 'a::len word \<Rightarrow> bool)\<close>

by (min_script \<open>
  HAVE even_word_unfold: "\<forall>k. even k \<longleftrightarrow> (\<exists>l. take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l))" END
  UNFOLD even_word_unfold [THEN spec, abs_def] dvd_def [where ?'a = "'a word", abs_def]
  APPLY transfer_prover
  END
\<close>)

proof -
  have even_word_unfold: "even k \<longleftrightarrow> (\<exists>l. take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l))" (is "?P \<longleftrightarrow> ?Q")
    for k :: int
  proof
    assume ?P
    then show ?Q
      by auto
  next
    assume ?Q
    then obtain l where "take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l)" ..
    then have "even (take_bit LENGTH('a) k)"
      by simp
    then show ?P
      by simp
  qed
  show ?thesis by (simp only: even_word_unfold [abs_def] dvd_def [where ?'a = "'a word", abs_def])
    transfer_prover
qed

end

lemma exp_eq_zero_iff [simp]:
  \<open>2 ^ n = (0 :: 'a::len word) \<longleftrightarrow> n \<ge> LENGTH('a)\<close>
  by transfer auto

lemma word_exp_length_eq_0 [simp]:
  \<open>(2 :: 'a::len word) ^ LENGTH('a) = 0\<close>
  by simp



end