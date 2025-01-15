theory MS_Translator
  imports Proof_Shell
begin

ML_file \<open>library/translator.ML\<close>


supply
ML \<open>Token.make_string0 "\"aaa\""\<close>
ML \<open>Token.make ((2,0), "a") Position.none\<close>

ML \<open>let
 val kws = Thy_Header.get_keywords \<^theory>
  in Parse.read_embedded \<^context> kws
        Method.parse (Input.string "this")
 end\<close>

ML \<open>
fun trim_makrup msg =
  let fun auto _ [] = []
        | auto acc (#"\005" :: L) = auto (not acc) L
        | auto true (#"\127" :: L) = auto true L
        | auto true (x :: L) = x :: auto true L
        | auto false (_ :: L) = auto false L
   in String.implode (auto true (String.explode msg))
  end
\<close>

consts CCC :: nat
syntax AAA :: logic ("BBB")
translations
  "BBB" <= "CONST CCC"


thm conjI
ML \<open>
Drule.implies_intr_protected
  [\<^cprop>\<open>A::bool\<close>] @{thm conjI}
\<close>

ML \<open>String.size\<close>
term CCC
ML \<open>Syntax.parse_term \<^context> "CCC"
  |> Syntax.unparse_term \<^context>
\<close>
ML \<open> singleton (Syntax.uncheck_terms \<^context>) \<^term>\<open>CCC\<close>
  |> Syntax.unparse_term \<^context>
  |> Pretty.string_of
  |> trim_makrup
  |> Syntax.read_term \<^context>\<close>

term "\<forall>a b. P a \<longrightarrow> Q b"

  case
  unfolding
  assume
  by
  obtain

end