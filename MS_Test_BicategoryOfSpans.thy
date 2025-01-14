(*  Title:       BicategoryOfSpans
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Bicategories of Spans"

theory MS_Test_BicategoryOfSpans
imports Category3.ConcreteCategory Bicategory.IsomorphismClass
        Bicategory.CanonicalIsos Bicategory.EquivalenceOfBicategories
        Bicategory.SpanBicategory Bicategory.Tabulation
        Proof_Shell
begin

text \<open>
  In this section, we prove CKS Theorem 4, which characterizes up to equivalence the
  bicategories of spans in a category with pullbacks.
  The characterization consists of three conditions:
  BS1: ``Every 1-cell is isomorphic to a composition \<open>g \<star> f\<^sup>*\<close>, where f and g are maps'';
  BS2: ``For every span of maps \<open>(f, g)\<close> there is a 2-cell \<open>\<rho>\<close> such that \<open>(f, \<rho>, g)\<close>
  is a tabulation''; and
  BS3: ``Any two 2-cells between the same pair of maps are equal and invertible.''
  One direction of the proof, which is the easier direction once it is established that
  BS1 and BS3 are respected by equivalence of bicategories, shows that if a bicategory \<open>B\<close>
  is biequivalent to the bicategory of spans in some category \<open>C\<close> with pullbacks,
  then it satisfies BS1 -- BS3.
  The other direction, which is harder, shows that a bicategory \<open>B\<close> satisfying BS1 -- BS3 is
  biequivalent to the bicategory of spans in a certain category with pullbacks that
  is constructed from the sub-bicategory of maps of \<open>B\<close>.
\<close>

  subsection "Definition"

  text \<open>
    We define a \emph{bicategory of spans} to be a bicategory that satisfies the conditions
    \<open>BS1\<close> -- \<open>BS3\<close> stated informally above.
  \<close>

  locale bicategory_of_spans =
    bicategory + chosen_right_adjoints +
  assumes BS1: "ide r \<Longrightarrow> \<exists>f g. is_left_adjoint f \<and> is_left_adjoint g \<and> isomorphic r (g \<star> f\<^sup>*)"
  and BS2: "\<lbrakk> is_left_adjoint f; is_left_adjoint g; src f = src g \<rbrakk>
                      \<Longrightarrow> \<exists>r \<rho>. tabulation V H \<a> \<i> src trg r \<rho> f g"
  and BS3: "\<lbrakk> is_left_adjoint f; is_left_adjoint f'; \<guillemotleft>\<mu> : f \<Rightarrow> f'\<guillemotright>; \<guillemotleft>\<mu>' : f \<Rightarrow> f'\<guillemotright> \<rbrakk>
                             \<Longrightarrow> iso \<mu> \<and> iso \<mu>' \<and> \<mu> = \<mu>'"

  text \<open>
    Using the already-established fact \<open>equivalence_pseudofunctor.reflects_tabulation\<close>
    that tabulations are reflected by equivalence pseudofunctors, it is not difficult to prove
    that the notion `bicategory of spans' respects equivalence of bicategories.
  \<close>
   
  lemma bicategory_of_spans_respects_equivalence:
    assumes "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
    and "bicategory_of_spans V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
    shows "bicategory_of_spans V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
    
by (min_script \<open>
  LOAD_MODULE C: bicategory_of_spans V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C END
  LOAD_MODULE D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             END WITH equivalent_bicategories_def equivalence_pseudofunctor.axioms(1)
                      pseudofunctor.axioms(2)
  LOAD_MODULE D: chosen_right_adjoints V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D END
  CONSIDER F \<Phi> where F: "equivalence_pseudofunctor
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>" END WITH equivalent_bicategories_def
  LOAD_MODULE F: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi> END
  LOAD_MODULE E: equivalence_of_bicategories
                   V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C  (* 17 sec *)
                F \<Phi> F.right_map F.right_cmp F.unit\<^sub>0 F.unit\<^sub>1 F.counit\<^sub>0 F.counit\<^sub>1 END
  LOAD_MODULE E': converse_equivalence_of_bicategories
                    V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                    F \<Phi> F.right_map F.right_cmp F.unit\<^sub>0 F.unit\<^sub>1 F.counit\<^sub>0 F.counit\<^sub>1 END
  LOAD_MODULE G: equivalence_pseudofunctor
                   V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                   F.right_map F.right_cmp END
  NOTATION V\<^sub>C          (infixr "\<cdot>\<^sub>C" 55)
       and V\<^sub>D          (infixr "\<cdot>\<^sub>D" 55)
       and H\<^sub>C          (infixr "\<star>\<^sub>C" 53)
       and H\<^sub>D          (infixr "\<star>\<^sub>D" 53)
  NOTATION \<a>\<^sub>C          ("\<a>\<^sub>C[_, _, _]")
  NOTATION \<a>\<^sub>D          ("\<a>\<^sub>D[_, _, _]")
  NOTATION C.in_hhom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
  NOTATION C.in_hom    ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>C _\<guillemotright>")
  NOTATION D.in_hhom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")
  NOTATION D.in_hom    ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>D _\<guillemotright>")
  NOTATION C.isomorphic (infix "\<cong>\<^sub>C" 50)
  NOTATION D.isomorphic (infix "\<cong>\<^sub>D" 50)
  NOTATION C.some_right_adjoint ("_\<^sup>*\<^sup>C" [1000] 1000)
  NOTATION D.some_right_adjoint ("_\<^sup>*\<^sup>D" [1000] 1000)

  CRUSH VARS r'
    CONSIDER f g where fg: "C.is_left_adjoint f \<and> C.is_left_adjoint g \<and> F.right_map r' \<cong>\<^sub>C g \<star>\<^sub>C f\<^sup>*\<^sup>C" END
    HAVE trg_g: "trg\<^sub>C g = E.G.map\<^sub>0 (trg\<^sub>D r')" END WITH fg C.isomorphic_implies_ide C.isomorphic_implies_hpar
    HAVE trg_f: "trg\<^sub>C f = E.G.map\<^sub>0 (src\<^sub>D r')" END WITH fg C.isomorphic_implies_ide C.isomorphic_implies_hpar
    DEFINE d_src where "d_src \<equiv> F.counit\<^sub>0 (src\<^sub>D r')"
    DEFINE e_src where "e_src \<equiv> (F.counit\<^sub>0 (src\<^sub>D r'))\<^sup>~\<^sup>D"
    HAVE "\<guillemotleft>d_src : F.map\<^sub>0 (E.G.map\<^sub>0 (src\<^sub>D r')) \<rightarrow>\<^sub>D src\<^sub>D r'\<guillemotright> \<and>
                     D.equivalence_map d_src"
        END
    HAVE e_src: "\<guillemotleft>e_src : src\<^sub>D r' \<rightarrow>\<^sub>D F.map\<^sub>0 (E.G.map\<^sub>0 (src\<^sub>D r'))\<guillemotright> \<and>
                     D.equivalence_map e_src" END
    CONSIDER \<eta>_src \<epsilon>_src
        where eq_src: "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_src e_src \<eta>_src \<epsilon>_src" END
    LOAD_MODULE eq_src: equivalence_in_bicategory
                            V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_src e_src \<eta>_src \<epsilon>_src END
    DEFINE d_trg where "d_trg \<equiv> F.counit\<^sub>0 (trg\<^sub>D r')"
    DEFINE e_trg where "e_trg \<equiv> (F.counit\<^sub>0 (trg\<^sub>D r'))\<^sup>~\<^sup>D"
    HAVE d_trg: "\<guillemotleft>d_trg : F.map\<^sub>0 (E.G.map\<^sub>0 (trg\<^sub>D r')) \<rightarrow>\<^sub>D trg\<^sub>D r'\<guillemotright> \<and>
                     D.equivalence_map d_trg" END
    HAVE e_trg: "\<guillemotleft>e_trg : trg\<^sub>D r' \<rightarrow>\<^sub>D F.map\<^sub>0 (E.G.map\<^sub>0 (trg\<^sub>D r'))\<guillemotright> \<and>
                     D.equivalence_map e_trg" END
    CONSIDER \<eta>_trg \<epsilon>_trg
        where eq_trg: "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_trg e_trg \<eta>_trg \<epsilon>_trg" END
    LOAD_MODULE eq_trg: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_trg e_trg \<eta>_trg \<epsilon>_trg END
    LOAD_MODULE eqs: two_equivalences_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            d_src e_src \<eta>_src \<epsilon>_src d_trg e_trg \<eta>_trg \<epsilon>_trg END
    LOAD_MODULE hom: subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : trg\<^sub>D d_src \<rightarrow>\<^sub>D trg\<^sub>D d_trg\<guillemotright>\<close> END
    LOAD_MODULE hom': subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : src\<^sub>D d_src \<rightarrow>\<^sub>D src\<^sub>D d_trg\<guillemotright>\<close> END
    LOAD_MODULE e: equivalence_of_categories hom.comp hom'.comp eqs.F eqs.G eqs.\<phi> eqs.\<psi> END
    HAVE r'_in_hhom: "D.in_hhom r' (src\<^sub>D e_src) (src\<^sub>D e_trg)" END
    DEFINE g' where "g' = d_trg \<star>\<^sub>D F g"
    HAVE g': "D.is_left_adjoint g'" UNFOLD g'_def END WITH fg d_trg trg_g C.left_adjoint_is_ide D.equivalence_is_adjoint
                D.left_adjoints_compose F.preserves_left_adjoint C.ideD(1) D.in_hhom_def
                F.preserves_trg
    HAVE 1: "D.is_right_adjoint (F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src)"
          HAVE "D.is_right_adjoint e_src" END
          HAVE "D.is_right_adjoint (F f\<^sup>*\<^sup>C)" END
          HAVE "src\<^sub>D (F f\<^sup>*\<^sup>C) = trg\<^sub>D e_src" END
        END
    CONSIDER f' where f': "D.adjoint_pair f' (F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src)" END
    HAVE f': "D.is_left_adjoint f' \<and> F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src \<cong>\<^sub>D (f')\<^sup>*\<^sup>D" END
    HAVE "r' \<cong>\<^sub>D d_trg \<star>\<^sub>D (e_trg \<star>\<^sub>D r' \<star>\<^sub>D d_src) \<star>\<^sub>D e_src" END WITH r'_in_hhom D.isomorphic_def eqs.\<psi>_in_hom eqs.\<psi>_components_are_iso
                D.isomorphic_symmetric D.ide_char eq_src.antipar(2) eq_trg.antipar(2)
    HAVE 1: "d_trg \<star>\<^sub>D (e_trg \<star>\<^sub>D r' \<star>\<^sub>D d_src) \<star>\<^sub>D e_src \<cong>\<^sub>D d_trg \<star>\<^sub>D F (F.right_map r') \<star>\<^sub>D e_src"
      HAVE "e_trg \<star>\<^sub>D r' \<star>\<^sub>D d_src \<cong>\<^sub>D F (F.right_map r')"
        HAVE "D.in_hom (F.counit\<^sub>1 r')
                        (r' \<star>\<^sub>D d_src) (F.counit\<^sub>0 (trg\<^sub>D r') \<star>\<^sub>D F (F.right_map r'))"
          UNFOLD d_src_def END WITH E.\<epsilon>.map\<^sub>1_in_hom(2) [of r']
        HAVE "r' \<star>\<^sub>D d_src \<cong>\<^sub>D F.counit\<^sub>0 (trg\<^sub>D r') \<star>\<^sub>D F (F.right_map r')"
          END WITH D.isomorphic_def E.\<epsilon>.iso_map\<^sub>1_ide
      END
    END
    HAVE 2: "d_trg \<star>\<^sub>D F (F.right_map r') \<star>\<^sub>D e_src \<cong>\<^sub>D d_trg \<star>\<^sub>D (F g \<star>\<^sub>D F f\<^sup>*\<^sup>C) \<star>\<^sub>D e_src"
      HAVE "F (F.right_map r') \<cong>\<^sub>D F g \<star>\<^sub>D F f\<^sup>*\<^sup>C"
        END WITH C.hseq_char C.ideD(1) C.isomorphic_implies_ide(2) C.left_adjoint_is_ide
                C.right_adjoint_simps(1) D.isomorphic_symmetric D.isomorphic_transitive
                F.preserves_isomorphic F.weakly_preserves_hcomp fg
    END
    HAVE 3: "d_trg \<star>\<^sub>D (F g \<star>\<^sub>D F f\<^sup>*\<^sup>C) \<star>\<^sub>D e_src \<cong>\<^sub>D (d_trg \<star>\<^sub>D F g) \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src"
      HAVE "d_trg \<star>\<^sub>D (F g \<star>\<^sub>D F f\<^sup>*\<^sup>C) \<star>\<^sub>D e_src \<cong>\<^sub>D d_trg \<star>\<^sub>D F g \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src" END 
      HAVE "d_trg \<star>\<^sub>D F g \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src \<cong>\<^sub>D (d_trg \<star>\<^sub>D F g) \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src" END
    END
    HAVE "(d_trg \<star>\<^sub>D F g) \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src \<cong>\<^sub>D g' \<star>\<^sub>D f'\<^sup>*\<^sup>D" END
    HAVE "D.isomorphic r' (g' \<star>\<^sub>D f'\<^sup>*\<^sup>D)" END
  NEXT
    HAVE "C.is_left_adjoint (F.right_map f)" END
    HAVE "C.is_left_adjoint (F.right_map g)" END
    HAVE "src\<^sub>C (F.right_map f) = src\<^sub>C (F.right_map g)" END
    HAVE 1: "\<exists>r \<rho>. tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> (F.right_map f) (F.right_map g)" END
    CONSIDER r \<rho> where
            \<rho>: "tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> (F.right_map f) (F.right_map g)" END
    LOAD_MODULE \<rho>: tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> \<open>F.right_map f\<close> \<open>F.right_map g\<close> END
    CONSIDER r' where
          r': "D.ide r' \<and> D.in_hhom r' (trg\<^sub>D f) (trg\<^sub>D g) \<and> C.isomorphic (F.right_map r') r" END
    CONSIDER \<phi> where \<phi>: "\<guillemotleft>\<phi> : r \<Rightarrow>\<^sub>C F.right_map r'\<guillemotright> \<and> C.iso \<phi>" END
    HAVE \<sigma>: "tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
               (F.right_map r') ((\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>) (F.right_map f) (F.right_map g)" END
    HAVE 1: "\<exists>\<rho>'. \<guillemotleft>\<rho>' : g \<Rightarrow>\<^sub>D H\<^sub>D r' f\<guillemotright> \<and>
                  F.right_map \<rho>' = F.right_cmp (r', f) \<cdot>\<^sub>C (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>"
      HAVE "D.ide g" END
      HAVE "D.ide (H\<^sub>D r' f)" END
      HAVE "src\<^sub>D g = src\<^sub>D (H\<^sub>D r' f)" END
      HAVE "trg\<^sub>D g = trg\<^sub>D (H\<^sub>D r' f)" END
      HAVE "\<guillemotleft>F.right_cmp (r', f) \<cdot>\<^sub>C (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho> :
                        F.right_map g \<Rightarrow>\<^sub>C F.right_map (r' \<star>\<^sub>D f)\<guillemotright>" END
    END
    CONSIDER \<rho>' where \<rho>': "\<guillemotleft>\<rho>' : g \<Rightarrow>\<^sub>D H\<^sub>D r' f\<guillemotright> \<and>
                             F.right_map \<rho>' = F.right_cmp (r', f) \<cdot>\<^sub>C (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>" END
    HAVE "tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D r' \<rho>' f g"
      HAVE "C.inv (F.right_cmp (r', f)) \<cdot>\<^sub>C F.right_map \<rho>' = (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>" END
    END
  NEXT VARS f f' \<mu> \<mu>'
    HAVE "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')" END
    HAVE "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')" END
    HAVE "C.iso (F.right_map \<mu>) \<and> C.iso (F.right_map \<mu>') \<and> F.right_map \<mu> = F.right_map \<mu>'" END
  NEXT VARS f f' \<mu> \<mu>'
    HAVE "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')" END
    HAVE "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')" END
    HAVE "C.iso (F.right_map \<mu>) \<and> C.iso (F.right_map \<mu>') \<and> F.right_map \<mu> = F.right_map \<mu>'" END
  NEXT VARS f f' \<mu> \<mu>'
    HAVE "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')" END
    HAVE "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')" END
    HAVE "C.iso (F.right_map \<mu>) \<and> C.iso (F.right_map \<mu>') \<and> F.right_map \<mu> = F.right_map \<mu>'" END
  END
\<close>)


lemma bicategory_of_spans_respects_equivalence__origin:
    assumes "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
    and "bicategory_of_spans V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
    shows "bicategory_of_spans V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  proof -
    interpret C: bicategory_of_spans V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
      using assms by simp
    interpret C: chosen_right_adjoints V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C ..
    interpret D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
      using assms equivalent_bicategories_def equivalence_pseudofunctor.axioms(1)
            pseudofunctor.axioms(2)
      by fast
    interpret D: chosen_right_adjoints V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..
    obtain F \<Phi> where F: "equivalence_pseudofunctor
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>"
      using assms equivalent_bicategories_def by blast
    interpret F: equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>
      using F by simp
    interpret E: equivalence_of_bicategories
                   V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C  (* 17 sec *)
                F \<Phi> F.right_map F.right_cmp F.unit\<^sub>0 F.unit\<^sub>1 F.counit\<^sub>0 F.counit\<^sub>1
      using F.extends_to_equivalence_of_bicategories by simp
    interpret E': converse_equivalence_of_bicategories
                    V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                    F \<Phi> F.right_map F.right_cmp F.unit\<^sub>0 F.unit\<^sub>1 F.counit\<^sub>0 F.counit\<^sub>1
      ..
    interpret G: equivalence_pseudofunctor
                   V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                   F.right_map F.right_cmp
      using E'.equivalence_pseudofunctor_left by simp

    write V\<^sub>C          (infixr "\<cdot>\<^sub>C" 55)
    write V\<^sub>D          (infixr "\<cdot>\<^sub>D" 55)
    write H\<^sub>C          (infixr "\<star>\<^sub>C" 53)
    write H\<^sub>D          (infixr "\<star>\<^sub>D" 53)
    write \<a>\<^sub>C          ("\<a>\<^sub>C[_, _, _]")
    write \<a>\<^sub>D          ("\<a>\<^sub>D[_, _, _]")
    write C.in_hhom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    write C.in_hom    ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>C _\<guillemotright>")
    write D.in_hhom   ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")
    write D.in_hom    ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>D _\<guillemotright>")
    write C.isomorphic (infix "\<cong>\<^sub>C" 50)
    write D.isomorphic (infix "\<cong>\<^sub>D" 50)
    write C.some_right_adjoint ("_\<^sup>*\<^sup>C" [1000] 1000)
    write D.some_right_adjoint ("_\<^sup>*\<^sup>D" [1000] 1000)

    show "bicategory_of_spans V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
    proof
      show "\<And>r'. D.ide r' \<Longrightarrow>
                 \<exists>f' g'. D.is_left_adjoint f' \<and> D.is_left_adjoint g' \<and> r' \<cong>\<^sub>D g' \<star>\<^sub>D (f')\<^sup>*\<^sup>D"
      proof -
        fix r'
        assume r': "D.ide r'"
        obtain f g
          where fg: "C.is_left_adjoint f \<and> C.is_left_adjoint g \<and> F.right_map r' \<cong>\<^sub>C g \<star>\<^sub>C f\<^sup>*\<^sup>C"
          using r' C.BS1 [of "F.right_map r'"] by auto
        have trg_g: "trg\<^sub>C g = E.G.map\<^sub>0 (trg\<^sub>D r')"
          using fg r' C.isomorphic_implies_ide C.isomorphic_implies_hpar
          by (metis C.ideD(1) C.trg_hcomp D.ideD(1) E.G.preserves_trg)
        have trg_f: "trg\<^sub>C f = E.G.map\<^sub>0 (src\<^sub>D r')"
          using fg r' C.isomorphic_implies_ide C.isomorphic_implies_hpar
          by (metis C.ideD(1) C.right_adjoint_simps(2) C.src_hcomp D.ideD(1) E.G.preserves_src)

        define d_src where "d_src \<equiv> F.counit\<^sub>0 (src\<^sub>D r')"
        define e_src where "e_src \<equiv> (F.counit\<^sub>0 (src\<^sub>D r'))\<^sup>~\<^sup>D"
        have d_src: "\<guillemotleft>d_src : F.map\<^sub>0 (E.G.map\<^sub>0 (src\<^sub>D r')) \<rightarrow>\<^sub>D src\<^sub>D r'\<guillemotright> \<and>
                     D.equivalence_map d_src"
          using d_src_def r' E.\<epsilon>.map\<^sub>0_in_hhom E.\<epsilon>.components_are_equivalences by simp
        have e_src: "\<guillemotleft>e_src : src\<^sub>D r' \<rightarrow>\<^sub>D F.map\<^sub>0 (E.G.map\<^sub>0 (src\<^sub>D r'))\<guillemotright> \<and>
                     D.equivalence_map e_src"
          using e_src_def r' E.\<epsilon>.map\<^sub>0_in_hhom E.\<epsilon>.components_are_equivalences by simp
        obtain \<eta>_src \<epsilon>_src
        where eq_src: "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_src e_src \<eta>_src \<epsilon>_src"
          using d_src_def e_src_def d_src e_src D.quasi_inverses_some_quasi_inverse
                D.quasi_inverses_def
          by blast
        interpret eq_src: equivalence_in_bicategory
                            V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_src e_src \<eta>_src \<epsilon>_src
          using eq_src by simp

        define d_trg where "d_trg \<equiv> F.counit\<^sub>0 (trg\<^sub>D r')"
        define e_trg where "e_trg \<equiv> (F.counit\<^sub>0 (trg\<^sub>D r'))\<^sup>~\<^sup>D"
        have d_trg: "\<guillemotleft>d_trg : F.map\<^sub>0 (E.G.map\<^sub>0 (trg\<^sub>D r')) \<rightarrow>\<^sub>D trg\<^sub>D r'\<guillemotright> \<and>
                     D.equivalence_map d_trg"
          using d_trg_def r' E.\<epsilon>.map\<^sub>0_in_hhom E.\<epsilon>.components_are_equivalences by simp
        have e_trg: "\<guillemotleft>e_trg : trg\<^sub>D r' \<rightarrow>\<^sub>D F.map\<^sub>0 (E.G.map\<^sub>0 (trg\<^sub>D r'))\<guillemotright> \<and>
                     D.equivalence_map e_trg"
          using e_trg_def r' E.\<epsilon>.map\<^sub>0_in_hhom E.\<epsilon>.components_are_equivalences by simp
        obtain \<eta>_trg \<epsilon>_trg
        where eq_trg: "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_trg e_trg \<eta>_trg \<epsilon>_trg"
          using d_trg_def e_trg_def d_trg e_trg D.quasi_inverses_some_quasi_inverse
                D.quasi_inverses_def
          by blast
        interpret eq_trg: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D d_trg e_trg \<eta>_trg \<epsilon>_trg
          using eq_trg by simp

        interpret eqs: two_equivalences_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            d_src e_src \<eta>_src \<epsilon>_src d_trg e_trg \<eta>_trg \<epsilon>_trg
          ..
         
        interpret hom: subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : trg\<^sub>D d_src \<rightarrow>\<^sub>D trg\<^sub>D d_trg\<guillemotright>\<close>
          using D.hhom_is_subcategory by simp
        interpret hom': subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : src\<^sub>D d_src \<rightarrow>\<^sub>D src\<^sub>D d_trg\<guillemotright>\<close>
          using D.hhom_is_subcategory by simp
        interpret e: equivalence_of_categories hom.comp hom'.comp eqs.F eqs.G eqs.\<phi> eqs.\<psi>
          using eqs.induces_equivalence_of_hom_categories by simp

        have r'_in_hhom: "D.in_hhom r' (src\<^sub>D e_src) (src\<^sub>D e_trg)"
          using r' e_src e_trg by (simp add: D.in_hhom_def)

        define g' where "g' = d_trg \<star>\<^sub>D F g"
        have g': "D.is_left_adjoint g'"
          unfolding g'_def
          using fg r' d_trg trg_g C.left_adjoint_is_ide D.equivalence_is_adjoint
                D.left_adjoints_compose F.preserves_left_adjoint C.ideD(1) D.in_hhom_def
                F.preserves_trg
          by metis
        have 1: "D.is_right_adjoint (F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src)"
        proof -
          have "D.is_right_adjoint e_src"
            using r' e_src D.equivalence_is_adjoint by simp
          moreover have "D.is_right_adjoint (F f\<^sup>*\<^sup>C)"
            using fg C.left_adjoint_extends_to_adjoint_pair F.preserves_adjoint_pair by blast
          moreover have "src\<^sub>D (F f\<^sup>*\<^sup>C) = trg\<^sub>D e_src"
            using fg r' trg_f C.right_adjoint_is_ide e_src by auto
          ultimately show ?thesis
            using fg r' D.right_adjoints_compose F.preserves_right_adjoint by blast
        qed
        obtain f' where f': "D.adjoint_pair f' (F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src)"
          using 1 by auto
        have f': "D.is_left_adjoint f' \<and> F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src \<cong>\<^sub>D (f')\<^sup>*\<^sup>D"
          using f' D.left_adjoint_determines_right_up_to_iso D.left_adjoint_extends_to_adjoint_pair
          by blast

        have "r' \<cong>\<^sub>D d_trg \<star>\<^sub>D (e_trg \<star>\<^sub>D r' \<star>\<^sub>D d_src) \<star>\<^sub>D e_src"
          using r' r'_in_hhom D.isomorphic_def eqs.\<psi>_in_hom eqs.\<psi>_components_are_iso
                D.isomorphic_symmetric D.ide_char eq_src.antipar(2) eq_trg.antipar(2)
          by metis
        also have 1: "... \<cong>\<^sub>D d_trg \<star>\<^sub>D F (F.right_map r') \<star>\<^sub>D e_src"
        proof -
          have "e_trg \<star>\<^sub>D r' \<star>\<^sub>D d_src \<cong>\<^sub>D F (F.right_map r')"
          proof -
            have "D.in_hom (F.counit\<^sub>1 r')
                    (r' \<star>\<^sub>D d_src) (F.counit\<^sub>0 (trg\<^sub>D r') \<star>\<^sub>D F (F.right_map r'))"
              unfolding d_src_def
              using r' E.\<epsilon>.map\<^sub>1_in_hom(2) [of r'] by simp

            hence "r' \<star>\<^sub>D d_src \<cong>\<^sub>D F.counit\<^sub>0 (trg\<^sub>D r') \<star>\<^sub>D F (F.right_map r')"
              using r' D.isomorphic_def E.\<epsilon>.iso_map\<^sub>1_ide by auto
            thus ?thesis
              using r' e_trg_def E.\<epsilon>.components_are_equivalences D.isomorphic_symmetric
                    D.quasi_inverse_transpose(2)
              by (metis D.isomorphic_implies_hpar(1) F.preserves_isomorphic d_trg d_trg_def
                  eq_trg.ide_left fg)
          qed
          thus ?thesis
            using D.hcomp_ide_isomorphic D.hcomp_isomorphic_ide D.in_hhom_def
                  D.isomorphic_implies_hpar(4) d_trg e_src eq_src.antipar(1-2)
                  eq_trg.antipar(2) r'
            by force
        qed
        also have 2: "d_trg \<star>\<^sub>D F (F.right_map r') \<star>\<^sub>D e_src \<cong>\<^sub>D d_trg \<star>\<^sub>D (F g \<star>\<^sub>D F f\<^sup>*\<^sup>C) \<star>\<^sub>D e_src"
        proof -
          have "F (F.right_map r') \<cong>\<^sub>D F g \<star>\<^sub>D F f\<^sup>*\<^sup>C"
            by (meson C.hseq_char C.ideD(1) C.isomorphic_implies_ide(2) C.left_adjoint_is_ide
                C.right_adjoint_simps(1) D.isomorphic_symmetric D.isomorphic_transitive
                F.preserves_isomorphic F.weakly_preserves_hcomp fg)
          thus ?thesis
            using D.hcomp_ide_isomorphic D.hcomp_isomorphic_ide
            by (metis 1 D.hseqE D.ideD(1) D.isomorphic_implies_hpar(2)
                eq_src.ide_right eq_trg.ide_left)
        qed
        also have 3: "d_trg \<star>\<^sub>D (F g \<star>\<^sub>D F f\<^sup>*\<^sup>C) \<star>\<^sub>D e_src \<cong>\<^sub>D (d_trg \<star>\<^sub>D F g) \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src"
        proof -
          have "d_trg \<star>\<^sub>D (F g \<star>\<^sub>D F f\<^sup>*\<^sup>C) \<star>\<^sub>D e_src \<cong>\<^sub>D d_trg \<star>\<^sub>D F g \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src"
            by (metis C.left_adjoint_is_ide C.right_adjoint_simps(1) D.hcomp_assoc_isomorphic
                D.hcomp_ide_isomorphic D.hcomp_simps(1) D.hseq_char D.ideD(1)
                D.isomorphic_implies_hpar(2) F.preserves_ide calculation eq_src.ide_right
                eq_trg.ide_left fg)
          also have "d_trg \<star>\<^sub>D F g \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src \<cong>\<^sub>D (d_trg \<star>\<^sub>D F g) \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src"
            by (metis C.left_adjoint_is_ide D.hcomp_assoc_isomorphic D.hcomp_simps(2)
                D.hseq_char D.ideD(1) D.isomorphic_implies_ide(1) D.isomorphic_symmetric
                F.preserves_ide calculation eq_trg.ide_left f' fg)
          finally show ?thesis by blast
        qed
        also have "(d_trg \<star>\<^sub>D F g) \<star>\<^sub>D F f\<^sup>*\<^sup>C \<star>\<^sub>D e_src \<cong>\<^sub>D g' \<star>\<^sub>D f'\<^sup>*\<^sup>D"
          using g'_def f'
          by (metis 3 D.adjoint_pair_antipar(1) D.hcomp_ide_isomorphic D.hseq_char D.ideD(1)
              D.isomorphic_implies_ide(2) g')
        finally have "D.isomorphic r' (g' \<star>\<^sub>D f'\<^sup>*\<^sup>D)"
          by simp
        thus "\<exists>f' g'. D.is_left_adjoint f' \<and> D.is_left_adjoint g' \<and> r' \<cong>\<^sub>D g' \<star>\<^sub>D f'\<^sup>*\<^sup>D"
          using f' g' by auto
      qed
      show "\<And>f f' \<mu> \<mu>'. \<lbrakk> D.is_left_adjoint f; D.is_left_adjoint f';
                           \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>D f'\<guillemotright>; \<guillemotleft>\<mu>' : f \<Rightarrow>\<^sub>D f'\<guillemotright> \<rbrakk> \<Longrightarrow> D.iso \<mu> \<and> D.iso \<mu>' \<and> \<mu> = \<mu>'"
      proof -
        fix f f' \<mu> \<mu>'
        assume f: "D.is_left_adjoint f"
        and f': "D.is_left_adjoint f'"
        and \<mu>: "\<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>D f'\<guillemotright>"
        and \<mu>': "\<guillemotleft>\<mu>' : f \<Rightarrow>\<^sub>D f'\<guillemotright>"
        have "C.is_left_adjoint (F.right_map f) \<and> C.is_left_adjoint (F.right_map f')"
          using f f' E.G.preserves_left_adjoint by blast
        moreover have "\<guillemotleft>F.right_map \<mu> : F.right_map f \<Rightarrow>\<^sub>C F.right_map f'\<guillemotright> \<and>
                       \<guillemotleft>F.right_map \<mu>' : F.right_map f \<Rightarrow>\<^sub>C F.right_map f'\<guillemotright>"
          using \<mu> \<mu>' E.G.preserves_hom by simp
        ultimately 
        have "C.iso (F.right_map \<mu>) \<and> C.iso (F.right_map \<mu>') \<and>
                         F.right_map \<mu> = F.right_map \<mu>'"
          using C.BS3 by blast
        thus "D.iso \<mu> \<and> D.iso \<mu>' \<and> \<mu> = \<mu>'"
          using \<mu> \<mu>' G.reflects_iso G.is_faithful by blast
      qed
      show "\<And>f g. \<lbrakk> D.is_left_adjoint f; D.is_left_adjoint g; src\<^sub>D f = src\<^sub>D g \<rbrakk>
                     \<Longrightarrow> \<exists>r \<rho>. tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D r \<rho> f g"
      proof -
        fix f g
        assume f: "D.is_left_adjoint f"
        assume g: "D.is_left_adjoint g"
        assume fg: "src\<^sub>D f = src\<^sub>D g"
        have "C.is_left_adjoint (F.right_map f)"
          using f E.G.preserves_left_adjoint by blast
        moreover have "C.is_left_adjoint (F.right_map g)"
          using g E.G.preserves_left_adjoint by blast
        moreover have "src\<^sub>C (F.right_map f) = src\<^sub>C (F.right_map g)"
          using f g D.left_adjoint_is_ide fg by simp
        ultimately have
            1: "\<exists>r \<rho>. tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> (F.right_map f) (F.right_map g)"
          using C.BS2 by simp
        obtain r \<rho> where
            \<rho>: "tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> (F.right_map f) (F.right_map g)"
          using 1 by auto
        interpret \<rho>: tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C r \<rho> \<open>F.right_map f\<close> \<open>F.right_map g\<close>
          using \<rho> by simp
        obtain r' where
          r': "D.ide r' \<and> D.in_hhom r' (trg\<^sub>D f) (trg\<^sub>D g) \<and> C.isomorphic (F.right_map r') r"
          using f g \<rho>.ide_base \<rho>.tab_in_hom G.locally_essentially_surjective
          by (metis D.obj_trg E.G.preserves_reflects_arr E.G.preserves_trg \<rho>.leg0_simps(2-3)
              \<rho>.leg1_simps(2,4) \<rho>.base_in_hom(1))
        obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : r \<Rightarrow>\<^sub>C F.right_map r'\<guillemotright> \<and> C.iso \<phi>"
          using r' C.isomorphic_symmetric by blast
        have \<sigma>: "tabulation V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                   (F.right_map r') ((\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>) (F.right_map f) (F.right_map g)"
          using \<phi> \<rho>.is_preserved_by_base_iso by simp
        have 1: "\<exists>\<rho>'. \<guillemotleft>\<rho>' : g \<Rightarrow>\<^sub>D H\<^sub>D r' f\<guillemotright> \<and>
                      F.right_map \<rho>' = F.right_cmp (r', f) \<cdot>\<^sub>C (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>"
        proof -
          have "D.ide g"
            by (simp add: D.left_adjoint_is_ide g)
          moreover have "D.ide (H\<^sub>D r' f)"
            using f r' D.left_adjoint_is_ide by auto
          moreover have "src\<^sub>D g = src\<^sub>D (H\<^sub>D r' f)"
            using fg by (simp add: calculation(2))
          moreover 
          have "trg\<^sub>D g = trg\<^sub>D (H\<^sub>D r' f)"
            using calculation(2) r' by auto
          moreover have "\<guillemotleft>F.right_cmp (r', f) \<cdot>\<^sub>C (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho> :
                            F.right_map g \<Rightarrow>\<^sub>C F.right_map (r' \<star>\<^sub>D f)\<guillemotright>"
            using f g r' \<phi> D.left_adjoint_is_ide \<rho>.ide_base
            by (intro C.comp_in_homI, auto)
          ultimately show ?thesis
            using G.locally_full by simp
        qed
        obtain \<rho>' where \<rho>': "\<guillemotleft>\<rho>' : g \<Rightarrow>\<^sub>D H\<^sub>D r' f\<guillemotright> \<and>
                             F.right_map \<rho>' = F.right_cmp (r', f) \<cdot>\<^sub>C (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>"
          using 1 by auto
        have "tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D r' \<rho>' f g"
        proof -
          have "C.inv (F.right_cmp (r', f)) \<cdot>\<^sub>C F.right_map \<rho>' = (\<phi> \<star>\<^sub>C F.right_map f) \<cdot>\<^sub>C \<rho>"
            using r' f \<rho>' C.comp_assoc C.comp_cod_arr C.invert_side_of_triangle(1)
            by (metis D.adjoint_pair_antipar(1) D.arrI D.in_hhomE E.G.cmp_components_are_iso
                E.G.preserves_arr)
          thus ?thesis
            using \<sigma> \<rho>' G.reflects_tabulation
            by (simp add: D.left_adjoint_is_ide f r')
        qed
        thus "\<exists>r' \<rho>'. tabulation V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D r' \<rho>' f g"
          by auto
      qed
    qed
  qed

end
