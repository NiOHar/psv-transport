theory Transport_Examples
  imports
    Transport_Proof
    Transport.Transport_Syntax
    Transport.Transport_Prototype
    Main
    "HOL-Eisbach.Eisbach"
    "HOL-Library.FSet"
begin



(* locale transport_PER =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes PER: "transport.partial_equivalence_rel_equivalence L R l r"
begin

lemma implies_eq_rightI:
  assumes "P"
  shows "(P \<Longrightarrow> Q) \<equiv> Trueprop Q"
  using assms by auto

sublocale transport
  rewrites "\<And>P. (partial_equivalence_rel_equivalence \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (preorder_equivalence \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (order_equivalence \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (galois_equivalence \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (galois_connection \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (reflexive_on (in_field L) L \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (reflexive_on (in_field R) R \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (transitive L \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (transitive R \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (symmetric L \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (symmetric R \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P Q. (True \<Longrightarrow> PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> True \<Longrightarrow> PROP Q)"
  using PER
  by (auto intro!: implies_eq_rightI elim: transport.partial_equivalence_rel_equivalenceE
    transport.preorder_equivalence_galois_equivalenceE
    galois.galois_equivalenceE
    intro!: galois.order_equivalence_if_reflexive_on_in_field_if_galois_equivalence
  dest: galois_prop.half_galois_prop_leftD galois_prop.half_galois_prop_rightD)

end *)

definition "pos (i :: int) \<equiv> 0 \<le> i"

interpretation tZN : transport "(=\<^bsub>pos\<^esub>)" "(=)" nat int .

context
begin
interpretation t : transport L R l r for L R l r .

lemma perZN: "((=\<^bsub>pos\<^esub>) \<equiv>\<^bsub>PER\<^esub> (=)) nat int"
  unfolding pos_def by fastforce


lemmas related_Fun_Rel_combI = Dep_Fun_Rel_relD[where ?S="\<lambda>_ _. S" for S, rotated]
lemma related_Fun_Rel_lambdaI:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  and "T = (R \<Rrightarrow> S)"
  shows "T f g"
  using assms by blast


named_theorems trp_side_condition

lemma tZN_left_total [trp_side_condition]: "left_total_on pos tZN.left_Galois"
  unfolding pos_def
  by (intro left_total_onI in_domI tZN.left_GaloisI bin_rel_restrict_leftI)
  (auto intro: nat_0_le[symmetric])

lemma tZN_rel_injective [trp_side_condition]: "rel_injective tZN.left_Galois"
  by (intro rel_injectiveI) auto

lemma rev_imp_top [trp_side_condition]: "(R \<Rrightarrow> (\<longleftarrow>)) \<top> P"
  by auto

end
text \<open>Unification Tuning\<close>

declare [[ML_map_context \<open>Logger.set_log_levels Logger.root_logger Logger.ALL\<close>]]
(* declare [[show_types]] *)
declare [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (fn _ => fn binders => Tactic_Util.set_kernel_ho_unif_bounds 1 1
    #> Tactic_Util.silence_kernel_ho_bounds_exceeded
    #> Higher_Order_Unification.unify binders)
  (Standard_Unification_Combine.metadata \<^binding>\<open>HO_unif\<close> Prio.VERY_LOW)\<close>]]

ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints_Concl_Combine
    and functor_name = Unification_Combine
    and id = \<open>"uhint_concl"\<close>}
\<close>
local_setup \<open>Standard_Unification_Combine.setup_attribute NONE\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unification_Hints_Concl_Mixed_Unification
    and functor_name = Mixed_Unification
    and id = \<open>"uhint_concl"\<close>
    and more_args = \<open>structure UC = Standard_Unification_Hints_Concl_Combine\<close>}
\<close>
declare [[uhint where concl_unifier =
  Standard_Unification_Hints_Concl_Mixed_Unification.first_higherp_decomp_comb_higher_unify]]


text \<open>Examples\<close>

ML_val\<open>
  Transport.mk_term_skeleton 0 @{term "\<forall>\<^bsub>in_field L\<^esub> (xs :: 'a fset) . \<forall>\<^bsub>in_field L\<^esub> xs' . L xs' xs"}
  |> Syntax.pretty_term @{context}
\<close>

lemma "\<forall>\<^bsub>pos\<^esub> (x :: int). x = x"
  apply (rule rev_impD[of _ "_ (_ _) (\<lambda>x. _ x x)"])
  apply (urule related_Fun_Rel_combI)
  apply (urule related_Fun_Rel_lambdaI)
  apply (urule related_Fun_Rel_combI)
  apply uassm
  apply (urule related_Fun_Rel_combI)
  apply uassm
  apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
  apply (urule refl)
  apply (urule iffD2[OF Fun_Rel_rev_imp_all_on_iff_left_total_on_restrict_right])
  apply (urule tZN_left_total)
  apply auto
  done

ML\<open>structure A = Higher_Order_Unification\<close>

lemma tZN_00: "tZN.left_Galois 0 0"
  by (simp add: bin_rel_restrict_leftI in_codomI pos_def tZN.left_Galois_iff_in_codom_and_left_rel_right)
lemma tZN_addadd: "(tZN.left_Galois \<Rrightarrow> tZN.left_Galois \<Rrightarrow> tZN.left_Galois) ((+) :: int \<Rightarrow> int \<Rightarrow> int) ((+) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  apply (intro Dep_Fun_Rel_relI)
  by (metis (full_types) bin_rel_restrict_leftE galois_rel.left_GaloisE of_nat_add perZN tZN.galois_connectionE tZN.galois_equivalence_def tZN.partial_equivalence_rel_equivalence_def tZN.right_left_Galois_if_right_relI)


lemma "\<forall>\<^bsub>pos\<^esub> (x :: int) . x = x + 0"
  apply (rule rev_impD[of _ "_ (_ _) (\<lambda>x. _ x (_ x _))"])
  apply (urule related_Fun_Rel_combI)
    apply (urule related_Fun_Rel_lambdaI)
     apply (urule related_Fun_Rel_combI)
      apply (urule related_Fun_Rel_combI)
       apply (urule tZN_00)
      apply (urule related_Fun_Rel_combI)
       apply uassm
      apply (urule tZN_addadd)
     apply (urule related_Fun_Rel_combI)
      apply uassm
  apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
    apply (urule refl)
 apply (urule iffD2[OF Fun_Rel_rev_imp_all_on_iff_left_total_on_restrict_right])
   apply (urule tZN_left_total)
  by simp

lemma tZN_restrict[simp,uhint]: "tZN.left_Galois\<restriction>\<^bsub>pos\<^esub> = tZN.left_Galois"
  using bin_rel_restrict_leftE by blast

lemma tZN_injective_on_pos: "rel_injective_on (pos :: int \<Rightarrow> bool) (tZN.left_Galois\<restriction>\<^bsub>pos\<^esub>)"
  by (intro rel_injective_onI) auto

lemma tZN_injective_at_top: "rel_injective_at (\<top> :: nat \<Rightarrow> bool) (tZN.left_Galois\<restriction>\<^bsub>pos\<^esub>)"
  by (intro rel_injective_atI) auto


lemma tZN_surjective_at_top: "rel_surjective_at (\<top> :: nat \<Rightarrow> bool) (tZN.left_Galois\<restriction>\<^bsub>pos\<^esub>)"
  apply (intro rel_surjective_atI)
  using pos_def by force

lemma "\<exists>\<^bsub>pos\<^esub> (x :: int) . x = 0"
  apply (rule rev_impD[of _ "_ _ (\<lambda> x . _ x _)"])
   apply (urule related_Fun_Rel_combI)
    apply (urule related_Fun_Rel_lambdaI)
     apply (urule related_Fun_Rel_combI)
      apply (urule tZN_00)
     apply (urule related_Fun_Rel_combI)
      apply uassm
     apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
      apply (urule tZN_injective_at_top)
  apply (urule rev_imp_top)
    apply (urule refl)
     apply (urule Fun_Rel_restricts_rev_imp_ex_on_if_rel_surjective_at)
   apply (urule tZN_surjective_at_top)
  apply blast
  done

(* from https://www.isa-afp.org/sessions/transport/#Transport_Lists_Sets_Examples.html *)
definition "LFSL xs xs' \<equiv> fset_of_list xs = fset_of_list xs'"
definition "(LFSR :: 'a fset \<Rightarrow> _) \<equiv> (=)"
definition "LSL xs xs' \<equiv> set xs = set xs'"
definition "(LSR :: 'a set \<Rightarrow> _) \<equiv> (=\<^bsub>finite :: 'a set \<Rightarrow> bool\<^esub>)"

context
begin

interpretation tFSetList : transport LFSR LFSL sorted_list_of_fset fset_of_list .
interpretation t : transport L R l r for L R l r .
text \<open>Proofs of equivalences.\<close>

lemma list_fset_PER: "(LFSL \<equiv>\<^bsub>PER\<^esub> LFSR) fset_of_list sorted_list_of_fset"
  unfolding LFSL_def LFSR_def by fastforce

lemma list_set_PER: "(LSL \<equiv>\<^bsub>PER\<^esub> LSR) set sorted_list_of_set"
  unfolding LSL_def LSR_def by fastforce

lemma setListInj: "rel_injective (tFSetList.left_Galois :: ('a :: linorder) fset \<Rightarrow> 'a list \<Rightarrow> bool)" 
  unfolding LFSR_def by auto
lemma setListLeftTot: "Binary_Relations_Left_Total.left_total (tFSetList.left_Galois :: ('a :: linorder) fset \<Rightarrow> _ \<Rightarrow> _)"
  by (metis (full_types) Binary_Relations_Left_Total.left_totalI LFSR_def in_domI list_fset_PER tFSetList.left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right)

lemma "\<forall> (xs :: ('a :: linorder) fset) . LFSR xs xs"
  apply (rule rev_impD[of _ "_ (\<lambda> xs . _ xs xs)"])
   apply (urule related_Fun_Rel_combI)
    apply (urule related_Fun_Rel_lambdaI)
     apply (urule related_Fun_Rel_combI)
      apply uassm
       apply (urule related_Fun_Rel_combI)
     apply uassm
     apply (urule tFSetList.Fun_Rel_rev_imp_left_rightI)
      defer
      defer
  apply (urule refl)
     apply (urule Fun_Rel_rev_imp_all_if_left_total)
     apply (urule setListLeftTot)
  defer
    apply (use list_fset_PER in auto)[1]
   apply (use list_fset_PER in auto)[1]
  oops

end

context
  fixes L :: "bool \<Rightarrow> bool \<Rightarrow> bool" and R :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  and l :: "bool \<Rightarrow> bool" and r :: "bool \<Rightarrow> bool"
  defines "L \<equiv> (\<lambda> a b . (a = False \<and> b = True))"
  and "R \<equiv> L"
  and "l \<equiv> \<lambda> x . x"
  and "r \<equiv> \<lambda> x . x"
begin

interpretation t: transport L R l r .
lemma "t.galois_equivalence" apply (intro t.galois_equivalenceI t.galois_connectionI) 
     apply (simp add: R_def dep_mono_wrt_relI l_def) apply (simp add: R_def dep_mono_wrt_relI r_def)
    apply (intro t.galois_propI t.half_galois_prop_leftI)
  using R_def l_def r_def t.left_Galois_iff_in_codom_and_left_rel_right apply blast
  apply (intro t.half_galois_prop_rightI)
  using R_def l_def r_def t.Galois_right_iff_in_dom_and_left_right_rel apply blast
  using R_def l_def r_def t.galois_propI' by fastforce

lemma "\<not> (left_total_on (in_field L) t.left_Galois)"
  by (metis L_def in_codom_def in_domE in_field_if_in_codom left_total_on_pred_def t.left_total_on_left_if_left_total_on_left_GaloisI)
end

context galois
begin

(* should work with Galois_equivalence + reflexive L *)
lemma left_gal_left_tot: 
  assumes "(L \<equiv>\<^bsub>PER\<^esub> R) l r"
  shows"left_total_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<^bsub>L\<^esub>\<lessapprox>)"
proof (intro left_total_onI, elim in_fieldE)
  fix x x'
  assume ass: "x \<le>\<^bsub>L\<^esub> x'"
  then have "l x \<le>\<^bsub>R\<^esub> l x'" using assms
    by (fastforce intro: galois.right_left_Galois_if_right_relI elim: galois_rel.left_GaloisE transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE)
  have "x \<le>\<^bsub>L\<^esub> r (l x')" using assms ass rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel by (fastforce intro: galois.right_left_Galois_if_right_relI elim: galois_rel.left_GaloisE transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE)
  with \<open>l x \<le>\<^bsub>R\<^esub> l x'\<close> have "x \<^bsub>L\<^esub>\<lessapprox> l x'" by auto
  then show "in_dom (\<^bsub>L\<^esub>\<lessapprox>) x" by auto
next
  fix x x'
  assume ass: "x' \<le>\<^bsub>L\<^esub> x"
  from assms have "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>" by (fastforce elim: transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE order_functors.order_equivalenceE)
  with assms ass have "x \<^bsub>L\<^esub>\<lessapprox> l x" using left_Galois_left_if_in_codom_if_inflationary_on_in_codomI assms
    by (fastforce simp: inflationary_on_pred_def transport.left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence)
  then show "in_dom (\<^bsub>L\<^esub>\<lessapprox>) x" by auto
qed
  

end

context
  fixes L1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and R1 :: "'b :: linorder \<Rightarrow> 'b \<Rightarrow> bool"
  and l1 :: "'a \<Rightarrow> 'b" and r1 :: "'b \<Rightarrow> 'a"
  and L :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" and R :: "'b list \<Rightarrow> 'b list \<Rightarrow> bool"
  and l :: "'a fset \<Rightarrow> 'b list" and r :: "'b list \<Rightarrow> 'a fset"
  assumes per1: "(L1 \<equiv>\<^bsub>PER\<^esub> R1) l1 r1"
  defines "L \<equiv> rel_fset L1" and "R \<equiv> rel_map fset_of_list (rel_fset R1)"
  and "l \<equiv> Functions_Base.comp (sorted_list_of_fset) (fimage l1)"
  and "r \<equiv> Functions_Base.comp (fimage r1) fset_of_list"
begin

interpretation t: transport L R l r .
                                     
lemma symmetric_imp_symmetric_rel_fset: "symmetric A \<Longrightarrow> symmetric (rel_fset A)"
  by (simp add: rel_fset_alt_def rel_iff_rel_if_symmetric symmetricI)

lemma transitive_imp_transitive_rel_fset: "transitive A \<Longrightarrow> transitive (rel_fset A)"
  by (smt (verit, del_insts) transitiveI rel_fset_alt_def transitiveD)

lemma symmetric_imp_symmetric_rel_map: "symmetric A \<Longrightarrow> symmetric (rel_map fset_of_list (rel_fset A))"
  by (auto simp: symmetricD symmetric_imp_symmetric_rel_fset)

lemma 
 infl_L1:  "inflationary_on (in_field L1) L1 (order_functors.unit l1 r1)" using per1 
  apply (elim transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE  order_functors.order_equivalenceE rel_equivalence_onE) .

lemma 
 defl_L1:  "deflationary_on (in_field L1) L1 (order_functors.unit l1 r1)" using per1 
  apply (elim transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE  order_functors.order_equivalenceE rel_equivalence_onE) .

lemma infl_R1: "inflationary_on (in_field R1) R1 (order_functors.counit l1 r1)" using per1
 apply (elim transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE  order_functors.order_equivalenceE rel_equivalence_onE) .

lemma defl_R1: "deflationary_on (in_field R1) R1 (order_functors.counit l1 r1)" using per1
 apply (elim transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE  order_functors.order_equivalenceE rel_equivalence_onE) .


lemma per: "(L \<equiv>\<^bsub>PER\<^esub> R) l r"
proof (intro transport.partial_equivalence_rel_equivalence_if_order_equivalenceI)
  show "t.order_equivalence" proof
      have "(L1 \<Rrightarrow>\<^sub>m R1) l1" using per1
        by (metis order_functors.order_equivalenceE transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE)
      show "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l" proof
        fix x y
        assume "L x y"
        then show "R (l x) (l y)" unfolding l_def R_def L_def using \<open>(L1 \<Rrightarrow>\<^sub>m R1) l1\<close> by (fastforce simp: dep_mono_wrt_relD rel_fset_alt_def) +
      qed
      have "(R1 \<Rrightarrow>\<^sub>m L1) r1" using per1
        by (metis order_functors.order_equivalenceE transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE)
      show "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r" proof
        fix x y
        assume "R x y"
        then show "L (r x) (r y)"  unfolding r_def R_def L_def using \<open>(R1 \<Rrightarrow>\<^sub>m L1) r1\<close> by (fastforce simp: dep_mono_wrt_relD rel_fset_alt_def) +
      qed
      show "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) t.unit" proof (intro rel_equivalence_onI)
        show "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) t.unit" proof (intro inflationary_onI) 
          fix x
          assume  "in_field L x"
          from \<open>in_field L x\<close> have "\<forall> a . a |\<in>| x \<longrightarrow>  in_field L1 a" using L_def
            by (fastforce simp: in_fieldE in_fieldI(1) in_fieldI(2) rel_fset_alt)
          with infl_L1 have "\<forall> a . a |\<in>| x \<longrightarrow> L1 a (r1 (l1 a))"
            by (simp add: inflationary_on_pred_def order_functors.unit_eq)
          have "\<forall>a . (a |\<in>| r (l x) \<longleftrightarrow> (\<exists> b . (b |\<in>| x \<and> (r1 (l1 b) = a))))" using r_def l_def by auto
          then show "in_field (\<le>\<^bsub>L\<^esub>) x \<Longrightarrow> x \<le>\<^bsub>L\<^esub> t.unit x" using order_functors.unit_eq[of l r] L_def \<open>\<forall> a . a |\<in>| x \<longrightarrow> L1 a (r1 (l1 a))\<close>
            using rel_fset_alt by force
        qed
        show "deflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) t.unit" proof (intro deflationary_onI) 
        fix x
        assume  "in_field L x"
        from \<open>in_field L x\<close> have "\<forall> a . a |\<in>| x \<longrightarrow>  in_field L1 a" using L_def
          by (fastforce simp: in_fieldE in_fieldI(1) in_fieldI(2) rel_fset_alt)
        with defl_L1 have "\<forall> a . a |\<in>| x \<longrightarrow> L1 (r1 (l1 a)) a"
          by (metis deflationary_onD order_functors.unit_eq)
        have "\<forall>a . (a |\<in>| r (l x) \<longleftrightarrow> (\<exists> b . (b |\<in>| x \<and> (r1 (l1 b) = a))))" using r_def l_def by auto
        then show "in_field (\<le>\<^bsub>L\<^esub>) x \<Longrightarrow> t.unit x \<le>\<^bsub>L\<^esub> x" using order_functors.unit_eq[of l r] L_def \<open>\<forall> a . a |\<in>| x \<longrightarrow> L1 (r1 (l1 a)) a\<close>
          using rel_fset_alt by force
      qed
    qed
    show "rel_equivalence_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) t.counit" proof (intro rel_equivalence_onI)
      show "inflationary_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) t.counit" proof (intro inflationary_onI) 
        fix x
        assume  "in_field R x"
        from \<open>in_field R x\<close> have "\<forall> a . List.member x a \<longrightarrow>  in_field R1 a" using R_def
          by (fastforce simp: fset_of_list.rep_eq in_fieldE in_fieldI(1) in_fieldI(2) in_set_member rel_fset_alt)
        with infl_R1 have "\<forall> a . List.member x a \<longrightarrow> R1 a (l1 (r1 a))"
          by (simp add: inflationary_on_pred_def order_functors.counit_eq)
        have "\<forall>a . (List.member (l (r x)) a \<longleftrightarrow> (\<exists> b . (List.member x b \<and> (l1 (r1 b) = a))))" using r_def l_def fset_of_list.rep_eq
          by (smt (verit, best) comp_eq fimage_iff in_set_member sorted_list_of_fset_simps(1))
        then show "in_field (\<le>\<^bsub>R\<^esub>) x \<Longrightarrow> x \<le>\<^bsub>R\<^esub> t.counit x" using order_functors.counit_eq[of l r] R_def \<open>\<forall> a . List.member x a \<longrightarrow> R1 a (l1 (r1 a))\<close>
            rel_fset_alt fset_of_list.rep_eq
          by (fastforce simp: fset_of_list.rep_eq in_set_member rel_fset_alt)
      qed
      show "deflationary_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) t.counit" proof (intro deflationary_onI) 
        fix x
        assume  "in_field R x"
        from \<open>in_field R x\<close> have "\<forall> a . List.member x a \<longrightarrow>  in_field R1 a" using R_def
          by (fastforce simp: fset_of_list.rep_eq in_fieldE in_fieldI(1) in_fieldI(2) in_set_member rel_fset_alt)
        with defl_R1 have "\<forall> a . List.member x a \<longrightarrow> R1 (l1 (r1 a)) a"
          by (metis deflationary_onD order_functors.counit_eq)
        have "\<forall>a . (List.member (l (r x)) a \<longleftrightarrow> (\<exists> b . (List.member x b \<and> (l1 (r1 b) = a))))" using r_def l_def fset_of_list.rep_eq
          by (smt (verit, best) comp_eq fimage_iff in_set_member sorted_list_of_fset_simps(1))
        then show "in_field (\<le>\<^bsub>R\<^esub>) x \<Longrightarrow> t.counit x \<le>\<^bsub>R\<^esub> x" using order_functors.counit_eq[of l r] R_def \<open>\<forall> a . List.member x a \<longrightarrow> R1 (l1 (r1 a)) a\<close>
             rel_fset_alt fset_of_list.rep_eq
          by (fastforce simp: fset_of_list.rep_eq in_set_member rel_fset_alt)
      qed
    qed
  qed
  show "partial_equivalence_rel L" proof
      have "transitive L1" using per1 apply (elim transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_galois_equivalenceE) by blast
      then show "transitive L"  using L_def transitive_imp_transitive_rel_fset by auto
      show "symmetric L" using L_def symmetric_imp_symmetric_rel_fset per1 
      by (auto elim: transport.partial_equivalence_rel_equivalenceE)
  qed
next
  show "partial_equivalence_rel R" proof
    have "transitive R1" using per1 apply (elim transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_galois_equivalenceE) by blast
    then show "transitive R" using R_def transitive_imp_transitive_rel_fset by fastforce
    have "symmetric R1" using per1 apply  (elim transport.partial_equivalence_rel_equivalenceE) by blast
    then show "symmetric R" using R_def symmetric_imp_symmetric_rel_map by blast
  qed
qed


(* declare [[show_types]] *)
lemma "\<forall>\<^bsub>in_field L\<^esub> (xs :: 'a fset) . \<forall>\<^bsub>in_field L\<^esub> xs' . L xs' xs"
  apply (rule rev_impD[of _ "_ _ (\<lambda>xs. _ _ (\<lambda>xs'. _ xs' xs))"])
   apply (urule related_Fun_Rel_combI)
    apply (urule related_Fun_Rel_lambdaI)
     apply (urule related_Fun_Rel_combI)
      apply (urule related_Fun_Rel_lambdaI)
       apply (urule related_Fun_Rel_combI)
        apply uassm
       apply (urule related_Fun_Rel_combI)
  apply (tactic \<open>rotate_tac 1 1\<close>)
        apply uassm
     apply (urule t.Fun_Rel_rev_imp_left_rightI)
     defer
     defer
     apply (urule refl)
    apply (urule iffD2[OF Fun_Rel_rev_imp_all_on_iff_left_total_on_restrict_right]) (* here we need to have the type specified *)
       defer
       apply (urule refl)
      apply (urule iffD2[OF Fun_Rel_rev_imp_all_on_iff_left_total_on_restrict_right]) (* here we need to have the type specified *)
      defer
     defer
  using per apply blast
  using per apply blast
  using per apply (urule galois.left_gal_left_tot)
  using per apply (urule galois.left_gal_left_tot)
  oops

end

named_theorems trp_register
declare Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI[trp_register]

method transport_step =
  (urule trp_register)
  | (urule related_Fun_Rel_combI related_Fun_Rel_lambdaI)
  | uassm

lemma "\<forall>\<^bsub>pos\<^esub> (x :: int). x = x"
  apply (rule rev_impD[of _ "_ (_ _) (\<lambda>x. _ x x)"])
  apply transport_step
  (* apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI) *)
  oops

  (* apply transport_step *)
  (* apply (urule related_Fun_Rel_combI)
  apply (urule related_Fun_Rel_lambdaI)
  apply (urule related_Fun_Rel_combI)
  apply uassm
  apply (urule related_Fun_Rel_combI)
  apply uassm
  apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
  apply (urule refl)
  apply (urule iffD2[OF Fun_Rel_rev_imp_all_on_iff_left_total_on_restrict_right])
  supply [[uhint where concl_unifier = Higher_Order_Unification.unify]]
  apply (urule tZN_left_total)
  apply auto
  done *)

end


