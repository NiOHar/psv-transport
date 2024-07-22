theory Transport_Examples
  imports
    "HOL-Eisbach.Eisbach"
    "HOL-Library.FSet"
    Main
    ML_Unification.Unify_Assumption_Tactic
    ML_Unification.Unify_Fact_Tactic
    Transport.Transport_Syntax
    Transport.Transport_Prototype
    Transport.Transport_White_Box
    Transport.HOL_Alignment_Binary_Relations
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

lemma transport_start:
  assumes "(\<longleftarrow>) P Q"
  and "Q"
  shows "P"
  using assms by auto

lemma transport_comb:
  assumes "R x y"
  and "(R \<Rrightarrow> S) f g"
  shows "S (f x) (g y)"
  using assms by auto

lemma transport_lambda:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (g y)"
  and "T = (R \<Rrightarrow> S)"
  shows "T f g"
  using assms by auto

theorem transport_Fun_Rel_rev_imp_ball_if_left_total_on_restrict_right:
  assumes "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms Fun_Rel_rev_imp_ball_iff_left_total_on_restrict_right by blast

definition "nonneg (i :: int) \<equiv> 0 \<le> i"

lemma nonneg_iff [iff]: "nonneg i \<longleftrightarrow> 0 \<le> i"
  unfolding nonneg_def by simp

interpretation tZN : transport "(=\<^bsub>nonneg\<^esub>)" "(=)" nat int .

context
begin
interpretation t : transport L R l r for L R l r .

lemma perZN: "((=\<^bsub>nonneg\<^esub>) \<equiv>\<^bsub>PER\<^esub> (=)) nat int"
  unfolding nonneg_def by fastforce

named_theorems trp_side_condition

lemma tZN_left_total [trp_side_condition]: "left_total_on nonneg tZN.left_Galois"
  by (intro left_total_onI) (auto intro: nat_0_le[symmetric])

lemma tZN_rel_injective [trp_side_condition]: "rel_injective tZN.left_Galois"
  by (intro rel_injectiveI) auto

lemma rev_imp_top [trp_side_condition]: "((R :: _ \<Rightarrow> _ \<Rightarrow> bool) \<Rrightarrow> (\<longleftarrow>)) \<top> P"
  by auto

end

text \<open>Unification Tuning\<close>

declare [[ucombine add = \<open>Standard_Unification_Combine.eunif_data
  (fn _ => fn binders => Tactic_Util.set_kernel_ho_unif_bounds 1 1
    #> Tactic_Util.silence_kernel_ho_bounds_exceeded
    #> Higher_Order_Unification.unify binders)
  (Standard_Unification_Combine.metadata \<^binding>\<open>HO_unif\<close> Prio.VERY_LOW)\<close>]]


text \<open>Examples\<close>

lemma "\<forall>x : nonneg. x = x"
  apply (rule transport_start[where ?Q="_ (_ _) (\<lambda>x. _ x x)"])
  apply (urule transport_comb)
  apply (urule transport_lambda)
  apply (urule transport_comb)
  apply uassm
  apply (urule transport_comb)
  apply uassm
  apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
  apply (urule refl)
  apply (urule transport_Fun_Rel_rev_imp_ball_if_left_total_on_restrict_right)
  apply (urule tZN_left_total)
  apply auto
  done

ML\<open>structure A = Higher_Order_Unification\<close>


lemma tZN_00: "tZN.left_Galois 0 0"
  by (intro tZN.left_GaloisI) auto

lemma tZN_add_add: "(tZN.left_Galois \<Rrightarrow> tZN.left_Galois \<Rrightarrow> tZN.left_Galois) ((+) :: int \<Rightarrow> _) ((+) :: nat \<Rightarrow> _)"
  by (intro Fun_Rel_relI tZN.left_GaloisI) (auto elim!: tZN.left_GaloisE rel_restrict_leftE)

paragraph \<open>Unification Hints\<close>

lemma restrict_left_eq_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)"
  and "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<equiv> S"
  shows "R\<restriction>\<^bsub>P\<^esub> \<equiv> S"
  using assms by simp

lemma restrict_right_eq_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'b \<Rightarrow> bool)"
  and "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<equiv> S"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> \<equiv> S"
  using assms by simp

ML\<open>
  Transport.mk_term_skeleton 0 @{term "\<forall>x : nonneg. x = x + 0"}
  |> Syntax.pretty_term @{context}
\<close>

lemma "\<forall>x : nonneg. x = x + 0"
  (*TODO: difficult unification problem if type is not fixed: wrong instantiation for type of x is chosen*)
  apply (rule transport_start[where ?Q="_ _ (\<lambda>(x :: nat). _ x (_ x _))"])
  apply (urule transport_comb)
    apply (urule transport_lambda)
     apply (urule transport_comb)
      apply (urule transport_comb)
       apply (urule tZN_00)
      apply (urule transport_comb)
       apply uassm
      apply (urule tZN_add_add)
     apply (urule transport_comb)
      apply uassm
  apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
    apply (urule refl)
  apply (urule transport_Fun_Rel_rev_imp_ball_if_left_total_on_restrict_right)
   apply (urule tZN_left_total)
  by auto

lemma tZN_restrict[uhint]: "tZN.left_Galois\<restriction>\<^bsub>nonneg\<^esub> = tZN.left_Galois"
  using rel_restrict_leftE by blast

lemma tZN_injective_on_nonneg [trp_side_condition]: "rel_injective_on (nonneg :: int \<Rightarrow> bool) (tZN.left_Galois)"
  by (intro rel_injective_onI) auto

lemma tZN_surjective [trp_side_condition]: "rel_surjective tZN.left_Galois"
  apply (intro rel_surjectiveI)
  using nonneg_def by force

lemma "\<exists>x : nonneg. x = 0"
  apply (rule transport_start[where ?Q="_ _ (\<lambda>x. _ x _)"])
   apply (urule transport_comb)
    apply (urule transport_lambda)
     apply (urule transport_comb)
      apply (urule tZN_00)
     apply (urule transport_comb)
      apply uassm
     apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
     defer
     defer
    apply (urule refl)
     apply (urule Fun_Rel_restricts_rev_imp_bex_if_rel_surjective_at)
   apply (urule trp_side_condition)
  defer
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
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
lemma setListLeftTot [trp_side_condition]:
  "Binary_Relations_Left_Total.left_total (tFSetList.left_Galois :: ('a :: linorder) fset \<Rightarrow> _ \<Rightarrow> _)"
  by (metis (full_types) Binary_Relations_Left_Total.left_totalI LFSR_def in_domI list_fset_PER tFSetList.left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right)

lemma "\<forall> (xs :: ('a :: linorder) fset) . LFSR xs xs"
  apply (rule transport_start[where ?Q="_ (\<lambda>xs . _ xs xs)"])
   apply (urule transport_comb)
    apply (urule transport_lambda)
     apply (urule transport_comb)
      apply uassm
       apply (urule transport_comb)
     apply uassm
    defer
  apply (urule refl)
     apply (urule Fun_Rel_rev_imp_all_if_left_total)
     defer
     defer
    apply (urule tFSetList.Fun_Rel_left_Galois_left_Galois_rev_imp_left_rightI)
    apply (use list_fset_PER in auto)[1]
    apply (use list_fset_PER in auto)[1]
    apply (urule trp_side_condition)
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
lemma "t.galois_equivalence"
  using R_def l_def r_def t.galois_propI'
  by (intro t.galois_equivalenceI t.galois_connectionI) fastforce+

(*Note: left_total on in_dom but not in_codom*)
lemma "\<not> (left_total_on (in_codom L) t.left_Galois)"
  by (metis L_def galois.left_total_on_left_if_left_total_on_left_GaloisI in_codomI left_total_onE)
end

context galois
begin

(* should work with Galois_equivalence + reflexive L *)
lemma left_gal_left_tot [trp_side_condition]:
  assumes "(L \<equiv>\<^bsub>PER\<^esub> R) l r"
  shows"left_total_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<^bsub>L\<^esub>\<lessapprox>)"
proof (intro left_total_onI, elim in_fieldE)
  fix x x'
  assume ass: "x \<le>\<^bsub>L\<^esub> x'"
  then have "l x \<le>\<^bsub>R\<^esub> l x'" using assms
    by (fastforce intro: galois.right_left_Galois_if_right_relI elim: galois_rel.left_GaloisE transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE)
  have "x \<le>\<^bsub>L\<^esub> r (l x')"  sorry
    (* using assms ass rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel by (fastforce intro!: galois.right_left_Galois_if_right_relI elim!: galois_rel.left_GaloisE transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE) *)
  with \<open>l x \<le>\<^bsub>R\<^esub> l x'\<close> have "x \<^bsub>L\<^esub>\<lessapprox> l x'" by auto
  then show "in_dom (\<^bsub>L\<^esub>\<lessapprox>) x" by auto
next
  fix x x'
  assume ass: "x' \<le>\<^bsub>L\<^esub> x"
  from assms have "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>" by (fastforce elim: transport.partial_equivalence_rel_equivalenceE transport.preorder_equivalence_order_equivalenceE order_functors.order_equivalenceE)
  with assms ass have "x \<^bsub>L\<^esub>\<lessapprox> l x" using left_Galois_left_if_in_codom_if_inflationary_on_in_codomI assms
    (* by (fastforce simp: inflationary_on_pred_def transport.left_Galois_left_if_left_rel_if_partial_equivalence_rel_equivalence) *)
    sorry
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

lemma symmetric_imp_symmetric_rel_fset: "symmetric (A :: 'd \<Rightarrow> 'd \<Rightarrow> bool) \<Longrightarrow> symmetric (rel_fset A)"
  supply HOL_bin_rel_alignment[uhint] by (ufact FSet.fset.rel_symp)

lemma transitive_imp_transitive_rel_fset: "transitive (A :: 'd \<Rightarrow> 'd \<Rightarrow> bool) \<Longrightarrow> transitive (rel_fset A)"
  supply HOL_bin_rel_alignment[uhint] by (ufact FSet.fset.rel_transp)

lemma symmetric_imp_symmetric_rel_map: "symmetric A \<Longrightarrow> symmetric (rel_map fset_of_list (rel_fset A))"
  sorry

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

lemma per: "(L \<equiv>\<^bsub>PER\<^esub> R) l r" sorry

(* declare [[show_types]] *)
lemma "\<forall>(xs :: 'a fset) : in_field L. \<forall>xs' : in_field L. L xs' xs"
  apply (rule transport_start[where ?Q="_ _ (\<lambda>(xs :: 'b list). _ _ (\<lambda>xs'. _ xs' xs))"])
   apply (urule transport_comb)
    apply (urule transport_lambda)
     apply (urule transport_comb)
      apply (urule transport_lambda)
       apply (urule transport_comb)
        apply uassm
       apply (urule transport_comb)
    (*rotation needed (need to pick the right assumption for bvars*)
    apply (tactic \<open>rotate_tac 1 1\<close>)
    apply uassm
    defer
     (* apply (urule t.Fun_Rel_rev_imp_left_rightI) *)
     apply (urule refl)
    (* here we need to have the type specified; otherwise unifier loops *)
    apply (urule transport_Fun_Rel_rev_imp_ball_if_left_total_on_restrict_right)
       defer
       apply (urule refl)
      apply (urule transport_Fun_Rel_rev_imp_ball_if_left_total_on_restrict_right) (* here we need to have the type specified *)
      defer
     defer
     apply (urule t.Fun_Rel_left_Galois_left_Galois_rev_imp_left_rightI)
  using per apply blast
  using per apply blast
  using per apply (urule trp_side_condition)
  using per apply (urule trp_side_condition)
  oops

end

named_theorems trp_register
declare Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI[trp_register]

method transport_step =
  (urule trp_register)
  | (urule transport_comb transport_lambda)
  | uassm

lemma "\<forall>x : nonneg. x = x"
  apply (rule transport_start[where ?Q="_ (_ _) (\<lambda>x. _ x x)"])
  apply transport_step
  (* apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI) *)
  oops

  (* apply transport_step *)
  (* apply (urule transport_comb)
  apply (urule transport_lambda)
  apply (urule transport_comb)
  apply uassm
  apply (urule transport_comb)
  apply uassm
  apply (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI)
  apply (urule trp_side_condition)
  apply (urule trp_side_condition)
  apply (urule refl)
  apply (urule transport_Fun_Rel_rev_imp_ball_if_left_total_on_restrict_right)
  supply [[uhint where concl_unifier = Higher_Order_Unification.unify]]
  apply (urule tZN_left_total)
  apply auto
  done *)

end
