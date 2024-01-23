theory Transport_Examples
  imports
    Transport_Proof
    Transport.Transport_Syntax
    Transport.Transport_Prototype
    Main
    "HOL-Eisbach.Eisbach"
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
  Standard_Unification_Hints_Concl_Mixed_Unification.first_higherp_first_comb_higher_unify]]


text \<open>Examples\<close>

ML_val\<open>
  Transport.mk_term_skeleton 0 @{term "\<forall>\<^bsub>pos\<^esub> (x :: int) . x < x + 1"}
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

lemma "\<forall>\<^bsub>pos\<^esub> (x :: int) . x = x + 0"
  apply (rule rev_impD[of _ "_ (_ _) (\<lambda>x. _ x x)"])
  apply (urule related_Fun_Rel_combI)
  apply (urule related_Fun_Rel_lambdaI)
  apply uassm
    apply (urule related_Fun_Rel_lambdaI)
     apply (urule related_Fun_Rel_combI)
      apply uassm
  sorry

  
  
  
  

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

end
