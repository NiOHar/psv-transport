theory Transport_Proof
  imports "Transport.Transport" "Transport.Binary_Relations_Surjective" "Transport.Binary_Relation_Properties"
begin


definition "left_unique R \<equiv> \<forall> x x' y . R x y \<and> R x' y \<longrightarrow> x = x'"
definition "bi_unique R = (left_unique R \<and> injective R)"

theorem bi_unique_imp_rel_eq: "bi_unique T \<longrightarrow> (T \<Rrightarrow> T \<Rrightarrow> (=)) (=) (=)"
  sorry

definition "bi_total R = (left_total R & rel_surjective R)"

theorem bi_total_imp_rel_all: "bi_total T \<longrightarrow> ((A \<Rrightarrow> (=)) \<Rrightarrow> (=)) All All"
  sorry
end