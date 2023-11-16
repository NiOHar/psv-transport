\<^marker>\<open>creator "Nils Harmsen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_Proof
  imports
    "Transport.Transport"
    "Transport.Binary_Relations_Surjective"
    "Transport.Binary_Relation_Properties"
    "ML_Unification.ML_Unification_HOL_Setup"
    "ML_Unification.Unify_Resolve_Tactics"
begin

paragraph \<open>Unification Hints\<close>

lemma eq_restrict_eq_eq_if_eq_top [uhint]: "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _) \<equiv> (=)"
  by simp

lemma right_unique_on_eq_right_unique_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> right_unique_on P \<equiv> (right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding right_unique_eq_right_unique_on by simp

lemma rel_injective_on_eq_rel_injective_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> rel_injective_on P \<equiv> (rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding rel_injective_eq_rel_injective_on by simp

lemma left_total_on_eq_left_total_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> left_total_on P \<equiv> (left_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding left_total_eq_left_total_on by simp

lemma rel_surjective_at_eq_left_total_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'b \<Rightarrow> bool) \<Longrightarrow> rel_surjective_at P \<equiv> (rel_surjective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding rel_surjective_eq_rel_surjective_at by simp


paragraph \<open>Basic Library\<close>

definition "rev_implies \<equiv> (\<longrightarrow>)\<inverse>"

bundle transport_rev_imp_syntax begin notation rev_implies (infixr "\<longleftarrow>" 25) end
bundle no_transport_rev_imp_syntax begin no_notation rev_implies (infixr "\<longleftarrow>" 25) end
unbundle transport_rev_imp_syntax

lemma rev_implies_eq_implies_inv [simp]: "(\<longleftarrow>) = (\<longrightarrow>)\<inverse>"
  unfolding rev_implies_def by simp

lemma rev_impI [intro]:
  assumes "Q \<Longrightarrow> P"
  shows "P \<longleftarrow> Q"
  using assms by auto

lemma rev_impD [dest]:
  assumes "P \<longleftarrow> Q"
  shows "Q \<Longrightarrow> P"
  using assms by auto


paragraph \<open>Relation Properties\<close>

definition "bi_unique_on \<equiv> right_unique_on \<sqinter> rel_injective_on"

lemma bi_unique_onI [intro]:
  assumes "right_unique_on P R"
  and "rel_injective_on P R"
  shows "bi_unique_on P R"
  unfolding bi_unique_on_def using assms by auto

lemma bi_unique_onE [elim]:
  assumes "bi_unique_on P R"
  obtains "right_unique_on P R" "rel_injective_on P R"
  using assms unfolding bi_unique_on_def by auto

definition "bi_unique \<equiv> bi_unique_on (\<top> :: 'a \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

(*TODO Kevin: use argument-free lemmas for all relational properties*)
lemma bi_unique_eq_bi_unique_on:
  "bi_unique = (bi_unique_on (\<top> :: 'a \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding bi_unique_def ..

lemma bi_unique_on_eq_bi_unique_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> bi_unique_on P \<equiv> (bi_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding bi_unique_eq_bi_unique_on by simp

lemma bi_uniqueI [intro]:
  assumes "right_unique R"
  and "rel_injective R"
  shows "bi_unique R"
  using assms by (urule bi_unique_onI)

lemma bi_uniqueE [elim]:
  assumes "bi_unique R"
  obtains "right_unique R" "rel_injective R"
  using assms by (urule (e) bi_unique_onE)

lemma Fun_Rel_imp_eq_restrict_if_bi_unique_on:
  assumes bi_unique: "bi_unique_on (P :: 'a \<Rightarrow> bool) (R ::'a \<Rightarrow> _)"
  and rel: "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI impI)
  fix a a' b b'
  assume "R a a'" "R b b'" "a =\<^bsub>P\<^esub> b"
  then have "R a b'" by auto
  with rel \<open>a =\<^bsub>P\<^esub> b\<close> have "Q b'" by auto
  moreover from bi_unique \<open>R a a'\<close> \<open>R a b'\<close> have "a' = b'" using \<open>a =\<^bsub>P\<^esub> b\<close>
    by (auto dest: right_unique_onD)
  ultimately show "a' =\<^bsub>Q\<^esub> b'" by blast
qed

lemma Fun_Rel_rev_imp_eq_restrict_if_bi_unique_on:
  assumes "bi_unique_on (P :: 'a \<Rightarrow> bool) (R ::'a \<Rightarrow> _)"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  sorry

corollary Fun_Rel_iff_eq_restrict_if_bi_unique_on:
  assumes bi_unique: "bi_unique_on (P :: 'a \<Rightarrow> bool) (R ::'a \<Rightarrow> _)"
  and rel: "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof -
  from rel have "(R \<Rrightarrow> (\<longrightarrow>)) P Q" "(R \<Rrightarrow> (\<longleftarrow>)) P Q" by auto
  with Fun_Rel_imp_eq_restrict_if_bi_unique_on Fun_Rel_rev_imp_eq_restrict_if_bi_unique_on
    have "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
    using bi_unique by auto
  then show ?thesis by blast
qed

corollary Fun_Rel_imp_eq_if_bi_unique:
  assumes "bi_unique (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_imp_eq_restrict_if_bi_unique_on) auto

corollary Fun_Rel_rev_imp_eq_if_bi_unique:
  assumes "bi_unique (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_rev_imp_eq_restrict_if_bi_unique_on) auto

corollary Fun_Rel_iff_eq_if_bi_unique:
  assumes "bi_unique (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_iff_eq_restrict_if_bi_unique_on) auto


definition "bi_total_on P Q \<equiv> left_total_on P \<sqinter> rel_surjective_at Q"

lemma bi_total_onI [intro]:
  assumes "left_total_on P R"
  and "rel_surjective_at Q R"
  shows "bi_total_on P Q R"
  unfolding bi_total_on_def using assms by auto

lemma bi_total_onE [elim]:
  assumes "bi_total_on P Q R"
  obtains "left_total_on P R" "rel_surjective_at Q R"
  using assms unfolding bi_total_on_def by auto

definition "bi_total \<equiv> bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

lemma bi_total_eq_bi_total_on:
  "bi_total = (bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding bi_total_def ..

lemma bi_total_on_eq_bi_total_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)" "Q \<equiv> (\<top> ::'b \<Rightarrow> bool)"
  shows "bi_total_on P Q \<equiv> (bi_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding bi_total_eq_bi_total_on using assms by simp

lemma bi_totalI [intro]:
  assumes "left_total R"
  and "rel_surjective R"
  shows "bi_total R"
  using assms by (urule bi_total_onI)

lemma bi_totalE [elim]:
  assumes "bi_total R"
  obtains "left_total R" "rel_surjective R"
  using assms by (urule (e) bi_total_onE)

theorem Fun_Rel_iff_all_restrict_if_bi_total_on:
  assumes "bi_total_on (P :: 'a \<Rightarrow> bool) (Q :: 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (\<lambda> p . (\<forall> x . P x \<longrightarrow> p x)) (\<lambda> q . (\<forall> x . Q x \<longrightarrow> q x))"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume reled: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(\<forall> x . P x \<longrightarrow> p x) \<longleftrightarrow> (\<forall> x . Q x \<longrightarrow> q x)" by fast
qed


theorem Fun_Rel_iff_all_if_bi_total: assumes "bi_total (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume reled: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(All p) \<longleftrightarrow> (All q)" sorry
qed

theorem bi_total_if_Fun_Rel_iff_all:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  shows "bi_total (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
using assms proof (intro bi_total_onI, goal_cases)
  case (1 y)
  then show ?case using assms Dep_Fun_Rel_rel_def in_codom_def sorry
next
  case (2 x)
  then show ?case sorry
qed

(*
theorem left_total_imp_Ex: assumes "(\<exists> x . (p x \<and> (\<exists> y . T x y))) \<and> (\<exists> y . (q y \<and> (\<exists> x . T x y)))"
  shows "((T \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume "(T \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(\<exists> x . p x) \<longleftrightarrow> (\<exists> x . q x)" apply (auto simp add: left_total_eq_left_total_on)
  qed
*)

end