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

lemma rel_injective_at_eq_rel_injective_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'b \<Rightarrow> bool) \<Longrightarrow> rel_injective_at P \<equiv> (rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding rel_injective_eq_rel_injective_at by simp

lemma rel_injective_on_eq_rel_injective_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> rel_injective_on P \<equiv> (rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding rel_injective_eq_rel_injective_on by simp

lemma right_unique_at_eq_right_unique_if_eq_top [uhint]:
  "Q \<equiv> (\<top> ::'b \<Rightarrow> bool) \<Longrightarrow> right_unique_at Q \<equiv> (right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding right_unique_eq_right_unique_at by simp

lemma right_unique_on_eq_right_unique_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> right_unique_on P \<equiv> (right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding right_unique_eq_right_unique_on by simp

lemma left_total_on_eq_left_total_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'a \<Rightarrow> bool) \<Longrightarrow> left_total_on P \<equiv> (left_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding left_total_eq_left_total_on by simp

lemma rel_surjective_at_eq_rel_surjective_if_eq_top [uhint]:
  "P \<equiv> (\<top> ::'b \<Rightarrow> bool) \<Longrightarrow> rel_surjective_at P \<equiv> (rel_surjective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding rel_surjective_eq_rel_surjective_at by simp


paragraph \<open>Basic Library\<close>

definition "rev_implies \<equiv> (\<longrightarrow>)\<inverse>"

bundle transport_rev_imp_syntax begin notation rev_implies (infixr "\<longleftarrow>" 25) end
bundle no_transport_rev_imp_syntax begin no_notation rev_implies (infixr "\<longleftarrow>" 25) end
unbundle transport_rev_imp_syntax

lemma rev_implies_eq_implies_inv [simp]: "(\<longleftarrow>) = (\<longrightarrow>)\<inverse>"
  unfolding rev_implies_def by simp

lemma rev_impI [intro!]:
  assumes "Q \<Longrightarrow> P"
  shows "P \<longleftarrow> Q"
  using assms by auto

lemma rev_impD [dest!]:
  assumes "P \<longleftarrow> Q"
  shows "Q \<Longrightarrow> P"
  using assms by auto

lemma rev_imp_iff_imp: "(P \<longleftarrow> Q) \<longleftrightarrow> (Q \<longrightarrow> P)" by auto


paragraph \<open>Relation Properties\<close>

lemma rel_injective_on_if_Fun_Rel_imp_if_rel_injective_at:
  assumes "rel_injective_at Q R"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "rel_injective_on P R"
  using assms by (intro rel_injective_onI) (auto dest: rel_injective_atD)

lemma rel_injective_at_if_Fun_Rel_rev_imp_if_rel_injective_on:
  assumes "rel_injective_on P R"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "rel_injective_at Q R"
  using assms by (intro rel_injective_atI) (auto dest: rel_injective_onD)

lemma right_unique_on_if_Fun_Rel_imp_if_right_unique_at:
  assumes "right_unique_at Q R"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) (auto dest: right_unique_atD)

lemma right_unique_at_if_Fun_Rel_rev_imp_if_right_unique_on:
  assumes "right_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "right_unique_at Q R"
  using assms by (intro right_unique_atI) (auto dest: right_unique_onD)


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

lemma bi_unique_on_rel_inv_if_Fun_Rel_iff_if_bi_unique_on:
  assumes "bi_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "bi_unique_on Q R\<inverse>"
  using assms by (intro bi_unique_onI
    rel_injective_on_if_Fun_Rel_imp_if_rel_injective_at
    right_unique_on_if_Fun_Rel_imp_if_right_unique_at)
  auto

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
  "(bi_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) =
  (bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
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


paragraph \<open>Equality\<close>

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_imp_eq_restrict_if_right_unique_onI:
  assumes runique: "right_unique_on P R"
  and rel: "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI impI)
  fix x x' y y'
  assume "R x y" "R x' y'" "x =\<^bsub>P\<^esub> x'"
  moreover with rel have "R x y'" "Q y'" by auto
  ultimately show "y =\<^bsub>Q\<^esub> y'" using runique by (auto dest: right_unique_onD)
qed

lemma Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI:
  assumes rinjective: "rel_injective_at Q R"
  and rel: "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI rev_impI)
  fix x x' y y'
  assume "R x y" "R x' y'" "y =\<^bsub>Q\<^esub> y'"
  moreover with rel have "R x y'" "P x" by auto
  ultimately show "x =\<^bsub>P\<^esub> x'" using rinjective by (auto dest: rel_injective_atD)
qed

corollary Fun_Rel_iff_eq_restrict_if_bi_unique_onI:
  assumes bi_unique: "bi_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof -
  from assms have "(R \<Rrightarrow> (\<longrightarrow>)) P Q" "(R \<Rrightarrow> (\<longleftarrow>)) P Q" "bi_unique_on Q R\<inverse>"
    using bi_unique_on_rel_inv_if_Fun_Rel_iff_if_bi_unique_on by auto
  with bi_unique Fun_Rel_imp_eq_restrict_if_right_unique_onI
    Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI
    have "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" by auto
  then show ?thesis by blast
qed

lemma right_unique_on_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=)"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) auto

lemma Fun_Rel_imp_if_Fun_Rel_imp_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) ((S :: 'b \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  using assms by (intro Dep_Fun_Rel_relI) blast

corollary Fun_Rel_imp_eq_restrict_iff_right_unique_on_and_Fun_Rel_imp:
  "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>) \<longleftrightarrow> (right_unique_on P R \<and> (R \<Rrightarrow> (\<longrightarrow>)) P Q)"
  using Fun_Rel_imp_eq_restrict_if_right_unique_onI
    right_unique_on_if_Fun_Rel_imp_eq_restrict Fun_Rel_imp_if_Fun_Rel_imp_restrict
  by blast

lemma rel_injective_at_if_Fun_Rel_rev_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=\<^bsub>Q\<^esub>)"
  shows "rel_injective_at Q R"
  using assms by (intro rel_injective_atI) auto

lemma Fun_Rel_rev_imp_if_Fun_Rel_rev_imp_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) ((S :: 'a \<Rightarrow> 'a \<Rightarrow> bool)\<restriction>\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  using assms by (intro Dep_Fun_Rel_relI rev_impI) auto

corollary Fun_Rel_rev_imp_eq_restrict_iff_rel_injective_at_and_Fun_Rel_rev_imp:
  "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>) \<longleftrightarrow> (rel_injective_at Q R \<and> (R \<Rrightarrow> (\<longleftarrow>)) P Q)"
  using Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI
    rel_injective_at_if_Fun_Rel_rev_imp_eq_restrict Fun_Rel_rev_imp_if_Fun_Rel_rev_imp_restrict
  by blast

lemma bi_unique_on_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "bi_unique_on P R"
  using assms by (intro bi_unique_onI) blast+

lemma Fun_Rel_iff_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  using assms by (intro Dep_Fun_Rel_relI) blast

corollary Fun_Rel_iff_eq_restrict_iff_bi_unique_on_and_Fun_Rel_iff:
  "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>) \<longleftrightarrow> (bi_unique_on P R \<and> (R \<Rrightarrow> (\<longleftrightarrow>)) P Q)"
  using Fun_Rel_iff_eq_restrict_if_bi_unique_onI
    bi_unique_on_if_Fun_Rel_iff_eq_restrict Fun_Rel_iff_if_Fun_Rel_iff_eq_restrict
  by blast

end

corollary Fun_Rel_imp_eq_if_right_unique:
  assumes "right_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_imp_eq_restrict_if_right_unique_onI) auto

corollary Fun_Rel_rev_imp_eq_if_rel_injective:
  assumes "rel_injective R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_atI) auto

corollary Fun_Rel_iff_eq_if_bi_unique:
  assumes "bi_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_iff_eq_restrict_if_bi_unique_onI) auto

corollary right_unique_if_Fun_Rel_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  shows "right_unique R"
  using assms by (urule right_unique_on_if_Fun_Rel_imp_eq_restrict)

corollary Fun_Rel_imp_eq_iff_right_unique: "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=) \<longleftrightarrow> right_unique R"
  using right_unique_if_Fun_Rel_imp_eq Fun_Rel_imp_eq_if_right_unique by blast

corollary rel_injective_if_Fun_Rel_rev_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  shows "rel_injective R"
  using assms by (urule rel_injective_at_if_Fun_Rel_rev_imp_eq_restrict)

corollary Fun_Rel_rev_imp_eq_iff_rel_injective: "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=) \<longleftrightarrow> rel_injective R"
  using rel_injective_if_Fun_Rel_rev_imp_eq Fun_Rel_rev_imp_eq_if_rel_injective by blast

corollary bi_unique_if_Fun_Rel_iff_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  shows "bi_unique R"
  using assms by (urule bi_unique_on_if_Fun_Rel_iff_eq_restrict)

corollary Fun_Rel_iff_eq_iff_bi_unique: "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=) \<longleftrightarrow> bi_unique R"
  using bi_unique_if_Fun_Rel_iff_eq Fun_Rel_iff_eq_if_bi_unique by blast


paragraph \<open>Universal Quantifier\<close>

definition "all_on P Q \<equiv> (\<forall>x. P x \<longrightarrow> Q x)"

bundle all_on_syntax begin
syntax
  "_all_on" :: "('a \<Rightarrow> bool) \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>(\<^bsub>_\<^esub>) _./ _)" [10, 10] 10)
notation all_on ("\<forall>(\<^bsub>_\<^esub>)")
end
bundle no_all_on_syntax begin
no_syntax
  "_all_on" :: "('a \<Rightarrow> bool) \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>(\<^bsub>_\<^esub>) _./ _)" [10, 10] 10)
no_notation all_on ("\<forall>(\<^bsub>_\<^esub>)")
end
unbundle all_on_syntax
translations
  "\<forall>\<^bsub>P\<^esub> x. Q" \<rightleftharpoons> "CONST all_on P (\<lambda>x. Q)"

lemma all_onI [intro!]:
  assumes "\<And>x. P x \<Longrightarrow> Q x"
  shows "\<forall>\<^bsub>P\<^esub> x. Q x"
  using assms unfolding all_on_def by blast

lemma all_onE [elim]:
  assumes "\<forall>\<^bsub>P\<^esub> x. Q x"
  obtains "\<And>x. P x \<Longrightarrow> Q x"
  using assms unfolding all_on_def by blast

lemma all_on_top_eq_all [simp]: "\<forall>\<^bsub>\<top>\<^esub> = All" by fastforce

lemma all_on_eq_all_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)"
  shows "\<forall>\<^bsub>P\<^esub> \<equiv> All"
  using assms by simp

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_restricts_imp_all_on_if_rel_surjective_atI:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) blast

lemma Fun_Rel_restricts_rev_imp_all_on_if_left_total_onI:
  assumes "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) blast

lemma Fun_Rel_restricts_iff_all_on_if_left_total_on_if_rel_surjective_at:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  and "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) blast

corollary Fun_Rel_restricts_iff_all_on_if_bi_total_on:
  assumes "bi_total_on P Q R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_restricts_iff_all_on_if_left_total_on_if_rel_surjective_at)
  force+

lemma rel_surjective_at_restrict_left_if_Fun_Rel_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
proof -
  let ?P2 = "\<lambda>y. \<exists>x. R x y \<and> P x"
  have "(R \<Rrightarrow> (\<longrightarrow>)) P ?P2" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. P x) \<longrightarrow> (\<forall>\<^bsub>Q\<^esub> y. ?P2 y)" by blast
  then show "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>" by fast
qed

lemma Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel:
  assumes "((O \<Rrightarrow> S) \<Rrightarrow> T) U V"
  and "O \<le> O'"
  shows "((O' \<Rrightarrow> S) \<Rrightarrow> T) U V"
proof -
  from assms have "(O' \<Rrightarrow> S) \<le> (O \<Rrightarrow> S)" by blast
  with assms antimonoD antimono_Dep_Fun_Rel_rel_left show ?thesis by blast
qed

corollary Fun_Rel_imp_all_on_iff_rel_surjective_at_restrict_left:
  "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub> \<longleftrightarrow> rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  by (blast intro: Fun_Rel_restricts_imp_all_on_if_rel_surjective_atI
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    rel_surjective_at_restrict_left_if_Fun_Rel_imp_all_on)

lemma left_total_on_restrict_right_if_Fun_Rel_rev_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
proof -
  let ?P1 = "\<lambda>x. \<exists>y. R x y \<and> Q y"
  have "(R \<Rrightarrow> (\<longleftarrow>)) ?P1 Q" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. ?P1 x) \<longleftarrow> (\<forall>\<^bsub>Q\<^esub> y. Q y)" by blast
  then show "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>" by fast
qed

corollary Fun_Rel_rev_imp_all_on_iff_left_total_on_restrict_right:
  "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub> \<longleftrightarrow> left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (blast intro: Fun_Rel_restricts_rev_imp_all_on_if_left_total_onI
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    left_total_on_restrict_right_if_Fun_Rel_rev_imp_all_on)

lemma bi_total_on_restricts_if_Fun_Rel_iff_if_bi_total_on:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "bi_total_on P Q R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  using assms by force

lemma bi_total_on_if_Fun_Rel_iff_all_on:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "bi_total_on P Q R"
proof (rule bi_total_onI)
  let ?P1 = "\<lambda>x. \<exists>y. R x y" and ?P2 = "\<lambda>_. True"
  have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. ?P1 x) \<longleftrightarrow> (\<forall>\<^bsub>Q\<^esub> y. ?P2 y)" by blast
  then show "left_total_on P R" by fast
next
  let ?P1 = "\<lambda>_. True" and ?P2 = "\<lambda>y. \<exists>x. R x y"
  have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. ?P1 x) \<longleftrightarrow> (\<forall>\<^bsub>Q\<^esub> y. ?P2 y)" by blast
  then show "rel_surjective_at Q R" by fast
qed

corollary Fun_Rel_iff_all_on_iff_bi_total_on_if_Fun_Rel_iff:
  assumes "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub> \<longleftrightarrow> bi_total_on P Q R"
  using assms by (blast intro: Fun_Rel_restricts_iff_all_on_if_bi_total_on
    Fun_Rel_Fun_Rel_if_le_left_if_Fun_Rel_Fun_Rel
    bi_total_on_restricts_if_Fun_Rel_iff_if_bi_total_on
    bi_total_on_if_Fun_Rel_iff_all_on)

end

corollary Fun_Rel_imp_all_if_rel_surjective:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All"
  using assms by (urule Fun_Rel_restricts_imp_all_on_if_rel_surjective_atI)

corollary Fun_Rel_rev_imp_all_if_left_total:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All"
  using assms by (urule Fun_Rel_restricts_rev_imp_all_on_if_left_total_onI)

corollary Fun_Rel_iff_all_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  using assms by (urule Fun_Rel_restricts_iff_all_on_if_bi_total_on)

corollary rel_surjective_if_Fun_Rel_imp_all:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All"
  shows "rel_surjective R"
  using assms by (urule rel_surjective_at_restrict_left_if_Fun_Rel_imp_all_on)

corollary Fun_Rel_imp_all_iff_rel_surjective:
  "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All \<longleftrightarrow> rel_surjective R"
  using rel_surjective_if_Fun_Rel_imp_all Fun_Rel_imp_all_if_rel_surjective by blast

corollary left_total_if_Fun_Rel_rev_imp_all:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All"
  shows "left_total R"
  using assms by (urule left_total_on_restrict_right_if_Fun_Rel_rev_imp_all_on)

corollary Fun_Rel_rev_imp_all_iff_left_total:
  "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All \<longleftrightarrow> left_total R"
  using left_total_if_Fun_Rel_rev_imp_all Fun_Rel_rev_imp_all_if_left_total by blast

corollary bi_total_if_Fun_Rel_iff_all:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  shows "bi_total R"
  using assms by (urule bi_total_on_if_Fun_Rel_iff_all_on)

corollary Fun_Rel_iff_all_iff_bi_total:
  "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All \<longleftrightarrow> bi_total R"
  using bi_total_if_Fun_Rel_iff_all Fun_Rel_iff_all_if_bi_total by blast


paragraph \<open>Existential Quantifier\<close>

definition "ex_on P Q \<equiv> \<exists>x. P x \<and> Q x"

bundle ex_on_syntax begin
syntax
  "_ex_on" :: "('a \<Rightarrow> bool) \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>(\<^bsub>_\<^esub>) _./ _)" [10, 10] 10)
notation ex_on ("\<exists>(\<^bsub>_\<^esub>)")
end
bundle no_ex_on_syntax begin
no_syntax
  "_ex_on" :: "('a \<Rightarrow> bool) \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>(\<^bsub>_\<^esub>) _./ _)" [10, 10] 10)
no_notation ex_on ("\<exists>(\<^bsub>_\<^esub>)")
end
unbundle ex_on_syntax
translations
  "\<exists>\<^bsub>P\<^esub> x. Q" \<rightleftharpoons> "CONST ex_on P (\<lambda>x. Q)"

lemma ex_onI [intro!]:
  assumes "\<exists>x. (P x \<and> Q x)"
  shows "\<exists>\<^bsub>P\<^esub> x. Q x"
  using assms unfolding ex_on_def by blast

lemma ex_onE [elim]:
  assumes "\<exists>\<^bsub>P\<^esub> x. Q x"
  obtains x where "P x" "Q x"
  using assms unfolding ex_on_def by blast

lemma ex_on_top_eq_ex [simp]: "\<exists>\<^bsub>\<top>\<^esub> = Ex" by fastforce

lemma ex_on_eq_ex_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)"
  shows "\<exists>\<^bsub>P\<^esub> \<equiv> Ex"
  using assms by simp

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_restricts_imp_ex_on_if_left_total_onI:
  assumes "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma Fun_Rel_restricts_rev_imp_ex_on_if_rel_surjective_at:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma Fun_Rel_restricts_iff_ex_on_if_left_total_on_if_rel_surjective_at:
  assumes "rel_surjective_at Q R\<restriction>\<^bsub>P\<^esub>"
  and "left_total_on P R\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) fast

corollary Fun_Rel_restricts_iff_ex_on_if_bi_total_on:
  assumes "bi_total_on P Q R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  shows "((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
  using assms by (intro Fun_Rel_restricts_iff_ex_on_if_left_total_on_if_rel_surjective_at)
  fast+

text \<open>Note: the reverse directions do not hold.\<close>

lemma ex_Fun_Rel_imp_ex_on_and_not_left_total_on:
  assumes "(a = (x::'a) \<or> a = y \<or> a = z) \<and> x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z"
  shows "(\<exists>R :: 'a \<Rightarrow> 'a \<Rightarrow> bool. \<exists>P :: 'a \<Rightarrow> bool. \<exists>Q :: 'a \<Rightarrow> bool.
  ((R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub> \<and> \<not>(left_total_on P R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>))"
proof -
  (*TODO Nils: prove this counterexample (you can concretise the types above to, say, bool*)
  let ?R = "\<lambda> (a::'a) (b::'a) . (a = x \<and> b = x)"
  let ?P = "\<lambda> (a::'a) . True"
  let ?Q = "\<lambda> (a::'a) . True"
  have 1: "((?R\<restriction>\<^bsub>?P\<^esub>\<upharpoonleft>\<^bsub>?Q\<^esub>  \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>?P\<^esub> \<exists>\<^bsub>?Q\<^esub>" apply (intro Dep_Fun_Rel_relI, elim Dep_Fun_Rel_relE) apply auto sorry
  have "(\<nexists> b .(?P y) \<and> (y = x \<and> b = x) \<and> (?Q b)) " using assms by auto
  then have "\<not>(left_total_on ?P ?R\<restriction>\<^bsub>?P\<^esub>\<upharpoonleft>\<^bsub>?Q\<^esub>)" by auto
  with 1 show ?thesis by blast
qed

end

corollary Fun_Rel_imp_ex_if_left_total:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_restricts_imp_ex_on_if_left_total_onI)

corollary Fun_Rel_rev_imp_ex_if_rel_surjective:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_restricts_rev_imp_ex_on_if_rel_surjective_at)

corollary Fun_Rel_iff_ex_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_restricts_iff_ex_on_if_bi_total_on)


(*TODO Kevin: review ex1_on later (it's a compound concept, so in principle,
we should derive it from ex_on, eq_on, and conjunction*)
definition "ex1_on P p \<equiv> (\<exists>!x. P x \<and> p x)"

lemma ex_on1I [intro]:
  assumes "\<exists>!x. (P x \<and> Q x)"
  shows "ex1_on P Q"
  using assms unfolding ex1_on_def by blast

lemma ex_on1E[elim]: assumes "ex1_on P Q" obtains "\<exists>!x. (P x \<and> Q x)"
  using assms unfolding ex1_on_def by blast

lemma ex_on1_top_eq_ex1[simp]: "ex1_on \<top> = Ex1" by fastforce

lemma ex_on1_eq_ex1_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)"
  shows "ex1_on P \<equiv> Ex1"
  using assms by simp

lemma left_total_imp_Ex1_on_imp: assumes "bi_total_on P Q R" "right_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) (ex1_on P) (ex1_on Q)"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(ex1_on P p) \<longrightarrow> (ex1_on Q q)" proof
    assume "ex1_on P p"
    then obtain x where "P x" "p x" "(\<forall> x' . (P x' \<and> p x') \<longrightarrow> x' = x)" by blast
    then obtain y where "R x y" using \<open>bi_total_on P Q R\<close> by blast
    then have "Q y \<and> q y" using as assms \<open>P x\<close> \<open>p x\<close> by blast
    have "(\<forall>y'. q y' \<and> Q y' \<longrightarrow> y' = y)"
    proof (intro allI impI)
      fix y'
      assume "q y' \<and> Q y'"
      then have "Q y'" by blast
      then obtain x' where "R x' y'" using assms by blast
      from this \<open>q y' \<and> Q y'\<close> as assms(3) have "p x' \<and> P x'" by blast
      from this \<open>\<forall> x' . (P x' \<and> p x') \<longrightarrow> x' = x\<close> \<open>P x\<close> \<open>p x\<close> have "x' = x" by blast
      from this \<open>right_unique_on P R\<close> \<open>P x\<close> \<open>R x' y'\<close> \<open>R x y\<close> \<open>Q y'\<close> \<open>Q y \<and> q y\<close> have "y = y'" by (auto dest: right_unique_onD)
      then show "y' = y" by blast
    qed
    with \<open>Q y \<and> q y\<close> show "ex1_on Q q"  by blast
  qed
qed

lemma surjective_imp_Ex1_on_revimp: assumes "bi_total_on P Q R" "rel_injective_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftarrow>)) (ex1_on (P::'a \<Rightarrow> bool)) (ex1_on (Q::'b \<Rightarrow> bool))"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(ex1_on P p) \<longleftarrow> (ex1_on Q q)"
  proof (rule rev_impI)
    assume "ex1_on Q q"
    then obtain y where "Q y" "q y" "(\<forall> y' . (Q y' \<and> q y') \<longrightarrow> y' = y)" by blast
    then obtain x where "R x y" using \<open>bi_total_on P Q R\<close> by blast
    then have "P x \<and> p x" using as assms \<open>Q y\<close> \<open>q y\<close> by blast
    have "(\<forall>x'. p x' \<and> P x' \<longrightarrow> x' = x)"
    proof (intro allI impI)
      fix x'
      assume "p x' \<and> P x'"
      then obtain y' where "R x' y'" using assms by blast
      from this \<open>p x' \<and> P x'\<close> as assms(3) have "q y' \<and> Q y'" by blast
      from this  \<open>\<forall> y' . (Q y' \<and> q y') \<longrightarrow> y' = y\<close> \<open>Q y\<close> \<open>q y\<close> have "y' = y" by blast
      from this \<open>rel_injective_on P R\<close> \<open>R x' y'\<close> \<open>R x y\<close> \<open>p x' \<and> P x'\<close> \<open>P x \<and> p x\<close> have "x = x'" by (auto dest: rel_injective_onD)
      then show "x' = x" by blast
    qed
    with \<open>P x \<and> p x\<close> show "ex1_on P p"  by blast
  qed
qed


corollary bi_total_imp_Ex1_on_iff: assumes "bi_total_on P Q R" "bi_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (ex1_on P) (ex1_on Q)"
  using assms apply (intro Dep_Fun_Rel_relI) apply (elim bi_total_onE bi_unique_onE) apply (intro iffI)
  using left_total_imp_Ex1_on_imp[of P Q R] surjective_imp_Ex1_on_revimp[of P Q R] by auto
(* reverse does not hold *)

lemma left_total_imp_Ex1_imp: assumes "bi_total R" "right_unique R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex1 Ex1"
using assms by (urule left_total_imp_Ex1_on_imp) auto

lemma surjective_imp_Ex1_revimp: assumes "bi_total R" "rel_injective R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex1 Ex1"
using assms by (urule surjective_imp_Ex1_on_revimp) auto


corollary bi_total_imp_Ex1_iff: assumes "bi_total R" "bi_unique R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex1 Ex1"
  using assms by (urule bi_total_imp_Ex1_on_iff) auto
(* reverse does not hold *)


context galois
begin

paragraph \<open>Right-Uniqueness\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma right_unique_at_left_Galois_if_right_unique_at_rightI:
  assumes "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "right_unique_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (auto dest: right_unique_atD)

lemma right_unique_at_right_if_right_unique_at_left_GaloisI:
  assumes "right_unique_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (blast dest: right_unique_atD)

corollary right_unique_at_left_Galois_iff_right_unique_at_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_at Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms right_unique_at_left_Galois_if_right_unique_at_rightI
    right_unique_at_right_if_right_unique_at_left_GaloisI
  by blast

corollary right_unique_on_left_Galois_if_right_unique_at_rightI:
  assumes "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "right_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro right_unique_on_if_Fun_Rel_imp_if_right_unique_at)
  (blast intro: right_unique_at_left_Galois_if_right_unique_at_rightI)

corollary right_unique_at_right_if_right_unique_on_left_GaloisI:
  assumes "right_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) P Q"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro right_unique_at_right_if_right_unique_at_left_GaloisI
    right_unique_at_if_Fun_Rel_rev_imp_if_right_unique_on)

corollary right_unique_on_left_Galois_iff_right_unique_at_rightI:
  assumes "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms right_unique_on_left_Galois_if_right_unique_at_rightI
    right_unique_at_right_if_right_unique_on_left_GaloisI
  by blast

end

corollary right_unique_left_Galois_if_right_unique_rightI:
  assumes "right_unique (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "right_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule right_unique_at_left_Galois_if_right_unique_at_rightI)

corollary right_unique_right_if_right_unique_left_GaloisI:
  assumes "right_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule right_unique_at_right_if_right_unique_at_left_GaloisI)

corollary right_unique_left_Galois_iff_right_unique_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "right_unique (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms right_unique_left_Galois_if_right_unique_rightI
    right_unique_right_if_right_unique_left_GaloisI
  by blast


paragraph \<open>Injectivity\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma injective_on_left_Galois_if_rel_injective_on_left:
  assumes "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  shows "rel_injective_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (auto dest: rel_injective_onD)

lemma rel_injective_on_left_if_injective_on_left_GaloisI:
  assumes "rel_injective_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro rel_injective_onI) (blast dest!: rel_injective_onD)

corollary injective_on_left_Galois_iff_rel_injective_on_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms injective_on_left_Galois_if_rel_injective_on_left
    rel_injective_on_left_if_injective_on_left_GaloisI
  by blast

corollary injective_at_left_Galois_if_rel_injective_on_leftI:
  assumes "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "rel_injective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro rel_injective_at_if_Fun_Rel_rev_imp_if_rel_injective_on)
  (blast intro: injective_on_left_Galois_if_rel_injective_on_left)

corollary rel_injective_on_left_if_injective_at_left_GaloisI:
  assumes "rel_injective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro rel_injective_on_left_if_injective_on_left_GaloisI
    rel_injective_on_if_Fun_Rel_imp_if_rel_injective_at)

corollary injective_at_left_Galois_iff_rel_injective_on_leftI:
  assumes "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_at Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  using assms injective_at_left_Galois_if_rel_injective_on_leftI
    rel_injective_on_left_if_injective_at_left_GaloisI
  by blast

end

corollary injective_left_Galois_if_rel_injective_left:
  assumes "rel_injective (\<le>\<^bsub>L\<^esub>)"
  shows "rel_injective (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule injective_on_left_Galois_if_rel_injective_on_left)

corollary rel_injective_left_if_injective_left_GaloisI:
  assumes "rel_injective (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows  "rel_injective (\<le>\<^bsub>L\<^esub>)"
  using assms by (urule rel_injective_on_left_if_injective_on_left_GaloisI)

corollary rel_injective_left_Galois_iff_rel_injective_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective (\<le>\<^bsub>L\<^esub>)"
  using assms injective_left_Galois_if_rel_injective_left
    rel_injective_left_if_injective_left_GaloisI
  by blast


paragraph \<open>Bi-Uniqueness\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

corollary bi_unique_on_left_Galois_if_right_unique_at_right_if_rel_injective_on_leftI:
  assumes "rel_injective_on P (\<le>\<^bsub>L\<^esub>)"
  and "right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms
  by (intro bi_unique_onI right_unique_on_left_Galois_if_right_unique_at_rightI
    injective_on_left_Galois_if_rel_injective_on_left)

corollary rel_injective_on_left_and_right_unique_at_right_if_bi_unique_on_left_GaloisI:
  assumes "bi_unique_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective_on P (\<le>\<^bsub>L\<^esub>) \<and> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro conjI rel_injective_on_left_if_injective_on_left_GaloisI
    right_unique_at_right_if_right_unique_on_left_GaloisI)
  auto

corollary bi_unique_on_left_Galois_iff_rel_injective_on_left_and_right_unique_at_rightI:
  assumes "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  and "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective_on P (\<le>\<^bsub>L\<^esub>) \<and> right_unique_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms bi_unique_on_left_Galois_if_right_unique_at_right_if_rel_injective_on_leftI
    rel_injective_on_left_and_right_unique_at_right_if_bi_unique_on_left_GaloisI
  by blast

end

corollary bi_unique_left_Galois_if_right_unique_right_if_rel_injective_leftI:
  assumes "rel_injective (\<le>\<^bsub>L\<^esub>)"
  and "right_unique (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule bi_unique_on_left_Galois_if_right_unique_at_right_if_rel_injective_on_leftI
    where chained = insert)
  (uassm+, auto)

corollary rel_injective_left_and_right_unique_right_if_bi_unique_left_GaloisI:
  assumes "bi_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "rel_injective (\<le>\<^bsub>L\<^esub>) \<and> right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule rel_injective_on_left_and_right_unique_at_right_if_bi_unique_on_left_GaloisI
    where chained = insert)
  (uassm+, auto)

corollary bi_unique_left_Galois_iff_rel_injective_left_and_right_unique_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_unique (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_injective (\<le>\<^bsub>L\<^esub>) \<and> right_unique (\<le>\<^bsub>R\<^esub>)"
  using assms bi_unique_left_Galois_if_right_unique_right_if_rel_injective_leftI
    rel_injective_left_and_right_unique_right_if_bi_unique_left_GaloisI
  by blast


paragraph \<open>Surjectivity\<close>

context
  fixes Q :: "'b \<Rightarrow> bool"
begin

lemma surjective_at_left_Galois_if_rel_surjective_at_rightI:
  assumes "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro rel_surjective_atI) fast

lemma rel_surjective_at_right_if_surjective_at_left_Galois:
  assumes "rel_surjective_at Q (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro rel_surjective_atI) (auto)

corollary rel_surjective_at_right_iff_surjective_at_left_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective_at Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms surjective_at_left_Galois_if_rel_surjective_at_rightI
    rel_surjective_at_right_if_surjective_at_left_Galois
  by blast

end

corollary surjective_left_Galois_if_rel_surjective_rightI:
  assumes "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule surjective_at_left_Galois_if_rel_surjective_at_rightI)

corollary rel_surjective_right_if_surjective_left_Galois:
  assumes "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule rel_surjective_at_right_if_surjective_at_left_Galois)

corollary rel_surjective_right_iff_surjective_left_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms surjective_left_Galois_if_rel_surjective_rightI
    rel_surjective_right_if_surjective_left_Galois
  by blast


paragraph \<open>Left-Totality\<close>

context
  fixes P :: "'a \<Rightarrow> bool"
begin

lemma left_total_on_left_Galois_if_left_total_on_leftI:
  assumes leftt: "left_total_on P (\<le>\<^bsub>L\<^esub>)"
  and mono: "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and gal_prop: "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
shows "left_total_on P (\<^bsub>L\<^esub>\<lessapprox>)"
proof (rule left_total_onI)
  fix x
  assume "P x"
  with leftt obtain x' where "x \<le>\<^bsub>L\<^esub> x'" by (elim left_total_onE)
  with mono gal_prop have "x \<^bsub>L\<^esub>\<lessapprox> l x'" by (intro left_Galois_left_if_left_relI)
  then show "in_dom (\<^bsub>L\<^esub>\<lessapprox>) x" by blast
qed

lemma left_total_on_left_if_left_total_on_left_GaloisI:
  assumes "left_total_on P (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "left_total_on P (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro left_total_onI) (auto)

corollary left_total_on_left_Galois_iff_left_total_on_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total_on P (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total_on P (\<le>\<^bsub>L\<^esub>)"
  using assms left_total_on_left_Galois_if_left_total_on_leftI
    left_total_on_left_if_left_total_on_left_GaloisI
  by blast

end

corollary left_total_left_Galois_if_left_total_leftI:
  assumes "left_total (\<le>\<^bsub>L\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule left_total_on_left_Galois_if_left_total_on_leftI)

corollary left_total_left_if_left_total_left_Galois:
  assumes "left_total (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "left_total (\<le>\<^bsub>L\<^esub>)"
  using assms by (urule left_total_on_left_if_left_total_on_left_GaloisI)

corollary left_total_left_Galois_iff_left_total_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total (\<le>\<^bsub>L\<^esub>)"
  using assms left_total_left_Galois_if_left_total_leftI
    left_total_left_if_left_total_left_Galois
  by blast


paragraph \<open>Bi-Totality\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma bi_total_on_left_GaloisI:
  assumes "left_total_on P (\<le>\<^bsub>L\<^esub>)"
  and "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total_on P Q (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms surjective_at_left_Galois_if_rel_surjective_at_rightI
    left_total_on_left_Galois_if_left_total_on_leftI
  by blast

lemma left_total_on_left_rel_surjective_at_right_if_bi_total_on_left_GaloisE:
  assumes "bi_total_on P Q (\<^bsub>L\<^esub>\<lessapprox>)"
  obtains "left_total_on P (\<le>\<^bsub>L\<^esub>)" "rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms rel_surjective_at_right_if_surjective_at_left_Galois
    left_total_on_left_if_left_total_on_left_GaloisI
  by auto

corollary bi_total_on_left_Galois_iff_left_total_on_left_and_rel_surjective_on_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total_on P Q (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total_on P (\<le>\<^bsub>L\<^esub>) \<and> rel_surjective_at Q (\<le>\<^bsub>R\<^esub>)"
  using assms bi_total_on_left_GaloisI
    left_total_on_left_rel_surjective_at_right_if_bi_total_on_left_GaloisE
  by blast

end

corollary bi_total_left_GaloisI:
  assumes "left_total (\<le>\<^bsub>L\<^esub>)"
  and "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (urule bi_total_on_left_GaloisI)

corollary left_total_left_rel_surjective_right_if_bi_total_left_GaloisE:
  assumes "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  obtains "left_total (\<le>\<^bsub>L\<^esub>)" "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms by (urule (e) left_total_on_left_rel_surjective_at_right_if_bi_total_on_left_GaloisE)

corollary bi_total_left_Galois_iff_left_total_left_and_rel_surjective_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total (\<^bsub>L\<^esub>\<lessapprox>) \<longleftrightarrow> left_total (\<le>\<^bsub>L\<^esub>) \<and> rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms bi_total_left_GaloisI
    left_total_left_rel_surjective_right_if_bi_total_left_GaloisE
  by blast

end


context galois
begin

lemma Fun_Rel_imp_bi_relatedI:
  assumes monol: "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and half_gal: "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and perR: "partial_equivalence_rel (\<le>\<^bsub>R\<^esub>)"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) (\<equiv>\<^bsub>L\<^esub>)  (\<equiv>\<^bsub>R\<^esub>)"
proof (intro Dep_Fun_Rel_relI impI)
  fix x y x' y'
  assume lassms: "x \<^bsub>L\<^esub>\<lessapprox> y" "x' \<^bsub>L\<^esub>\<lessapprox> y'" "x \<equiv>\<^bsub>L\<^esub> x'"
  show "y \<equiv>\<^bsub>R\<^esub> y'"
  proof (intro bi_relatedI)
    from lassms half_gal have "l x' \<le>\<^bsub>R\<^esub> y'" by auto
    with \<open>x \<equiv>\<^bsub>L\<^esub> x'\<close> monol perR have "l x \<le>\<^bsub>R\<^esub> y'" by blast
    with \<open>x \<^bsub>L\<^esub>\<lessapprox> y\<close> half_gal perR have "y \<le>\<^bsub>R\<^esub> l x" by (blast dest: symmetricD)
    with perR \<open>l x \<le>\<^bsub>R\<^esub> y'\<close> show "y \<le>\<^bsub>R\<^esub> y'" by blast
    from lassms half_gal have "l x \<le>\<^bsub>R\<^esub> y" by blast
    with \<open>x \<equiv>\<^bsub>L\<^esub> x'\<close> monol perR have "l x' \<le>\<^bsub>R\<^esub> y" by blast
    with \<open>x' \<^bsub>L\<^esub>\<lessapprox> y'\<close> half_gal perR have "y' \<le>\<^bsub>R\<^esub> l x'" by (blast dest: symmetricD)
    with perR \<open>l x' \<le>\<^bsub>R\<^esub> y\<close> show "y' \<le>\<^bsub>R\<^esub> y" by auto
  qed
qed

lemma Fun_Rel_rev_imp_bi_relatedI:
  assumes monor: "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and perL: "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftarrow>)) (\<equiv>\<^bsub>L\<^esub>)  (\<equiv>\<^bsub>R\<^esub>)"
proof (intro Dep_Fun_Rel_relI rev_impI)
  fix x y x' y'
  assume "x \<^bsub>L\<^esub>\<lessapprox> y" and "x' \<^bsub>L\<^esub>\<lessapprox> y'" and "y \<equiv>\<^bsub>R\<^esub> y'"
  then show "x \<equiv>\<^bsub>L\<^esub> x'" proof (intro bi_relatedI, goal_cases)
    case 1
    with monor perL have "x \<le>\<^bsub>L\<^esub> r y'" by fastforce
    with  \<open>x' \<^bsub>L\<^esub>\<lessapprox> y'\<close>  have "x' \<le>\<^bsub>L\<^esub> r y'" by auto
    with perL \<open>x \<le>\<^bsub>L\<^esub> r y'\<close> show ?case by (blast dest: symmetricD)
  next
    case 2
    with monor perL have "x' \<le>\<^bsub>L\<^esub> r y" by blast
    with  \<open>x \<^bsub>L\<^esub>\<lessapprox> y\<close>  have "x \<le>\<^bsub>L\<^esub> r y" by auto
    with perL \<open>x' \<le>\<^bsub>L\<^esub> r y\<close> show ?case by (blast dest: symmetricD)
  qed
qed

corollary Fun_Rel_iff_bi_relatedI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>R\<^esub>)"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longleftrightarrow>)) (\<equiv>\<^bsub>L\<^esub>)  (\<equiv>\<^bsub>R\<^esub>)"
  using assms Fun_Rel_imp_bi_relatedI Fun_Rel_rev_imp_bi_relatedI by (auto 8 0)

(*TODO: we should derive specialised theorems for the Galois relator that are in simplified form.*)
(*TODO: for the Galois relator, many assumptions needed for the parametricity theorems of the
logical connectives become vacous. Example:*)

print_statement Fun_Rel_imp_eq_restrict_if_right_unique_onI
  [of "in_field (\<le>\<^bsub>L\<^esub>)" "(\<^bsub>L\<^esub>\<lessapprox>)" "in_field (\<le>\<^bsub>R\<^esub>)"]

lemma "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) (in_field (\<le>\<^bsub>L\<^esub>)) (in_field (\<le>\<^bsub>R\<^esub>))"
  by (intro Dep_Fun_Rel_relI) auto

end

end
