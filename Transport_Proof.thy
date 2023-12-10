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

lemma Fun_Rel_rev_imp_eq_restrict_if_rel_injective_onI:
  assumes rinjective: "rel_injective_on P R"
  and rel: "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI rev_impI)
  fix x x' y y'
  assume "R x y" "R x' y'" "y =\<^bsub>Q\<^esub> y'"
  moreover with rel have "R x y'" "P x" "P x'" by auto
  ultimately show "x =\<^bsub>P\<^esub> x'" using rinjective by (auto dest: rel_injective_onD)
qed

corollary Fun_Rel_iff_eq_restrict_if_bi_unique_onI:
  assumes bi_unique: "bi_unique_on P R"
  and rel: "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof -
  from rel have "(R \<Rrightarrow> (\<longrightarrow>)) P Q" "(R \<Rrightarrow> (\<longleftarrow>)) P Q" by auto
  with Fun_Rel_imp_eq_restrict_if_right_unique_onI Fun_Rel_rev_imp_eq_restrict_if_rel_injective_onI
    have "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
    using bi_unique by auto
  then show ?thesis by blast
qed

lemma right_unique_on_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) auto

lemma Fun_Rel_imp_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  using assms by (intro Dep_Fun_Rel_relI) blast

lemma rel_injective_on_if_Fun_Rel_rev_imp_eq_restrictI:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "rel_injective_on P R"
  using assms by (intro rel_injective_onI) blast

lemma Fun_Rel_rev_imp_if_Fun_Rel_rev_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  using assms by (intro Dep_Fun_Rel_relI) auto

lemma bi_unique_on_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "bi_unique_on P R"
  using assms by (intro bi_unique_onI
    right_unique_on_if_Fun_Rel_imp_eq_restrict
    rel_injective_on_if_Fun_Rel_rev_imp_eq_restrictI)
  blast+

lemma Fun_Rel_iff_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  using assms by (intro Dep_Fun_Rel_relI) blast

end

corollary Fun_Rel_imp_eq_if_right_unique:
  assumes "right_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_imp_eq_restrict_if_right_unique_onI) auto

corollary Fun_Rel_rev_imp_eq_if_rel_inective:
  assumes "rel_injective R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_onI) auto

corollary Fun_Rel_iff_eq_if_bi_unique:
  assumes "bi_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_iff_eq_restrict_if_bi_unique_onI) auto

corollary right_unique_if_Fun_Rel_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  shows "right_unique R"
  using assms by (urule right_unique_on_if_Fun_Rel_imp_eq_restrict)

corollary rel_injective_if_Fun_Rel_rev_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  shows "rel_injective R"
  using assms by (urule rel_injective_on_if_Fun_Rel_rev_imp_eq_restrictI) auto

corollary bi_unique_if_Fun_Rel_iff_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  shows "bi_unique R"
  using assms by (urule bi_unique_on_if_Fun_Rel_iff_eq_restrict)


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

lemma Fun_Rel_imp_all_on_if_rel_surjective_atI:
  assumes "rel_surjective_at Q R"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma Fun_Rel_rev_imp_all_on_if_left_total_onI:
  assumes "left_total_on P R"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma Fun_Rel_iff_all_on_if_bi_total_onI:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma ex_rel_dom_pred_if_Fun_Rel_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "\<And>y. Q y \<Longrightarrow> \<exists>x. R x y \<and> P x"
proof -
  let ?P2 = "\<lambda>y. \<exists>x. R x y \<and> P x"
  have "(R \<Rrightarrow> (\<longrightarrow>)) P ?P2" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. P x) \<longrightarrow> (\<forall>\<^bsub>Q\<^esub> y. ?P2 y)" by blast
  then show "Q y \<Longrightarrow> \<exists>x. R x y \<and> P x" for y by blast
qed

corollary rel_surjective_at_if_Fun_Rel_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "rel_surjective_at Q R"
  using assms ex_rel_dom_pred_if_Fun_Rel_imp_all_on by force

lemma ex_rel_codom_pred_if_Fun_Rel_rev_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "\<And>x. P x \<Longrightarrow> \<exists>y. R x y \<and> Q y"
proof -
  let ?P1 = "\<lambda>x. \<exists>y. R x y \<and> Q y"
  have "(R \<Rrightarrow> (\<longleftarrow>)) ?P1 Q" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. ?P1 x) \<longleftarrow> (\<forall>\<^bsub>Q\<^esub> y. Q y)" by blast
  then show "P x \<Longrightarrow> \<exists>y. R x y \<and> Q y" for x by blast
qed

corollary left_total_on_if_Fun_Rel_rev_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "left_total_on P R"
  using assms ex_rel_codom_pred_if_Fun_Rel_rev_imp_all_on by force

lemma bi_total_on_if_Fun_Rel_imp_all_on:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<forall>\<^bsub>P\<^esub> \<forall>\<^bsub>Q\<^esub>"
  shows "bi_total_on P Q R"
proof (intro bi_total_onI rel_surjective_atI left_total_onI)
  let ?P1 = "\<lambda>x. \<exists>y. R x y" and ?P2 = "\<lambda>_. True"
  have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. ?P1 x) \<longleftrightarrow> (\<forall>\<^bsub>Q\<^esub> y. ?P2 y)" by blast
  then show "P x \<Longrightarrow> in_dom R x" for x by auto
next
  let ?P1 = "\<lambda>_. True" and ?P2 = "\<lambda>y. \<exists>x. R x y"
  have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
  with assms have "(\<forall>\<^bsub>P\<^esub> x. ?P1 x) \<longleftrightarrow> (\<forall>\<^bsub>Q\<^esub> y. ?P2 y)" by blast
  then show "Q y \<Longrightarrow> in_codom R y" for y by auto
qed

end

corollary Fun_Rel_imp_all_if_rel_surjective:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All"
  using assms by (urule Fun_Rel_imp_all_on_if_rel_surjective_atI) auto

corollary Fun_Rel_rev_imp_all_if_left_total:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All"
  using assms by (urule Fun_Rel_rev_imp_all_on_if_left_total_onI) auto

corollary Fun_Rel_iff_all_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  using assms by (urule Fun_Rel_iff_all_on_if_bi_total_onI) auto

corollary rel_surjective_if_Fun_Rel_imp_all:
  assumes "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) All All"
  shows "rel_surjective R"
  using assms by (urule rel_surjective_at_if_Fun_Rel_imp_all_on)

corollary left_total_if_Fun_Rel_rev_imp_all:
  assumes "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) All All"
  shows "left_total R"
  using assms by (urule left_total_on_if_Fun_Rel_rev_imp_all_on)

corollary bi_total_if_Fun_Rel_iff_all:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  shows "bi_total R"
  using assms by (urule bi_total_on_if_Fun_Rel_imp_all_on)


paragraph \<open>Existential Quantifier\<close>

definition "ex_on P p \<equiv> (\<exists>x. P x \<and> p x)"

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

lemma ex_onI [intro]:
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

lemma Fun_Rel_imp_ex_on_if_left_total_onI:
  assumes left_total: "left_total_on P R"
  and rel: "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
proof (intro Dep_Fun_Rel_relI impI)
  fix P' Q'
  assume rel': "(R \<Rrightarrow> (\<longrightarrow>)) P' Q'" and "\<exists>\<^bsub>P\<^esub> x. P' x"
  then obtain x where "P x" "P' x" by blast+
  moreover with left_total obtain y where "R x y" by auto
  ultimately have "Q y" "Q' y" using rel rel' by blast+
  then show "\<exists>\<^bsub>Q\<^esub> y. Q' y" by blast
qed

lemma Fun_Rel_rev_imp_ex_on_if_rel_surjective_atI:
  assumes surj: "rel_surjective_at Q R"
  and rel: "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
proof (intro Dep_Fun_Rel_relI rev_impI)
  fix P' Q' assume rel': "(R \<Rrightarrow> (\<longleftarrow>)) P' Q'" and "\<exists>\<^bsub>Q\<^esub> y. Q' y"
  then obtain y where "Q y" "Q' y" by blast+
  moreover with surj obtain x where "R x y" by (auto elim: rel_surjectiveE)
  ultimately have "P x" "P' x" using rel rel' by blast+
  then show "\<exists>\<^bsub>P\<^esub> x. P' x" by blast
qed

corollary Fun_Rel_iff_ex_on_if_bi_total_onI:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) \<exists>\<^bsub>P\<^esub> \<exists>\<^bsub>Q\<^esub>"
proof (intro Dep_Fun_Rel_relI iffI)
  fix P' Q' assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) P' Q'"
  then show "\<exists>\<^bsub>P\<^esub> x. P' x \<Longrightarrow> \<exists>\<^bsub>Q\<^esub> y. Q' y" using Fun_Rel_imp_ex_on_if_left_total_onI assms by blast
  show "\<exists>\<^bsub>Q\<^esub> y. Q' y \<Longrightarrow> \<exists>\<^bsub>P\<^esub> x. P' x"
    using as Fun_Rel_rev_imp_ex_on_if_rel_surjective_atI assms by blast
qed
(* reverse does not hold *)

end

lemma Fun_Rel_imp_ex_if_left_total:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_imp_ex_on_if_left_total_onI) auto

lemma Fun_Rel_rev_imp_ex_if_rel_surjective:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_rev_imp_ex_on_if_rel_surjective_atI) auto

corollary Fun_Rel_iff_ex_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex"
  using assms by (urule Fun_Rel_iff_ex_on_if_bi_total_onI) auto
(* reverse does not hold *)


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
    have "(\<forall>y'. q y' \<and> Q y' \<longrightarrow> y' = y)" proof (intro allI impI)
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
  show "(ex1_on P p) \<longleftarrow> (ex1_on Q q)" proof
 assume "ex1_on Q q"
    then obtain y where "Q y" "q y" "(\<forall> y' . (Q y' \<and> q y') \<longrightarrow> y' = y)" by blast
    then obtain x where "R x y" using \<open>bi_total_on P Q R\<close> by blast
    then have "P x \<and> p x" using as assms \<open>Q y\<close> \<open>q y\<close> by blast
    have "(\<forall>x'. p x' \<and> P x' \<longrightarrow> x' = x)" proof (intro allI impI)
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


context galois begin

(*Note Kevin: Try to generalise to relativised concepts next (e.g. rel_surjective_on*)
lemma surjective_left_GaloisI:
  assumes surj: "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and mono: "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
proof (intro rel_surjectiveI)
  fix y
  from surj obtain y' where "y' \<le>\<^bsub>R\<^esub> y" by (elim rel_surjectiveE)
  with mono have "r y' \<^bsub>L\<^esub>\<lessapprox> y" by blast
  then show "in_codom (\<^bsub>L\<^esub>\<lessapprox>) y" by blast
qed

(*Note Kevin: you cannot show monotonicity of r from surjectivity of the Galois relator (but
if L, R are a Galois connection, then r is monotone)*)
lemma rel_surjective_right_if_surjective_left_Galois:
  assumes "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms by (intro rel_surjectiveI) (auto elim: rel_surjectiveE)

lemma left_total_left_GaloisI:
  assumes leftt: "left_total (\<le>\<^bsub>L\<^esub>)"
  and mono: "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and gal_prop: "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "left_total (\<^bsub>L\<^esub>\<lessapprox>)"
proof (intro left_totalI)
  fix x
  from leftt obtain x' where "x \<le>\<^bsub>L\<^esub> x'" by (elim left_totalE)
  with mono gal_prop have "x \<^bsub>L\<^esub>\<lessapprox> l x'" by (intro left_Galois_left_if_left_relI)
  then show "in_dom (\<^bsub>L\<^esub>\<lessapprox>) x" by blast
qed

lemma left_total_left_if_left_total_left_GaloisI:
  assumes "left_total (\<^bsub>L\<^esub>\<lessapprox>)"
  shows "left_total (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro left_totalI) (auto elim!: left_totalE)

corollary bi_total_left_GaloisI:
  assumes "left_total (\<le>\<^bsub>L\<^esub>)"
  and "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (auto intro: surjective_left_GaloisI left_total_left_GaloisI)

corollary bi_total_left_Galois_if_galois_connectionI:
  assumes "left_total (\<le>\<^bsub>L\<^esub>)"
  and "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (intro bi_total_left_GaloisI) auto

corollary left_total_left_rel_surjective_right_if_bi_totalE:
  assumes "bi_total (\<^bsub>L\<^esub>\<lessapprox>)"
  obtains "left_total (\<le>\<^bsub>L\<^esub>)" "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  using assms rel_surjective_right_if_surjective_left_Galois
    left_total_left_if_left_total_left_GaloisI
  by blast

lemma injective_left_Galois_if_rel_injective_left:
  assumes "rel_injective (\<le>\<^bsub>L\<^esub>)"
  shows "rel_injective (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms by (auto dest: rel_injectiveD)
  (* this was suprisingly easy - assumption to strong? *)
  (*looks good!*)

lemma galois_injective_rev:
  assumes "rel_injective (\<^bsub>L\<^esub>\<lessapprox>)"
  shows  "rel_injective (\<le>\<^bsub>L\<^esub>)"
  sorry

lemma galois_right_unique:
  assumes run: "right_unique (\<le>\<^bsub>L\<^esub>)"
  shows "right_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  using assms  apply (intro right_uniqueI, elim left_GaloisE right_uniqueD) sorry

corollary galois_bi_unique:
  assumes inje: "rel_injective (\<le>\<^bsub>L\<^esub>)"
  and run: "right_unique (\<le>\<^bsub>L\<^esub>)"
shows "bi_unique (\<^bsub>L\<^esub>\<lessapprox>)"
  apply (intro bi_uniqueI)
  using run apply (rule galois_right_unique)
  using inje by (rule injective_left_Galois_if_rel_injective_left)

end

context galois
begin

thm galois_connectionE

end

end