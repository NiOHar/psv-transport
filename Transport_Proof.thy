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

lemma rev_impI [intro]:
  assumes "Q \<Longrightarrow> P"
  shows "P \<longleftarrow> Q"
  using assms by auto

lemma rev_impD [dest]:
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

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_imp_eq_restrict_if_right_unique_on:
  assumes runique: "right_unique_on P R"
  and rel: "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI impI)
  fix a a' b b'
  assume "R a a'" "R b b'" "a =\<^bsub>P\<^esub> b"
  moreover with rel have "R a b'" "Q a'" by auto
  ultimately show "a' =\<^bsub>Q\<^esub> b'" using runique by (auto dest: right_unique_onD)
qed

lemma Fun_Rel_rev_imp_eq_restrict_if_rel_injective_on:
  assumes rinjective: "rel_injective_on P R"
  and rel: "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI rev_impI)
  fix a a' b b'
  assume "R a a'" "R b b'" "a' =\<^bsub>Q\<^esub> b'"
  moreover with rel have "R a b'" "P a" "P b" by auto
  ultimately show "a =\<^bsub>P\<^esub> b" using rinjective by (auto dest: rel_injective_onD)
qed

corollary Fun_Rel_iff_eq_restrict_if_bi_unique_on:
  assumes bi_unique: "bi_unique_on P R"
  and rel: "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof -
  from rel have "(R \<Rrightarrow> (\<longrightarrow>)) P Q" "(R \<Rrightarrow> (\<longleftarrow>)) P Q" by auto
  with Fun_Rel_imp_eq_restrict_if_right_unique_on Fun_Rel_rev_imp_eq_restrict_if_rel_injective_on
    have "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)" "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
    using bi_unique by auto
  then show ?thesis by blast
qed

lemma right_unique_on_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) auto

(* Why does this work with this second assumption? *)
(* because you get \<open>y =Q y --> x =P x'\<close>, but you only have \<open>P x\<close> \<open>P x'\<close> and thus
   you cannot prove \<open>y =Q y\<close>*)
lemma rel_injective_on_if_Fun_Rel_imp_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "rel_injective_on P R"
  using assms by (intro rel_injective_onI) blast

lemma bi_unique_on_if_Fun_Rel_iff_eq_restrict:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
  shows "bi_unique_on P R"
  using assms by (intro bi_unique_onI
    right_unique_on_if_Fun_Rel_imp_eq_restrict
    rel_injective_on_if_Fun_Rel_imp_eq_restrict)
  blast+

end

corollary Fun_Rel_imp_eq_if_right_unique:
  assumes "right_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_imp_eq_restrict_if_right_unique_on) auto

corollary Fun_Rel_rev_imp_eq_if_rel_inective:
  assumes "rel_injective R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_rev_imp_eq_restrict_if_rel_injective_on) auto

corollary Fun_Rel_iff_eq_if_bi_unique:
  assumes "bi_unique R"
  shows "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  using assms by (urule Fun_Rel_iff_eq_restrict_if_bi_unique_on) auto

corollary right_unique_if_Fun_Rel_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longrightarrow>)) (=) (=)"
  shows "right_unique R"
  using assms by (urule right_unique_on_if_Fun_Rel_imp_eq_restrict)

corollary rel_injective_if_Fun_Rel_rev_imp_eq:
  assumes "(R \<Rrightarrow> R \<Rrightarrow> (\<longleftarrow>)) (=) (=)"
  shows "rel_injective R"
  using assms by (urule rel_injective_on_if_Fun_Rel_imp_eq_restrict) auto

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

definition "all_on P Q \<equiv> (\<forall>x. P x \<longrightarrow> Q x)"

lemma all_onI [intro!]:
  assumes "\<And>x. P x \<Longrightarrow> Q x"
  shows "all_on P Q"
  using assms unfolding all_on_def by blast

lemma all_onE [elim]:
  assumes "all_on P Q"
  obtains "\<And>x. P x \<Longrightarrow> Q x"
  using assms unfolding all_on_def by blast

lemma all_on_top_eq_all [simp]: "all_on \<top> = All" by fastforce

lemma all_on_eq_all_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)"
  shows "all_on P \<equiv> All"
  using assms by simp

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma Fun_Rel_iff_all_restrict_if_bi_total_on_imp:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) (all_on P) (all_on Q)"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma Fun_Rel_iff_all_restrict_if_bi_total_on_revimp:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) (all_on P) (all_on Q)"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma Fun_Rel_iff_all_restrict_if_bi_total_on:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (all_on P) (all_on Q)"
  using assms by (intro Dep_Fun_Rel_relI) fast

lemma bi_total_if_Fun_Rel_iff_all_on:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (all_on P) (all_on Q)"
  shows "bi_total_on P Q R"
  proof (intro bi_total_onI rel_surjective_atI left_total_onI)
    fix x
    let ?P1 = "\<lambda>x. \<exists>y. R x y" and ?P2 = "\<lambda>_. True"
    have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
    with assms have "all_on P ?P1 \<longleftrightarrow> all_on Q ?P2" by blast
    then show "P x \<Longrightarrow> in_dom R x" by auto
  next
    fix y
    let ?P1 = "\<lambda>_. True" and ?P2 = "\<lambda>y. \<exists>x. R x y"
    have "(R \<Rrightarrow> (\<longleftrightarrow>)) ?P1 ?P2" by blast
    with assms have "all_on P ?P1 \<longleftrightarrow> all_on Q ?P2" by blast
    then show "Q y \<Longrightarrow> in_codom R y" by auto
qed

end

corollary Fun_Rel_iff_all_if_bi_total:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  using assms by (urule Fun_Rel_iff_all_restrict_if_bi_total_on) auto

corollary bi_total_if_Fun_Rel_iff_all:
  assumes "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  shows "bi_total (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  using assms by (urule bi_total_if_Fun_Rel_iff_all_on)


definition "ex_on P p \<equiv> (\<exists>x. P x \<and> p x)"

lemma ex_onI [intro]:
  assumes "\<exists>x. (P x \<and> Q x)"
  shows "ex_on P Q"
  using assms unfolding ex_on_def by blast

lemma ex_onE [elim]:
  assumes "ex_on P Q"
  obtains x where "P x" "Q x"
  using assms unfolding ex_on_def by blast

lemma ex_on_top_eq_ex [simp]: "ex_on \<top> = Ex" by fastforce

lemma ex_on_eq_ex_if_eq_top [uhint]:
  assumes "P \<equiv> (\<top> ::'a \<Rightarrow> bool)"
  shows "ex_on P \<equiv> Ex"
  using assms by simp

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
begin

lemma left_total_imp_Ex_on_imp:
  assumes "left_total_on P R"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) (ex_on P) (ex_on Q)"
  proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(ex_on P p) \<longrightarrow> (ex_on Q q)" proof
    assume "ex_on P p"
    then obtain x where "P x \<and> p x" by blast
    then obtain y where "R x y" using assms by auto
    then have "Q y \<and> q y" using as assms \<open>P x \<and> p x\<close> by blast
    then show "ex_on Q q"  by blast
  qed
qed

lemma surjective_imp_Ex_on_revimp:
  assumes "rel_surjective_at Q R"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftarrow>)) \<Rrightarrow> (\<longleftarrow>)) (ex_on (P::'a \<Rightarrow> bool)) (ex_on (Q::'b \<Rightarrow> bool))"
  proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(ex_on P p) \<longleftarrow> (ex_on Q q)" proof
    assume "ex_on Q q"
    then obtain y where "q y \<and> Q y" by blast
    then obtain x where "R x y" using assms by (auto elim: rel_surjectiveE)
    then have "p x & P x" using as assms \<open>q y \<and> Q y\<close> by blast
    then show "ex_on P p" by blast
  qed
qed

corollary bi_total_imp_Ex_on_iff:
  assumes "bi_total_on P Q R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (ex_on P) (ex_on Q)"
proof (intro Dep_Fun_Rel_relI iffI)
  fix p q
  assume as: "(R \<Rrightarrow> (=)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  then show "ex_on P p \<Longrightarrow> ex_on Q q" using left_total_imp_Ex_on_imp assms by blast
  with as show "ex_on Q q \<Longrightarrow> ex_on P p" using surjective_imp_Ex_on_revimp assms by blast
qed

end

lemma left_total_imp_Ex_imp:
  assumes "left_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex Ex"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(\<exists>x. p x) \<longrightarrow> (\<exists>x. q x)" proof
    assume "\<exists>x. p x"
    then obtain x where "p x" by blast
    then obtain y where "R x y" using assms by (auto elim: left_totalE)
    then have "q y" using as \<open>p x\<close> by blast
    then show "\<exists> y . q y" by blast
  qed
qed

lemma surjective_imp_Ex_revimp:
  assumes "rel_surjective R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex Ex"
  proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(\<exists>x. p x) \<longleftarrow> (\<exists>x. q x)" proof
    assume "\<exists> y . q y"
    then obtain y where "q y" by blast
    then obtain x where "R x y" using assms by (auto elim: rel_surjectiveE)
    then have "p x" using as \<open>q y\<close> by blast
    then show "\<exists>x. p x" by blast
  qed
qed

corollary bi_total_imp_Ex_iff:
  assumes "bi_total R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex Ex"
  using assms by (urule bi_total_imp_Ex_on_iff) auto


definition "ex1_on P p \<equiv> (\<exists>!x. P x \<and> p x)"

lemma ex_on1I[intro]: assumes "\<exists>!x. (P x \<and> Q x)" shows "ex1_on P Q"
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

lemma left_total_imp_Ex1_imp: assumes "bi_total R" "right_unique R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longrightarrow>)) Ex1 Ex1"
  proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "Ex1 p \<longrightarrow> Ex1 q" proof
    assume "Ex1 p"
    then obtain x where "p x" "(\<forall>x'. p x' \<longrightarrow> x' = x)" by blast
    from \<open>p x\<close> obtain y where "R x y" using assms by (auto elim: left_totalE)
    then have "q y" using as \<open>p x\<close> by blast
    then have "\<exists> y . q y" by blast
    have "(\<forall>y'. q y' \<longrightarrow> y' = y)" proof (intro allI impI)
      fix y'
      assume "q y'"
      from assms obtain x' where "R x' y'" by (auto elim: rel_surjectiveE)
      from this \<open>q y'\<close> as have "p x'" by blast
      from this \<open>(\<forall>x'. p x' \<longrightarrow> x' = x)\<close> have "x' = x" by blast
      from this \<open>right_unique R\<close> \<open>R x' y'\<close> \<open>R x y\<close> have "y = y'" by (auto dest: right_uniqueD)
      then show "y' = y" by blast
    qed
    with \<open>\<exists> y . q y\<close> show "\<exists>! y . q y" by blast
  qed
qed

lemma surjective_imp_Ex1_revimp: assumes "bi_total R" "rel_injective R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftarrow>)) Ex1 Ex1"
  proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume as: "(R \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  show "(\<exists>!x. p x) \<longleftarrow> (\<exists>!x. q x)" proof
    assume "Ex1 q"
    then obtain y where "q y" "(\<forall>y'. q y' \<longrightarrow> y' = y)" by blast
    from \<open>q y\<close> obtain x where "R x y" using assms by (auto elim: rel_surjectiveE)
    then have "p x" using as \<open>q y\<close> by blast
    then have "\<exists>x. p x" by blast
    have "(\<forall>x'. p x' \<longrightarrow> x' = x)" proof (intro allI impI)
     fix x'
      assume "p x'"
      from assms obtain y' where "R x' y'" by (auto elim: left_totalE)
      from this \<open>p x'\<close> as have "q y'" by blast
      from this \<open>(\<forall>y'. q y' \<longrightarrow> y' = y)\<close> have "y' = y" by blast
      from this \<open>rel_injective R\<close> \<open>R x' y'\<close> \<open>R x y\<close> have "x = x'" by (fast dest: rel_injectiveD)
      then show "x' = x" by blast
    qed
    with \<open>\<exists>x. p x\<close> show "\<exists>!x. p x" by blast
  qed
qed


corollary bi_total_imp_Ex1_iff: assumes "bi_total R" "bi_unique R"
  shows "((R \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) Ex1 Ex1"
  using assms apply (intro Dep_Fun_Rel_relI) apply (elim bi_totalE bi_uniqueE) apply (intro iffI)
  using left_total_imp_Ex1_imp[of R] surjective_imp_Ex1_revimp[of R] sorry



context galois begin

lemma galois_surjective:
  assumes surj: "rel_surjective (\<le>\<^bsub>R\<^esub>)"
  and mono: "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  shows "rel_surjective (\<^bsub>L\<^esub>\<lessapprox>)"
proof (intro rel_surjectiveI)
  fix y
  from surj obtain y' where "y' \<le>\<^bsub>R\<^esub> y" by (elim rel_surjectiveE)
  with mono have "r y' \<^bsub>L\<^esub>\<lessapprox> y" by blast
  then show "in_codom (\<^bsub>L\<^esub>\<lessapprox>) y" by blast
qed

end

context galois
begin

thm galois_connectionE

end

end