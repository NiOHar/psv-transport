theory Transport_Proof
  imports "Transport.Transport" "Transport.Binary_Relations_Surjective" "Transport.Binary_Relation_Properties"
                                      
begin


definition "bi_unique_on A R = (right_unique_on A R \<and> rel_injective_on A R)"

lemma bi_unique_onI [intro]:
  assumes "\<And>x y y'. P x \<Longrightarrow> R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  and "\<And>x x' y. P x \<Longrightarrow> P x' \<Longrightarrow> R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "bi_unique_on P R"
  using assms unfolding bi_unique_on_def by blast

lemma bi_unique_onD1:
  assumes "bi_unique_on P R"
  and "P x"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding bi_unique_on_def using right_unique_onD by auto
                                                          
lemma bi_unique_onD2:
  assumes "bi_unique_on P R"
  and "P x" "P x'"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding bi_unique_on_def using rel_injective_onD by auto

definition "bi_unique T \<equiv> bi_unique_on (\<top> :: 'a \<Rightarrow> bool) (T :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"

lemma bi_unique_eq_bi_unique_on:
  "bi_unique (R :: 'a \<Rightarrow> _) = bi_unique_on (\<top> :: 'a \<Rightarrow> bool) R"
  unfolding bi_unique_def ..

theorem bi_unique_imp_rel_eq_on_pred:
  assumes "bi_unique_on (P :: 'a \<Rightarrow> bool) (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  and "(T \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(T \<Rrightarrow> T \<Rrightarrow> (\<longleftrightarrow>)) (=\<^bsub>P\<^esub>) (=\<^bsub>Q\<^esub>)"
proof (intro Dep_Fun_Rel_relI)
  fix a a' b b'
  assume "T a a'" and "T b b'"
  show "(a =\<^bsub>P\<^esub> b) \<longleftrightarrow> (a' =\<^bsub>Q\<^esub> b')"
  proof (intro iffI)
    assume "a =\<^bsub>P\<^esub> b"
    then have "T a b'" using \<open>T b b'\<close> by blast
    then have "Q b'" using assms(2) \<open>a =\<^bsub>P\<^esub> b\<close> by auto
    moreover from \<open>T a a'\<close> \<open>T a b'\<close> have "a' = b'" using assms(1) \<open>a =\<^bsub>P\<^esub> b\<close> bi_unique_onD1 by fastforce
    ultimately show "a' =\<^bsub>Q\<^esub> b'" by blast
  next
    show "a =\<^bsub>P\<^esub> b" sorry
  qed
qed

theorem bi_unique_imp_rel_eq:
  assumes "bi_unique (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  shows "(T \<Rrightarrow> T \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  sorry

theorem rel_eq_imp_bi_unique:
  assumes "((T::'a \<Rightarrow> 'b \<Rightarrow> bool) \<Rrightarrow> T \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
  shows "bi_unique (T :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
(* using assms proof (intro bi_uniqueI) qed blast+ *) sorry


definition "bi_total_on P Q R = (left_total_on P R \<and> rel_surjective_at Q R)"


lemma bi_total_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> in_dom R x"
  and  "\<And>y. Q y \<Longrightarrow> in_codom R y"
  shows "bi_total_on P Q R"
  unfolding bi_total_on_def using assms by auto

lemma bi_total_onE[elim]:
  assumes "bi_total_on P Q R"
  obtains "left_total_on P R" "rel_surjective_at Q R"
  using assms unfolding bi_total_on_def by blast


abbreviation "rel_bi_total T \<equiv> bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) (T :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"


theorem bi_total_on_imp_rel_all_on: 
  assumes "bi_total_on (P :: 'a \<Rightarrow> bool) (Q :: 'b \<Rightarrow> bool) (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  and "(T \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((T \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (\<lambda> p . (\<forall> x . P x \<longrightarrow> p x)) (\<lambda> q . (\<forall> x . Q x \<longrightarrow> q x))"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume reled: "(T \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(\<forall> x . P x \<longrightarrow> p x) \<longleftrightarrow> (\<forall> x . Q x \<longrightarrow> q x)" by fast
qed


theorem bi_total_imp_rel_all: assumes "rel_bi_total (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  shows "((T \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume reled: "(T \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(All p) \<longleftrightarrow> (All q)" sorry
qed

theorem rel_eq_imp_bi_total:
  assumes "((T \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
  shows "rel_bi_total (T :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
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