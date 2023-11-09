theory Transport_Proof
  imports "Transport.Transport" "Transport.Binary_Relations_Surjective" "Transport.Binary_Relation_Properties"
Main                                             
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

abbreviation "rel_bi_unique T \<equiv> bi_unique_on (\<top> :: 'a \<Rightarrow> bool) (T :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"



theorem bi_unique_imp_rel_eq_on_pred:
  assumes "bi_unique_on (P :: 'a \<Rightarrow> bool) (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  and "(T \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "(T \<Rrightarrow> T \<Rrightarrow> (\<longleftrightarrow>)) (eq_onp P) (eq_onp Q)"
proof (intro Dep_Fun_Rel_relI)
  fix a a' b b'
  assume "T a a'" and "T b b'"
  with assms show "(eq_onp P a b) \<longleftrightarrow> (eq_onp Q a' b')" proof (auto, goal_cases)
    case 1              
    then have "P a \<Longrightarrow> Q a'" using assms by blast
    from 1 have "T a b'" using \<open>T b b'\<close> eq_onp_to_eq by fastforce
    then have "a' = b'" using assms \<open>T a a'\<close> \<open>eq_onp P a b\<close> eq_onp_def
      by (metis bi_unique_onD1)
    then show ?case
      by (metis "1"(5) \<open>P a \<Longrightarrow> Q a'\<close> eq_onp_def)
  next
    case 2
    then show ?case
      by (smt (z3) Dep_Fun_Rel_rel_def bi_unique_onD2 eq_onp_def)
  qed
qed

theorem bi_unique_imp_rel_eq:
  assumes "rel_bi_unique (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  shows "(T \<Rrightarrow> T \<Rrightarrow> (\<longleftrightarrow>)) (=) (=)"
proof (intro Dep_Fun_Rel_relI)
  fix a a' b b'
  assume "T a a'" and "T b b'"
  with assms show "(a = b) \<longleftrightarrow> (a' = b')" by (auto dest: bi_unique_onD1 bi_unique_onD2)
 qed


definition "bi_total_on P Q R = (left_total_on P R \<and> rel_surjective_at Q R)"
                                                               
lemma bi_total_onI [intro]:
  assumes "\<And>y. Q y \<Longrightarrow> in_codom R y"
  and  "\<And>x. P x \<Longrightarrow> in_dom R x"
  shows "bi_total_on P Q R"
  unfolding bi_total_on_def using assms by auto

lemma bi_total_onE1:
  assumes "bi_total_on P Q R"
  and "Q y"
obtains "x" where "R x y"
  unfolding bi_total_on_def using rel_surjective_atE assms
  by (metis bi_total_on_def)

lemma bi_total_onE2:
  assumes "bi_total_on P Q R"
  and "P x"
obtains "y" where "R x y"
  unfolding bi_total_on_def using left_total_onE assms
  by (metis bi_total_on_def)

abbreviation "rel_bi_total T \<equiv> bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) (T :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"


theorem bi_total_on_imp_rel_all_on: assumes "bi_total_on (P :: 'a \<Rightarrow> bool) (Q :: 'b \<Rightarrow> bool) (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  and "(T \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "((T \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) (\<lambda> p . (\<forall> x . P x \<longrightarrow> p x)) (\<lambda> q . (\<forall> x . Q x \<longrightarrow> q x))"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume reled: "(T \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(\<forall> x . P x \<longrightarrow> p x) \<longleftrightarrow> (\<forall> x . Q x \<longrightarrow> q x)" by (auto elim: bi_total_onE1 bi_total_onE2)
qed


theorem bi_total_imp_rel_all: assumes "rel_bi_total (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  shows "((T \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> (\<longleftrightarrow>)) All All"
proof (intro Dep_Fun_Rel_relI)
  fix p q
  assume reled: "(T \<Rrightarrow> (\<longleftrightarrow>)) (p::'a \<Rightarrow> bool) (q::'b \<Rightarrow> bool)"
  with assms show "(All p) \<longleftrightarrow> (All q)" by (auto elim: bi_total_onE1 bi_total_onE2)
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