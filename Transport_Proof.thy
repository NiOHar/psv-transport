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


theorem bi_unique_imp_rel_eq:
  assumes biuni: "bi_unique_on (\<top>::'a \<Rightarrow> bool) (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  shows "(T \<Rrightarrow> T \<Rrightarrow> (=)) (=) (=)"
proof (intro Dep_Fun_Rel_relI)
  fix a a' b b'
  assume taa: "T a a'" and tbb: "T b b'"
  show "(a = b) = (a' = b')" proof (cases "a = b")
    case True
    then have "T a b'" using tbb by blast
    then have "a' = b'" using biuni taa bi_unique_onD1[of \<top> T a a' b'] by blast
    then show ?thesis using True by presburger
  next
    case False
    show ?thesis proof (rule ccontr)
      assume "(a = b) \<noteq> (a' = b')"
      from this False have "a' = b'" by argo
      then have "a = b" using biuni bi_unique_onD2[of \<top> T a b b']  taa tbb by blast
      from this False show "False" by argo
    qed
 qed
qed

definition "bi_total_on A R = (rel_surjective_at A R \<and> left_total_on A R)"
                                                               
lemma bi_total_onI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> in_codom R y"
  and  "\<And>x. P x \<Longrightarrow> in_dom R x"
  shows "bi_total_on P R"
  unfolding bi_total_on_def using assms by auto

lemma bi_total_onE1:
  assumes "bi_total_on P R"
  and "P y"
obtains "x" where "R x y"
  unfolding bi_total_on_def using rel_surjective_atE assms
  by (metis bi_total_on_def)

lemma bi_total_onE2:
  assumes "bi_total_on P R"
  and "P x"
obtains "y" where "R x y"
  unfolding bi_total_on_def using left_total_onE assms
  by (metis bi_total_on_def)

theorem bi_total_imp_rel_all: assumes bit: "bi_total_on (\<top>::'a \<Rightarrow> bool) (T::'a \<Rightarrow> 'b \<Rightarrow> bool)" 
  shows "((T \<Rrightarrow> (=)) \<Rrightarrow> (=)) All All"
proof (intro Dep_Fun_Rel_relI)
  fix a b
  assume reled: "(T \<Rrightarrow> (=)) (a::'a \<Rightarrow> bool) (b::'b \<Rightarrow> bool)"
  then show "(All a) = (All b)" sorry
  qed
qed
end