theory clique
  imports Main
begin

text \<open>Formalise the polynomial-time reduction between vertex cover, 
clique and independent set\<close>

section \<open>definitions\<close>

type_synonym 'a graph = "'a set \<times> ('a set set)"

definition invar :: "'a graph => bool" where
"invar g = (
    let (V, E) = g in (\<forall>s \<in> E. (\<forall>x \<in> s. x \<in> V) \<and> card s = 2)
)"

fun vertex_cover :: "'a graph => 'a set => bool" where
"vertex_cover g s = (
    let (_, E) = g in (\<forall>s1 \<in> E. \<exists>x \<in> s1. x \<in> s)
)"

fun clique :: "'a graph => 'a set => bool" where
"clique g s = (
    let (_, E) = g in (\<forall>a \<in> s. \<forall> b \<in> s. a \<noteq> b \<longrightarrow> {a, b} \<in> E)
)"

fun vc_to_clique :: "'a graph => 'a graph" where
"vc_to_clique g = (
    let (V, E) = g in (V, {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b})
)"

fun T_vc_to_clique :: "'a graph => nat" where
"T_vc_to_clique (V, E) = card {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b}"

section \<open>proofs of invariant, correctness and polynomial time\<close>

theorem invar_vc_to_clique : "invar (V, E) \<Longrightarrow> invar (vc_to_clique (V, E))"
by (auto simp add: invar_def)

theorem vc_clique_correct: 
assumes "invar (V, E)"
shows "clique (vc_to_clique (V, E)) (V - s) = vertex_cover (V, E) s"
proof 
  have 1:"\<forall>a. {a} \<notin> E" using assms invar_def by force
  from assms have prems: "\<forall>s \<in> E. (\<forall>x \<in> s. x \<in> V)" "\<forall>s \<in> E. \<exists>a \<in> V. \<exists> b \<in> V. s = {a, b}" 
  apply (auto simp: invar_def) by (metis card_2_iff insert_iff)

  assume "clique (vc_to_clique (V, E)) (V - s)"
  hence "\<forall>a \<in> V-s. \<forall>b \<in> V-s. a \<noteq> b \<longrightarrow> {a, b} \<in> {s. \<exists>a\<in>V. \<exists>b\<in>V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b}" by simp
  hence "\<forall>a \<in> V-s. \<forall>b \<in> V-s. a \<noteq> b \<longrightarrow> {a, b} \<notin> E" by auto
  hence "\<forall>a \<in> V-s. \<forall>b \<in> V-s. {a, b} \<notin> E" using 1 by force
  hence "\<forall>s1 \<in> E. \<exists>a b. s1 = {a, b} \<and> (a \<notin> V-s \<or> b \<notin> V-s)" 
  using prems(2) doubleton_eq_iff by fast
  hence "\<forall>s1 \<in> E. \<exists>a \<in> s1. a \<notin> V-s"
  by auto
  hence "\<forall>s1 \<in> E. \<exists>a \<in> s1. a \<in> s"
  using prems(1) by simp
  thus "vertex_cover (V, E) s" by simp

next 
  assume "vertex_cover (V, E) s"
  hence "\<forall>s1 \<in> E. \<exists>a \<in> s1. a \<in> s" by simp
  hence "\<forall>s1 \<in> E. \<exists>a \<in> s1. a \<notin> V-s" by auto
  hence "\<forall>a \<in>V-s. \<forall>b \<in>V-s. a \<noteq> b \<longrightarrow> {a, b} \<notin> E" by fast
  thus "clique (vc_to_clique (V, E)) (V - s)" by auto
qed

lemma aux0 :
assumes "finite A" "x \<in> A"
shows "card {s. \<exists>a\<in>A. s={x, a} \<and> a \<noteq> x} = card A - 1"
using assms proof (induction A rule: remove_induct)
case empty
  then show ?case by simp
next
  case infinite
  then show ?case by simp
next
  case (remove A)
  
  hence 0:"\<forall>y \<in> A - {x}. card {s. \<exists>a\<in>A - {y}. s = {x, a} \<and> a \<noteq> x} = card (A - {y}) - 1" 
  by auto

  have "\<forall>y \<in> A - {x}. {s. \<exists>a\<in>A. s = {x, a} \<and> a \<noteq> x} = insert {x, y} {s. \<exists>a\<in>A - {y}. s = {x, a} \<and> a \<noteq> x}"
  by auto

  moreover have "\<forall>y \<in> A - {x}. {x, y} \<notin> {s. \<exists>a\<in>A - {y}. s = {x, a} \<and> a \<noteq> x}"
  by auto

  ultimately have 1:"\<forall>y \<in> A - {x}. card {s. \<exists>a\<in>A. s = {x, a} \<and> a \<noteq> x} = card {s. \<exists>a\<in>A - {y}. s = {x, a} \<and> a \<noteq> x} + 1"
    using remove by simp

  from 0 1 have "\<forall>y \<in> A - {x}. card {s. \<exists>a\<in>A. s = {x, a} \<and> a \<noteq> x} = card (A - {y}) - 1 + 1" by simp
  
  hence 3: "\<forall>y \<in> A - {x}. card {s. \<exists>a\<in>A. s = {x, a} \<and> a \<noteq> x} = card (A) - 1"
     by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right card_Diff_singleton 
     card_Suc_Diff1 finite_insert insert_Diff_single insert_iff remove.prems(1) remove.prems(2))
  
     
  from 3 show ?case apply auto by (metis card_le_Suc0_iff_eq remove.prems(1))
  
qed

lemma aux: 
assumes "finite V"
shows "card {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> a \<noteq> b} = card V * (card V - 1) div 2"
using assms proof (induction V rule: finite_remove_induct)
  case empty
  then show ?case by auto
next
  case (remove A)
  have "\<forall>x \<in> A. {s. \<exists>a\<in>A - {x}. \<exists>b\<in>A - {x}. s = {a, b} \<and> a \<noteq> b} = 
  {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b} - {s. \<exists>a\<in>A. s={x, a} \<and> a \<noteq> x}" by auto

  hence "\<forall>x \<in> A. {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b} = 
    {s. \<exists>a\<in>A - {x}. \<exists>b\<in>A - {x}. s = {a, b} \<and> a \<noteq> b} \<union> {s. \<exists>a\<in>A. s={x, a} \<and> a \<noteq> x}"
    by auto

  moreover have "\<forall>x \<in> A. finite {s. \<exists>a\<in>A - {x}. \<exists>b\<in>A - {x}. s = {a, b} \<and> a \<noteq> b}"
  using remove by simp

  moreover have "\<forall>x \<in> A. finite {s. \<exists>a\<in>A. s={x, a} \<and> a \<noteq> x}" using remove by simp

  moreover have "\<forall>x \<in> A. {s. \<exists>a\<in>A - {x}. \<exists>b\<in>A - {x}. s = {a, b} \<and> a \<noteq> b} 
    \<inter> {s. \<exists>a\<in>A. s={x, a} \<and> a \<noteq> x} = {}" by auto

  ultimately have "\<forall>x \<in> A. card {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b}
    = card {s. \<exists>a\<in>A - {x}. \<exists>b\<in>A - {x}. s = {a, b} \<and> a \<noteq> b} + card {s. \<exists>a\<in>A. s={x, a} \<and> a \<noteq> x}" 
  
  using card_Un_disjoint by fastforce

  hence "\<forall>x \<in> A. card {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b}
    = card (A - {x}) * (card (A - {x}) - 1) div 2 + (card A - 1)" 
  using aux0 remove by fastforce

  hence "\<forall>x \<in> A. card {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b}
    = (card A - 1) * (card A - 2) div 2 + (card A - 1)"
 by (metis (no_types, lifting) card_Diff_singleton diff_diff_left nat_1_add_1)

  hence "\<forall>x \<in> A. card {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b}
    = ((card A - 1) * (card A - 2) + (card A - 1) * 2) div 2"
    by simp

  hence "\<forall>x \<in> A. card {s. \<exists>a\<in>A. \<exists>b\<in>A. s = {a, b} \<and> a \<noteq> b}
    = card A * (card A - 1) div 2" 
    by (metis (no_types, lifting) One_nat_def cancel_comm_monoid_add_class.diff_cancel
     card_0_eq distrib_left le_add_diff_inverse2 less_Suc0 less_Suc_eq 
     linorder_not_less mult.commute mult_zero_right one_add_one plus_1_eq_Suc remove.hyps(1) remove.hyps(2))

  then show ?case by auto
qed

theorem vc_to_clique_polynomial : "\<lbrakk>invar (V, E); finite E; finite V\<rbrakk> 
\<Longrightarrow> T_vc_to_clique (V, E) = card V * (card V -1) div 2 - card E"
proof-

assume assms: "invar (V, E)" "finite E" "finite V"
hence "\<forall>s \<in> E. \<exists>a \<in> V. \<exists> b \<in> V. s = {a, b} \<and> a \<noteq> b" 
apply (auto simp add: invar_def) by (metis card_2_iff insert_iff)

hence 1: "E \<subseteq> {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> a \<noteq> b}" by auto 

have "{s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b} 
  = {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> a \<noteq> b} - E" by auto
from card_Diff_subset[OF assms(2) 1] this 
have "card {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b} = 
card {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> a \<noteq> b} - card E" by argo
also have "... = card V * (card V - 1) div 2 - card E" by (auto simp add: aux[OF assms(3)])
finally show ?thesis by simp

qed

section \<open>independent set\<close>

fun independent_set :: "'a graph => 'a set => bool" where
"independent_set g s = (
  let (V, E) = g in 
    (\<forall>a \<in>s. \<forall>b \<in>s. a \<noteq> b \<longrightarrow> {a, b} \<notin> E)
)"


text \<open>constant reduction from independet set to vertex cover\<close>
fun is_to_vc :: "'a graph => 'a graph" where
"is_to_vc g = g"

fun T_is_to_vc :: "'a graph => nat" where
"T_is_to_vc _ = 1"

theorem is_to_vc_correct:
assumes "invar (V, E)"
shows "independent_set (V, E) s = vertex_cover (is_to_vc (V, E)) (V-s)"
proof
  from assms have prems: "\<forall>s \<in> E. (\<forall>x \<in> s. x \<in> V)" "\<forall>s \<in> E. \<exists>a \<in> V. \<exists> b \<in> V. s = {a, b}" 
  apply (auto simp: invar_def) by (metis card_2_iff insert_iff)

  assume "independent_set (V, E) s"
  hence "\<forall>a \<in>s. \<forall>b \<in>s. a \<noteq> b \<longrightarrow> {a, b} \<notin> E" by simp
  hence "(\<forall>a \<in>s. \<forall>b \<in>s.  {a, b} \<notin> E)" using assms by (force simp add: invar_def)
  hence "\<forall>s1 \<in>E. \<exists>a b. s1 = {a, b} \<and> (a \<notin> s \<or> b \<notin> s)" 
  using prems(2) by metis
  hence "\<forall>s1 \<in>E. \<exists>a \<in>s1. a\<notin>s" by auto
  hence "\<forall>s1 \<in>E. \<exists>a \<in>s1. a \<in> V-s" using prems(1) by simp
  then show "vertex_cover (is_to_vc (V, E)) (V-s)" by simp

next
  assume "vertex_cover (is_to_vc (V, E)) (V-s)"
  hence "\<forall>s1 \<in>E. \<exists>a \<in>s1. a \<in>V-s" by simp
  hence "\<forall>s1 \<in>E. \<exists>a \<in>s1. a \<in> V-s" by auto
  hence "\<forall>a \<in>s. \<forall>b \<in>s. a \<noteq> b \<longrightarrow> {a, b} \<notin> E" by fastforce
  then show "independent_set (V, E) s" by simp
qed

theorem is_to_vc_polynomial: "T_is_to_vc g = 1" by simp

text \<open>reduction from clique to independent set\<close>

fun clique_to_is :: "'a graph => 'a graph" where
"clique_to_is g = (
    let (V, E) = g in (V, {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b})
)"

fun T_clique_to_is :: "'a graph => nat" where
"T_clique_to_is (V, E) = card {s. \<exists>a \<in> V. \<exists>b \<in> V. s = {a, b} \<and> s \<notin> E \<and> a \<noteq> b}"

theorem clique_to_is_correct : 
assumes "invar (V, E)" "s \<subseteq> V"
shows "clique (V, E) s = independent_set (clique_to_is (V, E)) s"
using assms apply (auto simp add: invar_def) apply metis by blast

theorem clique_to_is_polynomial : "\<lbrakk>invar (V, E); finite E; finite v\<rbrakk> 
\<Longrightarrow> T_clique_to_is (V, E) = card V * (card V -1) div 2 - card E"
using vc_to_clique_polynomial by auto

theorem threeway_reduction_correct:
assumes "invar (V, E)" "s \<subseteq> V"
shows "clique (V, E) s = vertex_cover (is_to_vc (clique_to_is (V, E))) (V - s)"
proof-

have "clique (V, E) s = independent_set (clique_to_is (V, E)) s"
 using clique_to_is_correct assms by blast

also have "... = vertex_cover (is_to_vc (clique_to_is (V, E))) (V - s)"
 using is_to_vc_correct assms 
by (metis (mono_tags, lifting) clique_to_is.elims invar_vc_to_clique prod.simps(2) vc_to_clique.simps)

finally show ?thesis  by simp
qed


end