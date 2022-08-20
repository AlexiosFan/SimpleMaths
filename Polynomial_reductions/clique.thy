theory clique
  imports Main sat
begin

type_synonym 'a graph = "'a set \<times> ('a set set)"

definition invar :: "'a graph => bool" where
"invar g = (
    let (v, e) = g in (\<forall>s \<in> e. (\<forall>x \<in> s. x \<in> v) \<and> card s = 2)
)"

fun vertex_cover :: "'a graph => 'a set => bool" where
"vertex_cover g s = (
    let (_, e) = g in (\<forall>s1 \<in> e. \<exists>x \<in> s1. x \<in> s)
)"

fun clique :: "'a graph => 'a set => bool" where
"clique g s = (
    let (_, e) = g in (\<forall>a \<in> s. \<forall> b \<in> s. a \<noteq> b \<longrightarrow> {a, b} \<in> e)
)"

fun vc_to_clique :: "'a graph => 'a graph" where
"vc_to_clique g = (
    let (v, e) = g in (v, {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b})
)"

theorem invar_vc_to_clique : "invar (v, e) \<Longrightarrow> invar (vc_to_clique (v, e))"
by (auto simp add: invar_def)

theorem vc_clique: 
assumes "invar (v, e)"
shows "clique (vc_to_clique (v, e)) (v - s) = vertex_cover (v, e) s"
proof 
  have 1:"\<forall>a. {a} \<notin> e" using assms invar_def by force
  from assms have prems: "\<forall>s \<in> e. (\<forall>x \<in> s. x \<in> v)" "\<forall>s \<in> e. \<exists>a \<in> v. \<exists> b \<in> v. s = {a, b}" 
  apply (auto simp: invar_def) by (metis card_2_iff insert_iff)

  assume "clique (vc_to_clique (v, e)) (v - s)"
  hence "\<forall>a \<in> v-s. \<forall>b \<in> v-s. a \<noteq> b \<longrightarrow> {a, b} \<in> {s. \<exists>a\<in>v. \<exists>b\<in>v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b}" by simp
  hence "\<forall>a \<in> v-s. \<forall>b \<in> v-s. a \<noteq> b \<longrightarrow> {a, b} \<notin> e" by auto
  hence "\<forall>a \<in> v-s. \<forall>b \<in> v-s. {a, b} \<notin> e" using 1 by force
  hence "\<forall>s1 \<in> e. \<exists>a b. s1 = {a, b} \<and> (a \<notin> v-s \<or> b \<notin> v-s)" 
  using prems(2) by (smt (z3) doubleton_eq_iff)
  hence "\<forall>s1 \<in> e. \<exists>a \<in> s1. a \<notin> v-s"
  by auto
  hence "\<forall>s1 \<in> e. \<exists>a \<in> s1. a \<in> s"
  using prems(1) by simp
  thus "vertex_cover (v, e) s" by simp

next 
  assume "vertex_cover (v, e) s"
  hence "\<forall>s1 \<in> e. \<exists>a \<in> s1. a \<in> s" by simp
  hence "\<forall>s1 \<in> e. \<exists>a \<in> s1. a \<notin> v-s" by auto
  hence "\<forall>a \<in>v-s. \<forall>b \<in>v-s. a \<noteq> b \<longrightarrow> {a, b} \<notin> e" by fast
  thus "clique (vc_to_clique (v, e)) (v - s)" by auto
qed

fun T_vc_to_clique :: "'a graph => nat" where
"T_vc_to_clique (v, e) = card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b}"

lemma 
assumes "finite v"
shows "card {p. \<exists>a \<in> v. \<exists>b \<in> v. p = (a, b)} = card v * card v"
using assms apply (induction v rule: finite_induct_select)
apply auto
sorry


lemma aux: 
assumes "finite v"
shows "card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b} = card v * (card v - 1) div 2"
sorry

theorem vc_to_clique_polynomial : "\<lbrakk>invar (v, e); finite e; finite v\<rbrakk> 
\<Longrightarrow> T_vc_to_clique (v, e) = card v * (card v -1) div 2 - card e"
proof-

assume assms: "invar (v, e)" "finite e" "finite v"
hence "\<forall>s \<in> e. \<exists>a \<in> v. \<exists> b \<in> v. s = {a, b} \<and> a \<noteq> b" 
apply (auto simp add: invar_def) by (metis card_2_iff insert_iff)

hence 1: "e \<subseteq> {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b}" by auto 

have "{s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b} 
  = {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b} - e" by auto
from card_Diff_subset[OF assms(2) 1] this 
have "card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b} = 
card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b} - card e" by argo
also have "... = card v * (card v - 1) div 2 - card e" by (auto simp add: aux[OF assms(3)])
finally show ?thesis by simp

qed

(*
assume assms: "card v = n" "card e = m" "invar (v, e)" 
hence "\<forall>s \<in> e. \<exists>a \<in> v. \<exists> b \<in> v. s = {a, b} \<and> a \<noteq> b" 
apply (auto simp add: invar_def) by (metis card_2_iff insert_iff)

hence "e \<subseteq> {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b}" by auto 

have "{s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b} 
  = {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b} - e" by auto
hence "card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e \<and> a \<noteq> b} 
= card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> a \<noteq> b} - card e"
*)


(*for tcnf, limit to cnf where clauses have exactly 3 elements for simplification reason*)

datatype vertex = Pos "nat" | Neg "nat" | F "nat" | S "nat" | T "nat"

(*TODO: 3cnf to vc, hindering: the modeling of 3cnf, either set or triple raises significant
problems*)

end