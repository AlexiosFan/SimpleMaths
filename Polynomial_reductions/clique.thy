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
    let (_, e) = g in (\<forall>a \<in> s. \<forall> b \<in> s. {a, b} \<in> e)
)"

fun vc_to_clique :: "'a graph => 'a graph" where
"vc_to_clique g = (
    let (v, e) = g in (v, {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e})
)"

theorem vc_clique: "invar (v, e) \<Longrightarrow> clique (vc_to_clique (v, e)) (v - s) = vertex_cover (v, e) s"
proof -
assume "invar (v, e)"
hence prems: "\<forall>s \<in> e. (\<forall>x \<in> s. x \<in> v)" "\<forall>s \<in> e. \<exists>a \<in> v. \<exists> b \<in> v. s = {a, b}" 
apply (auto simp: invar_def) by (metis card_2_iff insert_iff) 

have "clique (vc_to_clique (v, e)) (v - s) = (\<forall>a \<in>v-s. \<forall>b \<in> v-s. {a, b} \<in> {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e})" by simp
also have "... = (\<forall>a \<in>v-s. \<forall>b \<in> v-s. {a, b} \<notin> e)" by blast
also have "... = (\<forall>s1 \<in> e. \<exists>a b. s1 = {a, b} \<and> (a \<notin> v-s \<or> b \<notin> v-s))" 
using prems by (smt (z3) doubleton_eq_iff)
also have "... = (\<forall>s1 \<in> e. \<exists>a \<in> s1. a \<notin> v-s)" using prems(2) by fastforce
also have "... = (\<forall>s1 \<in> e. \<exists>a \<in> s1. a \<in> s)" using prems(1) by simp
finally show ?thesis  by simp
qed

fun T_vc_to_clique :: "'a graph => nat" where
"T_vc_to_clique g = (
    let (v, e) = g in (card v) + (card {s. \<exists>a \<in> v. \<exists>b \<in> v. s = {a, b} \<and> s \<notin> e})
)"

theorem polynomil_time_vc_to_clique : "\<lbrakk>n = card v; m = card e; invar (v, e)\<rbrakk> 
\<Longrightarrow> T_vc_to_clique (v, e) = (n ^ 2 + n) div 2 - m"
proof-
  assume prems: "n = card v" "m = card e" "invar (v, e)"
  then have "2 * T_vc_to_clique (v, e) = n ^ 2 + n - 2 * m" apply auto sorry
  then show ?thesis by simp
qed


(*for tcnf, limit to cnf where clauses have exactly 3 elements for simplification reason*)

datatype vertex = Pos "nat" | Neg "nat" | F "nat" | S "nat" | T "nat"

(*TODO: 3cnf to vc, hindering: the modeling of 3cnf, either set or triple raises significant
problems*)

end