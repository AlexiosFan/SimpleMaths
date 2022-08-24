theory set_cover
  imports clique
begin

datatype 'a set_cover = SC "'a set" "'a set set"

definition invar :: "'a set_cover => bool" where
"invar sc = (
    case sc of (SC U S) => (\<forall>s \<in> S. s \<subseteq> U)
)"

fun cover :: "'a set_cover => 'a set set => bool" where
"cover (SC U S) C = (\<Union>{s. s \<in> C} = U)"

lemma cover_snd_def : "\<lbrakk>invar (SC U S); C \<subseteq> S\<rbrakk> \<Longrightarrow> cover (SC U S) C = (\<forall>e \<in> U. \<exists>s \<in> C. e \<in> s)"
by (auto simp add: invar_def)

fun vc_to_sc :: "'a graph => 'a set set_cover" where
"vc_to_sc (V, E) = SC E {s0. \<exists>a \<in> V. s0 = {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}}"

fun T_vc_to_sc :: "'a graph => nat" where
"T_vc_to_sc (V, E) = \<Sum> {c. \<exists>a \<in> V. c = card {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}}"

theorem invar_vc_to_sc : "clique.invar (V, E) \<Longrightarrow> invar (vc_to_sc (V, E))"
by (auto simp add: invar_def clique.invar_def)

theorem vc_to_sc_correct : 
assumes "clique.invar (V, E)"
shows "vertex_cover (V, E) S = cover (vc_to_sc (V, E)) {s0. \<exists>a \<in> S. s0 = {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}}"
proof


  assume "vertex_cover (V, E) S"
  hence "\<forall>e \<in> E. \<exists>x \<in> S. x \<in> e" by auto

  moreover have "\<forall>e \<in> E. \<exists>a\<in>V. \<exists>b\<in>V. e = {a, b}" 
  using assms apply (auto simp: clique.invar_def) by (metis card_2_iff insert_iff)

  ultimately have  "\<forall>e \<in> E. \<exists>x \<in> S. e \<in> {s. \<exists>b\<in>V. s = {x, b} \<and> s \<in> E}" by fastforce

  hence "\<forall>e \<in> E. \<exists>s \<in> {s0. \<exists>a \<in> S. s0 = {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}}. e \<in> s"
  using mem_Collect_eq by (smt (verit))

  then show "cover (vc_to_sc (V, E)) {s0. \<exists>a \<in> S. s0 = {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}}"
  by auto
next
  assume "cover (vc_to_sc (V, E)) {s0. \<exists>a \<in> S. s0 = {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}}"
  then show "vertex_cover (V, E) S" by auto
qed

lemma "clique.invar (V, E) \<Longrightarrow> finite V \<Longrightarrow> finite E \<Longrightarrow> card {s0. \<exists>a \<in> V. s0 = {s. \<exists>b\<in>V. s = {a, b} \<and> s \<in> E}} = card V"
apply (induction V rule: remove_induct)
apply (auto simp add: clique.invar_def)
sorry

theorem vc_to_sc_polynomial : 
assumes "clique.invar (V, E)" "finite V" "finite E"
shows "T_vc_to_sc (V, E) = card E * 2"
using assms proof (induction E rule: remove_induct)
  case empty
  then show ?case by simp
next
  case infinite
  then show ?case by simp
next
  case (remove A)
  then show ?case apply auto sorry
qed


end