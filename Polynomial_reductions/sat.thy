theory sat
  imports Main
begin

datatype var = P "nat" | N "nat"

datatype clause = C "nat" "var set"

type_synonym cnf = "clause set"

fun clause_set :: "clause => var set" where
"clause_set (C _ s) = s"

fun clause_index :: "clause => nat" where
"clause_index (C n _) = n"

fun index :: "var => nat" where
"index (P n) = n" | "index (N n) = n"

fun evaluate :: "var => bool list => bool" where
"evaluate (P n) values = nth values n" |
"evaluate (N n) values = (\<not>(nth values n))"

definition satisfy :: "cnf => bool list => bool" where
"satisfy f values = (
    if (\<exists>x \<in> f. \<exists>n s .x = (C n s) \<and> True \<notin> {y. \<exists>b \<in> s. y = evaluate b values}) then False
    else True
)"

lemma satisfy_empty : "satisfy {} [] = True"
by (auto simp add: satisfy_def)

lemma unsatisfy_empty_clausel: "satisfy {(C n {})} [] = False"
by (auto simp add: satisfy_def)

lemma satisfy_decrease : "\<lbrakk>satisfy c1 values; c2 \<subseteq> c1\<rbrakk> \<Longrightarrow> satisfy c2 values"
by (auto simp add: satisfy_def split: if_splits)

fun tcnf :: "cnf => bool" where
"tcnf f = (\<forall>x \<in> f. \<exists> s. x = (C 3 s))"

(*TODO:
formalisation of sat and sat reduction to 3cnf
*)


end 