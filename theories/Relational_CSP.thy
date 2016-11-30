theory Relational_CSP

imports
 Main
 List
begin

section {* Type Definitions*}

datatype 'a tr = tick | symbol 'a

type_synonym 'a trace = "'a list"
type_synonym 'a failure = "('a list * 'a set)"
type_synonym 'a state = "('a failure) option"
type_synonym 'a prel = "('a state * 'a state) set"

text {* In Failures-Divergences a CSP process is denoted by a pair of
        failures (set of failures) and divergences (set of traces).*}

type_synonym 'a process = "('a failure) set \<times> ('a trace) set"

section {* Healthiness Conditions *}

definition tracesbot :: "'a process \<Rightarrow> ('a trace) set" ("traces\<^sub>\<bottom>'(_')")
 where "tracesbot P = {s. \<exists>X. (s, X) \<in> fst P} \<union> snd P"
 
text {* F1: tracesbot is non-empty and prefix-closed *}

definition F1 :: "'a process \<Rightarrow> bool"
 where "F1 P \<equiv> traces\<^sub>\<bottom>(P) \<noteq> {} \<and> (\<forall>t. t \<in> traces\<^sub>\<bottom>(P) \<longrightarrow> (\<exists>s a. t=s @ a \<and> s \<in> traces\<^sub>\<bottom>(P)))"
 
text {* F2: Failures are subset-closed. *}
 
definition F2 :: "'a process \<Rightarrow> bool"
 where "F2 P \<equiv> \<forall>s X Y. (s, X) \<in> (fst P) \<and> Y \<subseteq> X \<longrightarrow> (s, Y) \<in> (fst P)"
 
text {* F3: When a process refuses $x$ it also refuses all events that
            it can never perform after the same trace. *}
 
definition F3 :: "'a process \<Rightarrow> bool"
 where "F3 P \<equiv> \<forall>s X Y. ((s, X) \<in> (fst P) \<and> (snd P) \<inter> {x. (s@x) \<in> traces\<^sub>\<bottom>(P)} = {}) \<longrightarrow> (s, X \<union> Y) \<in> (fst P)"

text {* There's no way to define F4 because we do not treat 'tick' here. *}

definition D1 :: "'a process \<Rightarrow> bool"
 where "D1 P \<equiv> \<forall>s t. s \<in> (snd P) \<longrightarrow> (s@t) \<in> (snd P)"
 
definition D2 :: "'a process \<Rightarrow> bool"
 where "D2 P \<equiv> \<forall>s X. s \<in> (snd P) \<longrightarrow> (s, X) \<in> (fst P)"

definition trace :: "'a failure \<Rightarrow> 'a trace"
 where "trace f = fst f"

definition fd2r :: "('a failure) set \<Rightarrow> ('a trace) set \<Rightarrow> 'a prel"
 where "fd2r F D = { (s,s'). {the s,the s'} \<subseteq> F \<and> s \<noteq> None \<and> s' \<noteq> None
                             \<and> (\<exists>a. trace (the s') = (trace (the s) @ a))
                             }
                   \<union> { (s,s'). trace (the s) \<in> D \<and> 
                               (s'=None \<or> (\<exists>a. trace (the s') = trace (the s) @ a)) } \<union> { (None,None) }"                               

definition fdP2r :: "'a process \<Rightarrow> 'a prel"
 where "fdP2r P = fd2r (fst P) (snd P)"
                               
definition divFailureStrict :: "('a failure) set \<Rightarrow> ('a trace) set \<Rightarrow> ('a failure) set"
 where "divFailureStrict F D = F \<union> {(s,X). s \<in> D}"
 
definition divStrict :: "('a trace) set \<Rightarrow> ('a trace) set"
 where "divStrict D = D \<union> {s'. \<exists>s a. s' = s @ a \<and> s \<in> D}"
 
definition F2f :: "('a failure) set \<Rightarrow> bool"
 where "F2f F \<equiv> \<forall>s X Y. (s, X) \<in> F \<and> Y \<subseteq> X \<longrightarrow> (s, Y) \<in> F" 
 
section {* Relational model*}

subsection {* Healthiness Conditions*}

text {* In a predicative style *}

text {* Prefix closure *} 
 
definition CR1H :: "'a prel \<Rightarrow> bool"
 where "CR1H R = (\<forall>s s'. ((s,s') \<in> R \<and> s\<noteq>None \<and> s'\<noteq>None) \<longrightarrow> (\<exists>t. trace (the s') = trace (the s) @ t))"
 
text {* Divergence strictness*}

definition CR2H :: "'a prel \<Rightarrow> bool"
 where "CR2H R = (\<forall>s s'. ((s,None) \<in> R \<and> s \<noteq> None \<and> s' \<noteq> None 
                  \<and> trace (the s) = trace (the s')) \<longrightarrow> (s',None) \<in> R)"
                  
text {* None to None *}

definition CR3H :: "'a prel \<Rightarrow> bool"
 where "CR3H R = (\<forall>s. s \<noteq> None \<and> (None,s) \<notin> R \<and> (None,None) \<in> R)"
 
text {* Or in a fixed-point style *}

definition R1H :: "'a prel \<Rightarrow> 'a prel"
 where "R1H R = { (s,s'). \<exists>t.(s,s') \<in> R \<and> s \<noteq> None \<and> trace (the s') = trace (the s) @ t }"

definition R2H :: "'a prel \<Rightarrow> 'a prel"
 where "R2H R = { (s,s'). \<exists>t. (s,None) \<in> R \<and> s \<noteq> None \<and> trace(the s') = trace (the s) @ t \<or> (s,s') \<in> R }"
 
definition R3H :: "'a prel \<Rightarrow> 'a prel"
 where "R3H R = R \<union> {(None,None)}"

subsection {* Linking from the relational model *}
 
text {* From a relation to a set of failures. *}

definition r2f :: "'a prel \<Rightarrow> ('a failure) set"
 where "r2f R = { f. \<exists>s s'. (s,s') \<in> R \<and> f = the s' \<and> s \<noteq> None \<and> s' \<noteq> None}"
 
text {* From a relation to a set of divergences. *} 
 
definition r2d :: "'a prel \<Rightarrow> ('a trace) set"
 where "r2d R = { t. \<exists>s. (s,None) \<in> R \<and> t = trace (the s) \<and> s \<noteq> None}"
 
text {* From a relation to a CSP process. *} 
 
definition r2P :: "'a prel \<Rightarrow> 'a process"
 where "r2P R = (r2f R, r2d R)"
 
lemma "CR1H(fd2r F D)"
 apply (simp add:CR1H_def fd2r_def trace_def)
 by auto
 
lemma "CR2H(fd2r F D)"
 apply (simp add:fd2r_def CR2H_def trace_def)
 by auto
 
lemma
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "fd2r (r2f R) (r2d R) = R"
 using assms
 apply (simp add:CR3H_def CR2H_def CR1H_def r2f_def r2d_def fd2r_def trace_def)
 by blast
 
lemma r2fd_is_F1:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "F1((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast

lemma r2fd_is_F2:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "F2((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast

lemma r2fd_is_F3:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "F3((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast
 
lemma r2fd_is_D1:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "D1((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast
 
lemma r2fd_is_D2:
 assumes "CR3H R" "CR2H R" "CR1H R"
 shows "D2((r2f R),(r2d R))"
 using assms unfolding CR1H_def CR2H_def CR3H_def
 by blast

lemma r2f_fd2r:
assumes "divStrict D = D" and "divFailureStrict F D = F"
shows "r2f (fd2r F D) = F"
apply auto
apply (simp add:fd2r_def r2f_def trace_def)
apply auto
using assms unfolding divStrict_def divFailureStrict_def
apply (simp add:fd2r_def r2f_def)
apply blast
using assms unfolding divStrict_def divFailureStrict_def
apply (simp add:fd2r_def r2f_def)
by (metis (no_types, lifting) append_Nil2 option.sel)

lemma r2d_fd2r: "r2d (fd2r F D) = D"
apply auto 
apply (simp add:fd2r_def r2d_def)
apply blast
apply (simp add:fd2r_def r2d_def)
by (metis option.sel prod.sel(1) trace_def)

lemma D1_is_divStrict:
 shows "D1(P) = (divStrict (snd P) = (snd P))"
 apply (simp add:divStrict_def D1_def)
 by blast
 
lemma D2_is_divFailureStrict:
 shows "D2(P) = (divFailureStrict (fst P) (snd P) = (fst P))"
 apply (simp add:divFailureStrict_def D2_def)
 by blast

lemma r2P_fdP2r:
 assumes "D1(P)" "D2(P)"
 shows "r2P (fdP2r P) = P"
 apply (simp add:r2P_def fdP2r_def)
 using assms
 by (simp add: D1_is_divStrict D2_is_divFailureStrict r2d_fd2r r2f_fd2r)

lemma fdP2r_r2P:
 assumes "CR3H R"
 shows "fdP2r (r2P R) = R"
 using CR3H_def and assms by blast

end