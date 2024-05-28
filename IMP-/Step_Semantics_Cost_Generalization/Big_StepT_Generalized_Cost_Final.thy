section "Big step semantics of IMP- generalized to include 
         cost functions depending on command and arithmetic expression
         loaded."
theory Big_StepT_Generalized_Cost_Final imports "../Max_Constant" Main "../Com" "../Big_StepT" "HOL-Eisbach.Eisbach_Tools" begin

paragraph "Summary"
text\<open>We attempt to generalize big step semantics with time for IMP-. 
Based on the big step semantics definition with time of IMP-\<close>

subsection "Big step semantics definition:"

text "In IMP- Branching is only based on whether a variable's value equals 0."

locale BS_Generalized_Cost =
  fixes skip_costs :: "state \<Rightarrow> nat" and 
      value_cost :: "nat \<Rightarrow> nat"
    assumes skip_cost_pos: "\<And> s. skip_costs s > 0"
begin 



fun atomVal_cost :: "atomExp \<Rightarrow> state \<Rightarrow> val" where
"atomVal_cost (V var) s = value_cost (s var)"|
"atomVal_cost (N number) _ = number"

fun aexp_cost :: "aexp \<Rightarrow> state \<Rightarrow> nat" where 
  "aexp_cost (A a) s = atomVal_cost a s" |
  "aexp_cost (Plus a b) s = atomVal_cost a s + atomVal_cost b s" |
  "aexp_cost (Sub a b) s = atomVal_cost a s + atomVal_cost b s" |
  "aexp_cost (Parity n) s = atomVal_cost n s" |
  "aexp_cost (RightShift n) s = atomVal_cost n s" 

abbreviation "while_exit_costs \<equiv> (\<lambda>x. 1 + (skip_costs x))"
abbreviation "assign_costs  \<equiv> (\<lambda>x y . aexp_cost x y + 1)"

inductive
  big_step_tG :: "com \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^sub>G\<^bsup> _ \<^esup> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow>\<^sub>G\<^bsup> skip_costs s \<^esup> s"|
Assign: "(x ::= a,s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s \<^esup> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2;  (c2,s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3 ; C3 = C1 + C2 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^sub>G\<^bsup> C3 \<^esup> s3" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t; C'= C + 1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> C' \<^esup> t" |
IfFalse: "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t; C'=  C + 1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> C' \<^esup> t" |
WhileFalse: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^sub>G\<^bsup> while_exit_costs s \<^esup> s" |
WhileTrue: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3; C3 = C1 + C2 + 1\<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^sub>G\<^bsup> C3 \<^esup> s3" 
end

bundle big_stepG_syntax
begin
notation BS_Generalized_Cost.big_step_tG ("_ \<Rightarrow>\<^sub>G\<^bsup> _ \<^esup> _" 55)
end

bundle no_big_stepG_syntax 
begin
no_notation BS_Generalized_Cost.big_step_tG ("_ \<Rightarrow>\<^sub>G\<^bsup> _ \<^esup> _" 55)
end

(*
code_pred BS_Generalized_Cost.big_step_tG .

text "Some examples using the big step semantics"
experiment
begin

text "finding out the final state and running time of a command:"
schematic_goal ex: "(''x'' ::= A (N 5);; ''y'' ::= A (V ''x''), s) \<Rightarrow>\<^sub>G\<^bsup> ?t \<^esup> ?s"
  apply(rule Seq)
    apply(rule Assign)
   apply simp
   apply(rule Assign)
  apply simp
  done


values "{(t, x). big_step_t (SKIP, \<lambda>_. 0) x t}"

values "{map t [''x''] |t x. (SKIP, <''x'' := 42>) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t}"

values "{map t [''x''] |t x. (''x'' ::=A (N 2), <''x'' := 42>) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t}"

values "{(map t [''x''],x) |t x. (WHILE ''x''\<noteq>0 DO ''x''::= Sub (V ''x'') (N 1),<''x'':=5>) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t }"

end

*)

sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

context BS_Generalized_Cost begin

subsection "proof automation:"

text "Introduction rules:"
declare  BS_Generalized_Cost.big_step_tG.intros [intro]

thm big_step_tG.induct

text "Induction rules with pair splitting"
lemmas big_step_tG_induct = big_step_tG.induct[split_format(complete), 
    OF BS_Generalized_Cost_axioms, consumes 1]

subsection "Rule inversion"
inductive_cases Skip_tE[elim!]: "(SKIP,s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t"
inductive_cases Assign_tE[elim!]: "(x ::= a,s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t"
inductive_cases Seq_tE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s2"
inductive_cases If_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t"
inductive_cases While_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t"
lemma Seq': "\<lbrakk>(c1,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2;  (c2,s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3\<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^sub>G\<^bsup> C1 + C2 \<^esup> s3"
  by (simp add: Seq)
lemma While_tE': "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3\<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^sub>G\<^bsup> C1 + C2 + 1 \<^esup> s3"
  by (simp add: big_step_tG.WhileTrue)

thm Seq_tE


lemma Seq_costs_split: "(c1;;c2, s1) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s3 \<Longrightarrow> \<exists>C1 C2 s2. ((c1,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2) \<and>  ((c2,s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3) \<and> C = C1 + C2" 
  apply (erule Seq_tE)
  by auto

lemma While_costs_split: "\<lbrakk> s1 b \<noteq> 0;  (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s3\<rbrakk> 
    \<Longrightarrow> \<exists>C1 C2 s2. ((c,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2) \<and> ((WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3) \<and> C = C1 + C2  + 1"
  by force


thm While_tE

text "Rule inversion use examples:"
lemma "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t \<Longrightarrow> t = s"
  by blast

lemma assumes "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> t"
  shows "t = s"
  using assms apply cases by auto

lemma assign_t_simp:
  "((x ::= a,s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s\<^esup>  s') \<longleftrightarrow> (s' = s(x := aval a s))"
  using big_step_tG.Assign by auto

lemma seq_costs_split: "(c1;;c2,s1) \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s2 \<Longrightarrow> 
                        \<exists>C1 C2 s. ((c1,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s) \<and> ((c2,s) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s2)
                        \<and> C = C1 + C2 " by auto

subsection "Determinism of Big semantics of IMP-"
theorem big_step_t_state_determ2: "\<lbrakk> (c,s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t; (c,s) \<Rightarrow>\<^sub>G\<^bsup> q \<^esup> u \<rbrakk> \<Longrightarrow> (u = t)"
  apply  (induction  arbitrary: u q rule: big_step_tG.induct)
    apply(elim Skip_tE) apply(simp)
    apply(elim Assign_tE) apply(simp)
  apply blast
    apply(elim If_tE) apply(simp) apply blast
    apply(elim If_tE)  apply (linarith) apply simp
   apply(erule While_tE) apply(simp) apply simp
  by (metis (no_types, opaque_lifting) While_tE) (* Well.. *)

   (*
    apply(elim If_tE) apply(simp) apply blast
    apply(elim If_tE)  apply (linarith) apply simp
    apply(erule While_tE) apply(simp) apply simp
  subgoal premises p for s1 b c x s2 y s3 z u q
    using p(7) apply(safe) 
      apply(erule While_tE)
        using p(1-6) apply fast
        using p(1-6) apply (simp)
      apply(erule While_tE)
        using p(1-6) apply fast
        using p(1-6) by (simp)
done *)

theorem big_step_t_cost_determ2: "\<lbrakk> (c,s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t; (c,s) \<Rightarrow>\<^sub>G\<^bsup> q \<^esup> t \<rbrakk> \<Longrightarrow> p = q"
proof  (induction  arbitrary: q rule: big_step_tG.induct)
  case (Skip s)
  then show ?case 
    apply(elim Skip_tE) by (simp)
next
  case (Assign x a s)
  then show ?case 
       apply(elim Assign_tE) by (simp)
next
  case (Seq c1 s1 C1 s2 c2 C2 s3 C3)
  then show ?case 
    by (metis Seq_tE big_step_t_state_determ2)
next
  case (IfTrue s b c1 C t C' c2)
  then show ?case 
    apply(elim If_tE) 
     defer using contrapos_np contrapos_pp notE notE' rev_notE 
     apply blast 
    using Suc_eq_plus1 by presburger
next
  case (IfFalse s b c2 C t C' c1)
  then show ?case
    apply(elim If_tE) 
     apply linarith
    by (metis (no_types, lifting) add.commute plus_1_eq_Suc)
next
  case (WhileFalse s b c)
  then show ?case 
    by auto
next
  case (WhileTrue s1 b c C1 s2 C2 s3 C3)
  then show ?case proof-
    obtain q1 q2 s2' where "
   ((c, s1) \<Rightarrow>\<^sub>G\<^bsup> q1 \<^esup> s2') \<and>
   ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G\<^bsup> q2 \<^esup> s3) \<and> q = q1 + q2 + 1"
      using WhileTrue.hyps(1) WhileTrue.prems by auto
    have "s2' = s2" 
      using WhileTrue.hyps(2) \<open>((c, s1) \<Rightarrow>\<^sub>G\<^bsup> q1 \<^esup> s2') \<and> ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G\<^bsup> q2 \<^esup> s3) \<and> q = ( q1 + q2 + 1)\<close> big_step_t_state_determ2 by auto
    moreover have "q1 = C1"
    proof- have "(c, s1) \<Rightarrow>\<^sub>G\<^bsup> q1 \<^esup> s2" 
        using \<open>((c, s1) \<Rightarrow>\<^sub>G\<^bsup> q1 \<^esup> s2') \<and> ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G\<^bsup> q2 \<^esup> s3) \<and> q = ( q1  + q2  + 1)\<close> calculation by auto
      thus ?thesis 
        using WhileTrue.IH(1) by auto
    qed
    moreover have "q2 = C2"
    proof- have "(WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> q2 \<^esup> s3" 
        using \<open>((c, s1) \<Rightarrow>\<^sub>G\<^bsup> q1 \<^esup> s2') \<and>
   ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G\<^bsup> q2 \<^esup> s3) \<and> q = (q1 + q2 + 1)\<close> calculation by auto
      thus ?thesis 
        by (simp add: WhileTrue.IH(2))
    qed
    moreover have "q = (C1 + C2 + 1)" 
    proof-
      have " q = (q1 + q2 + 1)" using \<open>((c, s1) \<Rightarrow>\<^sub>G\<^bsup> q1 \<^esup> s2') \<and> ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G\<^bsup> q2 \<^esup> s3) \<and> q = (q1 + q2 + 1)\<close>
        by simp
      thus ?thesis using calculation(2-3)
        by (simp add: \<open>q = (q1 + q2 + 1)\<close>)
    qed
    ultimately show ?thesis 
      by (simp add: WhileTrue.hyps(4))
  qed
qed

lemma bigstep_det: "(c1, s) \<Rightarrow>\<^sub>G\<^bsup> p1 \<^esup> t1 \<Longrightarrow> (c1, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t \<Longrightarrow> p1 = p  \<and> t1=t"
  by (metis big_step_t_cost_determ2 big_step_t_state_determ2)


lemma seq_assign_t_simp:
  "((c ;; x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup>  s') 
  \<longleftrightarrow> (\<exists>s'' t'. t = t' + assign_costs a s'' \<and> ((c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s'') \<and> s' = s''(x := aval a s''))"
proof
  assume "(c;; x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'"
  thm seq_costs_split
  then obtain t' s'' where "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s''" 
                          and "(x ::= a, s'') \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s'' \<^esup> s'" 
                          and "t = t' + assign_costs a s''"
    using local.assign_t_simp by force
  moreover have "\<exists>s'' t'. ((c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s'') \<and> s' = s''(x := aval a s'')"
    using \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s''\<close> \<open>(x ::= a, s'') \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s'' \<^esup> s'\<close> by auto
  ultimately show "\<exists>s'' t'. t = t' + assign_costs a s'' \<and> ((c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s'') \<and> s' = s''(x := aval a s'')"
    by blast
next
  assume "\<exists>s'' t'. t = t' + assign_costs a s'' \<and> ((c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s'') \<and> s' = s''(x := aval a s'')"
  show "(c ;; x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup>  s'"
    using BS_Generalized_Cost_axioms \<open>\<exists>s'' t'. t = t' + assign_costs a s'' \<and> (c, s) \<Rightarrow>\<^sub>G\<^bsup> t' \<^esup> s'' \<and> s' = s''(x := aval a s'')\<close> by auto
qed 

lemma seq_is_noop[simp]: "((SKIP, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s') \<longleftrightarrow> (t = skip_costs s \<and> s = s')" 
  using Skip by auto

lemma seq_skip[simp]: "((c ;; SKIP, s) \<Rightarrow>\<^sub>G\<^bsup> t + skip_costs s'\<^esup> s') \<longleftrightarrow> ((c, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s')"
  by (auto simp add: Seq')

subsection "Progress property"
text "every command costs time"

lemma bigstep_progress:  "(c, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t \<Longrightarrow> p > 0"
  apply(induct rule: big_step_tG.induct, auto)
  by (simp add: skip_cost_pos)
  
subsection "abbreviations and properties"
abbreviation terminates ("\<down>\<^sub>G") where "terminates cs \<equiv> (\<exists>n a. (cs \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a))"
abbreviation thestate ("\<down>\<^sub>G\<^sub>s") where "thestate cs \<equiv> (THE a. \<exists>n. (cs \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a))" 
abbreviation thetime ("\<down>\<^sub>G\<^sub>t") where "thetime cs \<equiv> (THE n. \<exists>a. (cs \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a))"

lemma bigstepT_the_cost: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s' \<Longrightarrow> \<down>\<^sub>G\<^sub>t(c, s) = t"
  using bigstep_det by blast 

lemma bigstepT_the_state: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s' \<Longrightarrow> \<down>\<^sub>G\<^sub>s(c, s) = s'"
  using bigstep_det by blast 

lemma SKIPnot: "(\<not> ((SKIP, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t)) \<longleftrightarrow> (s\<noteq>t \<or> p\<noteq>skip_costs s)" by auto

lemma SKIPp: "\<down>\<^sub>G\<^sub>t(SKIP,s) = skip_costs s"
  apply(rule the_equality)
  apply auto done 

lemma SKIPt: "\<down>\<^sub>G\<^sub>s(SKIP,s) = s"
  apply(rule the_equality)
  apply auto done 

lemma ASSp: "(THE p. Ex (big_step_tG (x ::= e, s) p)) = assign_costs e s"
  apply(rule the_equality)
  apply auto 
  using big_step_tG.Assign by auto  

lemma ASSt: "(THE t. \<exists>p. ((x ::= e, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t)) = s(x := aval e s)"
  apply(rule the_equality)
  apply auto 
  using big_step_tG.Assign by auto

lemma ASSnot: "( \<not>((x ::= e, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t )) = (p\<noteq>assign_costs e s \<or> t\<noteq>s(x := aval e s))"
  apply auto
  using big_step_tG.Assign by auto

(*
lemma If_THE_True: "Suc (THE n. \<exists>a. (c1, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a) =  (THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a)"
     if T: "s b \<noteq> 0" and c1_t: "terminates (c1,s)" for s l
proof -
  from c1_t obtain p t where a: "(c1, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t" by blast
  with T have b: "(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> p+1 \<^esup> t"  using IfTrue by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c1, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a) = p" by simp
  moreover from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a) = p+1" by simp
  ultimately show ?thesis by simp
qed

lemma If_THE_False:
 "Suc (THE n. \<exists>a. (c2, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a) =  (THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a)"
     if T: "s b = 0" and c2_t: "\<down> (c2,s)" for s l
proof -
  from c2_t obtain p t where a: "(c2, s) \<Rightarrow>\<^sub>G\<^bsup> p \<^esup> t"  by blast
  with T have b: "(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> p+1 \<^esup> t"  using IfFalse by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c2, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a) = p" by simp
  moreover from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> n \<^esup> a) = p+1" by simp
  ultimately show ?thesis by simp
qed

*)

lemma terminates_in_state_intro: "(c, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s' \<Longrightarrow> s' = s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro: "(c, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' 
  \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup>t'\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro': "(c', s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' \<Longrightarrow> c' = c
  \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup>t'\<^esup> s''"
  by simp

method dest_com  = 
  (match premises in a: "\<lbrakk>loop_cond; state_upd\<rbrakk> \<Longrightarrow> (_, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s'"
    for s s' t loop_cond state_upd \<Rightarrow> \<open>rule terminates_in_time_state_intro'[OF a]\<close>)

method dest_com' = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; (_, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s'\<rbrakk> \<Longrightarrow> P" 
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "(While _ _, s2) \<Rightarrow>\<^sub>G\<^bsup>t2\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)


method dest_com_init_while = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; ((_ ;; While _ _), s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s'\<rbrakk> \<Longrightarrow> P" 
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "((_ ;; While _ _), s2) \<Rightarrow>\<^sub>G\<^bsup>t2\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)

(*method dest_com_init_while = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; (v ::= a;; WHILE v \<noteq>0 DO _, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s'\<rbrakk> \<Longrightarrow> P" 
    for v a s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "(v ::= a;; WHILE v \<noteq>0 DO _, s2) \<Rightarrow>\<^sub>G\<^bsup>t2\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a\<close>\<close>)*)

lemma terminates_split_if : "(P s \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup>t1\<^esup> s1 ) \<Longrightarrow> 
(\<not> P s \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup>t2\<^esup> s2 ) \<Longrightarrow> (c,s) \<Rightarrow>\<^sub>G\<^bsup>if P s then t1 else t2\<^esup>  if P s then s1 else s2"
  by auto

lemma AssignD': 
"(x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s\<^esup> s' \<Longrightarrow> s' = s (x:= aval a s)"
  by (auto simp add: eval_nat_numeral)

(* TODO: Probably needs induction with pairs, needs fixing *)
lemma com_only_vars: "\<lbrakk>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'; x \<notin> set (Max_Constant.all_variables c)\<rbrakk> \<Longrightarrow> s x = s' x"
  apply (induction c s t s' arbitrary: x rule: big_step_tG_induct) 
  sorry

lemma Seq'': "\<lbrakk> ((c1,s1) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> s2) \<and> P s2; P s2 \<Longrightarrow> ((c2,s2) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> s3) \<and> Q s3; Q s3 \<Longrightarrow> R s3 \<rbrakk>
             \<Longrightarrow> ((c1;;c2, s1) \<Rightarrow>\<^sub>G\<^bsup> x + y \<^esup> s3) \<and> R s3"
  apply auto by (simp add: Seq')

lemma WhileI:
"\<lbrakk>(s1 b \<noteq> 0 \<Longrightarrow> ((c,s1) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> s2) \<and> ((WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> s3));
  (s1 b = 0 \<Longrightarrow> s1 = s3);
  z = (if s1 b \<noteq> 0 then (x + y + 1) else while_exit_costs s1)\<rbrakk>
        \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^sub>G\<^bsup> z \<^esup> s3" 
  using WhileTrue 
   apply auto[1]
  using WhileFalse
  by simp

lemma IfI:
"\<lbrakk>s b \<noteq> 0 \<Longrightarrow> (c1,s) \<Rightarrow>\<^sub>G\<^bsup> x1 \<^esup> t1;
  s b = 0 \<Longrightarrow> (c2,s) \<Rightarrow>\<^sub>G\<^bsup> x2 \<^esup> t2;
  y = ((if s b \<noteq> 0 then x1 else x2) + 1);
  t = (if s b \<noteq> 0 then t1 else t2)\<rbrakk>
        \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> t" 
  by (auto simp add: IfTrue IfFalse)

thm Suc_inject

lemma IfE: 
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> ((if s b \<noteq> 0 then x1 else x2) + 1) \<^esup> (if s b \<noteq> 0 then s1 else s2) \<Longrightarrow> 
 \<lbrakk>\<lbrakk>s b \<noteq> 0; ((if s b \<noteq> 0 then x1 else x2) + 1) = (x1 + 1); 
  (if s b \<noteq> 0 then s1 else s2) = s1; (c1,s) \<Rightarrow>\<^sub>G\<^bsup> x1 \<^esup> s1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; ((if s b \<noteq> 0 then x1 else x2) + 1) = x2 + 1;
   (if s b \<noteq> 0 then s1 else s2) = s2; (c2,s) \<Rightarrow>\<^sub>G\<^bsup> x2 \<^esup> s2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P"
  by (auto simp add: IfTrue IfFalse) 
thm Seq_tE

lemma IfD:
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1 \<^esup> (if s b \<noteq> 0 then t1 else t2) \<Longrightarrow> 
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (c1,s) \<Rightarrow>\<^sub>G\<^bsup> x1 \<^esup> t1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (c2,s) \<Rightarrow>\<^sub>G\<^bsup> x2 \<^esup> t2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P" 
  by (auto simp add: IfTrue IfFalse)

lemma AssignI:
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s\<^esup> s'" 
  using big_step_tG.Assign by auto

lemma AssignI': 
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s\<^esup> s'" 
  using big_step_tG.Assign by auto

lemma AssignI'': 
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> ((x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s\<^esup> s') \<and> (s' = s')" 
  using big_step_tG.Assign by auto

lemma AssignD: "(x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s' \<Longrightarrow> t = assign_costs a s \<and> s' = s(x := aval a s)"
  by auto

lemma compose_programs_1:
  "(c2, s2) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> s2 \<Longrightarrow> 
    ((c1;; c2, s1) \<Rightarrow>\<^sub>G\<^bsup>x + y\<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P" 
  by (simp add: Seq')

lemma compose_programs_2:
  "(c1, s1) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> s2 \<Longrightarrow> (c2, s2) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> s3 \<Longrightarrow> 
    ((c1;; c2, s1) \<Rightarrow>\<^sub>G\<^bsup>x + y\<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (simp add: Seq')

lemma While_tE_time:
"(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t \<Longrightarrow>
  (x = while_exit_costs s \<Longrightarrow> t = s \<Longrightarrow> s b = 0 \<Longrightarrow> P) \<Longrightarrow>
  (\<And>x' s2 y. 0 < s b \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup> x' \<^esup> s2 \<Longrightarrow> (WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> t \<Longrightarrow> x = (x' + y  + 1) \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma Seq_tE_While_init:
  "(WHILE v \<noteq>0 DO c2, s2) \<Rightarrow>\<^sub>G\<^bsup> y \<^esup> s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> s2 \<Longrightarrow> 
    ((c1;; WHILE v \<noteq>0 DO c2, s1) \<Rightarrow>\<^sub>G\<^bsup> x + y \<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  using compose_programs_1 by blast

method dest_com_gen = 
  (erule compose_programs_1[where ?c2.0 = "(Com.While _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; Com.While _ _)"], assumption,
    (match premises
      in a[thin]: 
      "(init_while_cond;; 
                WHILE _ \<noteq>0 DO (loop_body;; init_while_cond);;
                after_loop, _) \<Rightarrow>\<^sub>G\<^bsup>_\<^esup> _"
    for init_while_cond loop_body after_loop  \<Rightarrow> 
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
       for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a]\<close>\<close>))


method dest_com_gen_time = 
  (erule compose_programs_1[where ?c2.0 = "(Com.While _ _)"], assumption,
    erule compose_programs_2[where ?c1.0 = "(_;; Com.While _ _)"], assumption,
    (match premises
      in a[thin]: 
      "(init_while_cond;; 
                WHILE _ \<noteq>0 DO (loop_body;; init_while_cond);;
                after_loop, _) \<Rightarrow>\<^sub>G\<^bsup>_\<^esup> _"
    for init_while_cond loop_body after_loop  \<Rightarrow> 
      \<open>match premises in b[thin]: "\<lbrakk>loop_cond; state_upd; _\<rbrakk> \<Longrightarrow> P"
       for loop_cond state_upd P \<Rightarrow> \<open>subst b[OF _ _ a, simplified add.assoc]\<close>\<close>))

definition big_step_tG_concrete_cost :: "(com \<times> state \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (com \<times> state \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> state \<Rightarrow> nat option)" where
 "big_step_tG_concrete_cost bs x \<equiv> (\<lambda>cs C s. (if bs cs C s then Some (C x) else None))"

end

end