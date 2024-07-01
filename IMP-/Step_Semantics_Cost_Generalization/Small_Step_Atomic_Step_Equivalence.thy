\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "Equivalence of big step and small step semantics"

theory Small_Step_Atomic_Step_Equivalence imports Big_StepT_Generalized_Cost_Final Atomic_StepT_GC begin

paragraph "Introduction"
text "We show that the big and small step semantics with time we defined for IMP- are equivalent."

context BS_Generalized_Cost begin

fun step_cost :: "com \<Rightarrow> state \<Rightarrow> nat" where
 "step_cost SKIP s = skip_cost s" |
 "step_cost (Assign x a) s = aexp_cost a s" |
 "step_cost (Seq c1 c2) s = step_cost c1 s" |
 "step_cost _ _  = 0" 

fun next_small_step :: "com \<Rightarrow> state \<Rightarrow> com" where
 "next_small_step SKIP s = SKIP" |
 "next_small_step (Assign x a) s = SKIP" |
 "next_small_step (Seq SKIP c2) s = c2" |
 "next_small_step (Seq c1 c2) s = Seq (next_small_step c1 s) c2" |
 "next_small_step (If b c1 c2) s = (if s b \<noteq> 0 then c1 else c2)" |
 "next_small_step (While b c) s = (if s b \<noteq> 0 then (c ;; WHILE b \<noteq>0 DO c) else SKIP)" 

text "from small step to atomic step semantics"
lemma small_to_atomic_helper: "(c, s) \<rightarrow> (c',s') \<Longrightarrow>  (c, s , 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> Suc (step_cost c s) \<^esup> (c', s',0)"
proof (induction c s  c' s' rule: small_step_induct)
  case (Assign x a s)
  then show ?case using Assing_ex 
    using Suc_eq_plus1 step_cost.simps(2) by presburger
next
  case (Seq1 c\<^sub>2 s)
  then show ?case using Skip_ex by simp
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case using star_seq2 by auto
qed auto

(*

lemma big_to_small: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t + skip_costs s \<^esup> s' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (SKIP, s', 0)"
  using big_to_small_helper by blast

*)

text "from atomic to small semantics"

lemma atomic_to_small1:
"(c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', (step_cost c'' s)) \<Longrightarrow> (c, s) \<rightarrow> (c',s')"
  by (induction c s arbitrary: c' s' rule: step_cost.induct) auto (* ? ? ? *)

lemma atomic_step_cost :
"(c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (next_small_step c s, s', m) \<Longrightarrow> m = step_cost c s"
  by (induction c s arbitrary: s' m rule: next_small_step.induct) auto

(*
lemma atomic_to_small: "(c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> Suc (step_cost c s) \<^esup> (c', s', 0) \<Longrightarrow> (c, s) \<rightarrow> (c',s')"
proof (induction c s arbitrary: s' c' rule: step_cost.induct)
  case (1 s)
  then show ?case by auto
next
  case (2 x a s)
  have \<open>(x ::= a, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc (step_cost (x ::= a) s)\<^esup> (SKIP, s(x := aval a s), 0)\<close>
    using atomic_ex by auto
  then show ?case 
    by (metis "2" Pair_inject atomic_step_t_deterministic small_step.Assign) 
next
  case (3 c1 c2 s)
  then show ?case sorry
qed auto
*)

lemma atomic_imp_small: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m') \<Longrightarrow> (s = s' \<or> (c, s) \<rightarrow> (c',s'))"
  apply (induction c s m c' s' m' rule: atomic_step_GC_induct) apply auto
proof -
  fix x :: "char list" and a :: aexp and sa :: "char list \<Rightarrow> nat"
  assume "\<not> (x ::= a, sa) \<rightarrow> (SKIP, \<lambda>b. if b = x then aval a sa else sa b)"
  then have "\<not> (x ::= a, sa) \<rightarrow> (SKIP, sa(x := aval a sa))"
    by (simp add: fun_upd_def)
  then show "sa = (\<lambda>b. if b = x then aval a sa else sa b)"
    by (metis small_step.Assign)
qed


text "Equivalence statement. We have a difference of 1 between big step and small step semantics
because in small step semantics, we count the number of times transformation rules have to be applied
until a configuration (SKIP, s') is reached, while in big step semantics the time for each step including
the last command is fully considered."
(*
lemma equiv_atomic_small_pair:
 "(c,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> Suc (step_cost c s) \<^esup> (c',s',0) \<longleftrightarrow> (c, s) \<rightarrow> (c',s')"
  using small_to_atomic_helper atomic_to_small by metis

lemma equiv_atomic_small:
 "(c,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> Suc (step_cost c s) \<^esup> (c',s',0) = (c, s) \<rightarrow> (c',s')"
  using equiv_atomic_small_pair by blast


lemma atomic_step_cant_run_longer_than_big_step: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t' \<^esup> (c'', s'',0)
  \<Longrightarrow> t' \<le> t"
proof(rule ccontr)
  assume "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'" "(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t'\<^esup> (c'', s'',0)" "\<not> t' \<le> t"
  obtain t'' where "t = t'' + skip_costs s" 
    using \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'\<close> bigstep_progress gr0_implies_Suc 
    by (meson at_least_skip_costs)
  hence "(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t'' \<^esup> (SKIP, s',0)"
    using equiv_atomic_big_pair \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'\<close> by auto
  have "t'' < t'" 
    using \<open>t = t'' + skip_costs s\<close> \<open>\<not> t' \<le> t\<close> 
    by simp
  thus False
    using atomic_step_cant_continue_after_reaching_SKIP_0 \<open>(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t'' \<^esup> (SKIP, s',0)\<close>
        \<open>(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c'', s'',0)\<close>
    by fastforce
qed
*)
end
end