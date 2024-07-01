\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "Equivalence of big step and small step semantics"

theory Big_Step_Atomic_Step_Equivalence imports "../Big_Step_Small_Step_Equivalence" Small_Step_Atomic_Step_Equivalence Big_StepT_Generalized_Cost_Final Atomic_StepT_GC begin

paragraph "Introduction"
text "We show that the big and small step semantics with time we defined for IMP- are equivalent."

context BS_Generalized_Cost begin

text "from Big step to small step semantics"
lemma big_to_small_helper: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s' \<Longrightarrow> t =  t' + skip_costs s' \<Longrightarrow> (c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t' \<^esup> (SKIP, s',0)"
proof (induction arbitrary: t' rule: big_step_tG_induct)
  case (1 s)
  then show ?case by auto
next
  case (2 x a s)
  have "t' = aexp_cost a s + 1" 
    using "2" 
    by (metis Nat.add_diff_assoc2 add_diff_cancel_right' le_add2 skip_cost_var_names)
  then show ?case 
    using Assing_ex by blast
next
  case (3 c1 s1 x s2 c2 y s3 z)
  then obtain x' y' where suc_ex: "x = x' + skip_costs s2" "y = y' + skip_costs s3"
    by (meson at_least_skip_costs)
  then have "(c1, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> x' \<^esup> (SKIP, s2, 0)" using 3 by auto
  moreover have "(c2, s2, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> y' \<^esup> (SKIP, s3, 0)" using 3 suc_ex by auto
  ultimately have "(c1 ;; c2, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> (x' + y' + skip_costs s2) \<^esup> (SKIP, s3, 0)" using seq_comp by simp  
  hence "t' = x' + y' + skip_costs s2" 
    using "3.hyps"(3) "3.prems" suc_ex(1) suc_ex(2) by auto
  then show ?case using 3 suc_ex 
    using local.seq_comp by force
next
  case (4 s b c1 x t y c2)
  then obtain x' where "x = x' + skip_costs t" using  gr0_implies_Suc 
    by (meson at_least_skip_costs)
  then show ?case using 4 by auto
next
  case (5 s b c1 x t y c2)
  then obtain x' where "x = x' + skip_costs t" using  gr0_implies_Suc 
    by (meson at_least_skip_costs)
  then show ?case using 5 by auto
next
  case (6 s b c)
  then show ?case by auto
next
  case (7 s1 b c x s2 y s3 z)
  let ?w = "WHILE b \<noteq>0 DO c"
  obtain x' y' where suc_def:"x = x' + skip_costs s2" "y =  y' + skip_costs s3"
    using  "7.hyps"(2) "7.hyps"(3) bigstep_progress gr0_implies_Suc 
    using at_least_skip_costs 
    by meson
  have "(?w, s1,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> 1 \<^esup> (c ;; ?w, s1, 0)" using 7 by auto
  moreover have "(c ;; ?w, s1,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> x' \<^esup> (SKIP ;; ?w, s2,0)" 
    using 7 suc_def star_seq2  by simp
  moreover have "(SKIP ;; ?w, s2, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> skip_costs s2 \<^esup>(?w, s2, 0)" 
    using atomic_ex by auto
  moreover have "(?w, s2, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> y' \<^esup> (SKIP, s3, 0)" using 7 \<open>y =  y' + skip_costs s3\<close> by blast
  ultimately have "(?w, s1,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>  1 + x' + skip_costs s2  + y'\<^esup> (SKIP, s3, 0)" 
    by (meson rel_pow_sum)
  moreover have "t' = 1 + x' + skip_costs s2  + y' " using 7 suc_def by auto 
  ultimately show ?case by simp
qed

lemma big_to_small: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t + skip_costs s' \<^esup> s' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (SKIP, s', 0)"
  using big_to_small_helper by blast

text "from atomic to big semantics"

lemma small1_bigGC_continue:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> (c',s') \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> cs'' \<Longrightarrow> (c,s) \<Rightarrow>\<^sub>G\<^bsup> t + Suc (step_cost c s) \<^esup> cs''"
proof (induction c s  c' s' arbitrary: cs'' t rule: small_step_induct)
  case (Assign x a s)
  have \<open>(SKIP, s(x := aval a s)) \<Rightarrow>\<^sub>G\<^bsup> skip_costs (s(x := aval a s))\<^esup> s(x := aval a s)\<close>
    by simp
  hence \<open>t =  skip_costs (s(x := aval a s))\<close> \<open>cs'' = s(x := aval a s)\<close>
    apply (meson BS_Generalized_Cost.bigstep_det BS_Generalized_Cost_axioms local.Assign)
    using local.Assign by blast
  then show ?case 
    by (smt (verit, ccfv_SIG) Suc_eq_plus1 add.assoc add.left_commute local.ASSnot skip_costs_name step_cost.simps(2))
next
  case (Seq1 c\<^sub>2 s)
  then show ?case apply auto 
    by (simp add: big_step_tG.Seq)
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case apply auto 
    by (smt (verit) add.assoc add.commute add_Suc_right big_step_tG.Seq)
next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  then show ?case
    by (simp add: big_step_tG.IfTrue)
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  then show ?case 
    by (simp add: big_step_tG.IfFalse)
next
  case (WhileTrue s b c)
  then show ?case 
    using big_step_tG.WhileTrue by force
next
  case (WhileFalse s b c)
  then show ?case 
    using big_step_tG.WhileFalse by fastforce
qed

lemma successor: "c \<noteq> SKIP \<Longrightarrow> \<exists>c' s' m' . (c,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c',s',m')"
proof(induction c arbitrary: s m)
  case SKIP
  then show ?case by auto
next
  case (Assign x1 x2)
  then show ?case 
    by (metis atomic_ex atomic_step_GC.Assign not0_implies_Suc stepE surj_pair)
next
  case (Seq c1 c2)
  then show ?case apply(cases "c1 = SKIP")
    apply auto
    apply(cases "c2 = SKIP")
      apply auto
      apply (metis atomic_step_GC.Seq1 atomic_step_GC.atomic_step old.nat.exhaust)
     apply (metis atomic_step_GC.Seq1 atomic_step_GC.atomic_step not0_implies_Suc)
    by blast
next
  case (If b c1 c2)
  then show ?case 
    apply (cases "s b = 0")
    apply auto
    apply(cases "c1 = SKIP")
    apply auto
    apply(cases "c2 = SKIP")
       apply auto
       apply (metis atomic_step_GC.IfFalse atomic_step_GC.atomic_step not0_implies_Suc)
      apply (metis atomic_backtrack1 atomic_step_GC.IfFalse atomic_step_GC.atomic_step)
     apply (metis BS_Generalized_Cost.atomic_step_GC.IfFalse BS_Generalized_Cost_axioms atomic_step_GC.atomic_step bot_nat_0.not_eq_extremum gr0_conv_Suc)
    by (metis BS_Generalized_Cost.atomic_step_GC.IfTrue BS_Generalized_Cost_axioms atomic_step_GC.atomic_step bot_nat_0.not_eq_extremum gr0_conv_Suc)
next
  case (While b c)
  then show ?case 
    apply (cases "s b = 0")
    apply auto
     apply(cases "c = SKIP")
      apply auto
      apply (metis atomic_step_GC.WhileFalse atomic_step_GC.atomic_step old.nat.exhaust)
     apply (metis BS_Generalized_Cost.atomic_step_GC.WhileFalse BS_Generalized_Cost_axioms atomic_step_GC.atomic_step bot_nat_0.not_eq_extremum gr0_implies_Suc)
    by (metis atomic_step_GC.WhileTrue atomic_step_GC.atomic_step gr0_implies_Suc old.nat.exhaust)
qed

lemma atomic1_big_continue:
  "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m') \<Longrightarrow> (c', s') \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup> t + (if m = 0 then Suc m' else 0) \<^esup> s''"
proof (induction  arbitrary: s'' t rule: atomic_step_GC_induct )
  case (1 c s n)
  then show ?case by auto
next
  case (2 x a s)
  then show ?case 
    by (smt (verit, del_insts) small1_bigGC_continue small_step.Assign step_cost.simps(2))
next
  case (3 c\<^sub>2 s)
  then show ?case apply auto 
    by (simp add: big_step_tG.Seq)
next
  case (4 c\<^sub>1 s m c\<^sub>1' s' m' c\<^sub>2)
  then show ?case apply auto subgoal 
      by (smt (verit) add.assoc add.commute big_step_tG.Seq plus_1_eq_Suc)
    using big_step_tG.Seq by blast
next
  case (5 s b c\<^sub>1 c\<^sub>2)
  then show ?case apply auto 
    by (simp add: big_step_tG.IfTrue)
next
  case (6 s b c\<^sub>1 c\<^sub>2)
  then show ?case apply auto 
    by (simp add: big_step_tG.IfFalse)
next
  case (7 s b c)
  then show ?case apply auto 
    using While_tE' by auto
next
  case (8 s b c)
  then show ?case  apply auto 
   using big_step_tG.WhileFalse by auto
qed

corollary atomic1_big_continue0:
  "(c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', 0) \<Longrightarrow> (c', s') \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup> Suc t \<^esup> s''"
  using atomic1_big_continue by fastforce


lemma atomic_to_big':
 "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (SKIP, s', 0) \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup> t - m + skip_costs s'\<^esup> s'"
proof (induction t arbitrary: c s s' m)
  case 0
  then show ?case by auto
next
  case (Suc t)
  from \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (SKIP, s', 0)\<close>
  obtain c'' s'' m''  where
    \<open>(c,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'',s'',m'')\<close> \<open>(c'',s'',m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s', 0)\<close>
    by auto
  from Suc.IH[OF \<open>(c'',s'',m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s', 0)\<close>]
  have \<open>(c'', s'') \<Rightarrow>\<^sub>G\<^bsup> t - m''  + skip_costs s' \<^esup> s'\<close> by auto
  from atomic1_big_continue[OF \<open>(c,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'',s'',m'')\<close> this]
  have \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t - m'' + skip_costs s' + (if m = 0 then Suc m'' else 0) \<^esup> s'\<close> by simp
  then show ?case proof(cases "m = 0")
    case True
    from \<open>(c'',s'',m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s', 0)\<close> have \<open>t \<ge> m''\<close>
      by (meson atomic_ex atomic_step_cant_continue_after_reaching_SKIP_0)
    hence \<open>t - m'' + skip_costs s' + Suc m'' = t  + skip_costs s' + Suc m''- m'' \<close>
      by simp
    hence \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t  + skip_costs s' + Suc m'' - m'' \<^esup> s'\<close>
      using True \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t - m'' + skip_costs s' + (if m = 0 then Suc m'' else 0) \<^esup> s'\<close> by auto
    then show ?thesis 
      using True by auto
  next
    case False
    from \<open>(c,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'',s'',m'')\<close> False have \<open>m = Suc m''\<close> 
      by (meson atomic_backtrack1)
    from \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t - m'' + skip_costs s' + (if m = 0 then Suc m'' else 0) \<^esup> s'\<close> 
    have \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> Suc t - Suc m'' + skip_costs s' + (if m = 0 then Suc m'' else 0) \<^esup> s'\<close>
      by simp
    then show ?thesis 
      by (simp add: \<open>m = Suc m''\<close>)
  qed
qed

corollary atomic_to_big:
 "(c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (SKIP, s', 0) \<Longrightarrow> (c, s) \<Rightarrow>\<^sub>G\<^bsup> t + skip_costs s'\<^esup> s'"
  using atomic_to_big' by fastforce

text "Equivalence statement. We have a difference of 1 between big step and small step semantics
because in small step semantics, we count the number of times transformation rules have to be applied
until a configuration (SKIP, s') is reached, while in big step semantics the time for each step including
the last command is fully considered."
lemma equiv_atomic_big_pair:
 "(c,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (SKIP,s',0) \<longleftrightarrow> (c,s) \<Rightarrow>\<^sub>G\<^bsup> t + skip_costs s'\<^esup> s' "
  using big_to_small  by (metis Nat.add_0_right atomic_to_big)

lemma equiv_atomic_big:
 "(c,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (SKIP,s',0) = (c,s) \<Rightarrow>\<^sub>G\<^bsup> t + skip_costs s'\<^esup> s' "
  using equiv_atomic_big_pair by blast

lemma atomic_step_cant_run_longer_than_big_step: "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t' \<^esup> (c'', s'',0)
  \<Longrightarrow> t' \<le> t"
proof(rule ccontr)
  assume "(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'" "(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t'\<^esup> (c'', s'',0)" "\<not> t' \<le> t"
  obtain t'' where "t = t'' + skip_costs s'" 
    using \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'\<close> bigstep_progress gr0_implies_Suc 
    by (meson at_least_skip_costs)
  hence "(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t'' \<^esup> (SKIP, s',0)"
    using equiv_atomic_big_pair \<open>(c, s) \<Rightarrow>\<^sub>G\<^bsup> t \<^esup> s'\<close> by auto
  have "t'' < t'" 
    using \<open>t = t'' + skip_costs s'\<close> \<open>\<not> t' \<le> t\<close> 
    by simp
  thus False
    using atomic_step_cant_continue_after_reaching_SKIP_0 \<open>(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t'' \<^esup> (SKIP, s',0)\<close>
        \<open>(c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c'', s'',0)\<close>
    by fastforce
qed
end

end