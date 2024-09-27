\<^marker>\<open>creator Florian Kessler\<close>

theory Generalized_Memory
imports Big_Step_Atomic_Step_Equivalence Small_Step_Atomic_Step_Equivalence "HOL-Library.Discrete" "Max_Constant_GC" "../Memory" "HOL-Library.Landau_Symbols"
begin

context BS_Generalized_Cost begin

text \<open> We define something to be a memory bound for a program and an initial state, if it
       bounds every state that is reachable. \<close>

definition is_memory_bound_GC :: "com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool" where
"is_memory_bound_GC c s n \<equiv> (\<forall> t c' s'. (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', 0) \<longrightarrow> state_memory c' s' \<le> n)"

lemma memory_bound_to_small_step: "is_memory_bound_GC c s n \<equiv> is_memory_bound c s n"
proof-
  have "is_memory_bound_GC c s n \<Longrightarrow> is_memory_bound c s n"
  using is_memory_bound_GC_def is_memory_bound_def apply auto
  by (meson small_atomic_same_comp)
  moreover have \<open>is_memory_bound c s n \<Longrightarrow> is_memory_bound_GC c s n\<close>
    using is_memory_bound_GC_def is_memory_bound_def apply auto
    by (metis atomic_small_same_comp)
  ultimately show \<open>is_memory_bound_GC c s n \<equiv> is_memory_bound c s n\<close>
    by argo
qed


lemma finite_range_stays_finite_step: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c2, s2, m2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> finite (range s2)"
  apply (induction c1 s1 m1 c2 s2 m2 rule: atomic_step_GC_induct)
         apply auto
  by (meson rev_finite_subset subset_image_iff top_greatest)

lemma finite_range_stays_finite: "(c1, s1, m1)  \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c2, s2, m2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> finite (range s2)"
  apply(induction t arbitrary: c1 s1 m1)
   using finite_range_stays_finite_step by auto

lemma one_step_Max_increase: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c2, s2, m2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> Max (range s2) \<le> 2 * (max (Max (range s1)) (max_constant c1))"
proof (induction c1 s1 m1 c2 s2 m2 rule: atomic_step_GC_induct)
  case (2 x a s)
  then show ?case
  proof (cases a)
    case (A x1)
    then show ?thesis
      using \<open>finite (range s)\<close>
      by (cases x1; fastforce simp: numeral_2_eq_2 trans_le_add1 intro: Max_insert_le_when)
  next
    case (Plus x1 x2)
    then show ?thesis
      using \<open>finite (range s)\<close>
      apply(cases x1; cases x2; auto simp only: intro!: Max_insert_le_when)
      by(auto simp add: numeral_2_eq_2 max.coboundedI1 intro!: add_le_mono)
  next
    case (Sub x1 x2)
    then show ?thesis
      using \<open>finite (range s)\<close>
      apply(cases x1; cases x2; auto simp only: intro!: Max_insert_le_when)
      by(auto simp: numeral_2_eq_2 max.coboundedI1 
              intro!: le_then_sub_le trans_le_add1)
  next
    case (Parity x1)
    then show ?thesis
    proof (cases x1)
      case (N x1)
      then show ?thesis 
        using \<open>finite (range s)\<close> Parity
        apply (auto simp only: intro!: Max_insert_le_when)
        by auto
    next
      case (V x2)
      then show ?thesis
        using \<open>finite (range s)\<close> Parity
        by(fastforce simp add: numeral_2_eq_2 
                     intro!: trans_le_add1 Max_insert_le_when
                     intro: le_trans[where ?j="s x2"])
    qed
  next
    case (RightShift x1)
    then show ?thesis
    proof (cases x1)
      case (N x1)
      then show ?thesis 
        using \<open>finite (range s)\<close> RightShift
        apply (auto simp only: intro!: Max_insert_le_when)
        by auto
    next
      case (V x2)
      then show ?thesis
        using \<open>finite (range s)\<close> RightShift
        by(fastforce simp add: numeral_2_eq_2 
                     intro!: trans_le_add1 Max_insert_le_when 
                     intro: le_trans[where ?j="s x2"])
    qed
  qed
next
  case (4 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case by simp
qed (linarith)+

lemma Max_increase: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c2, s2, m2) \<Longrightarrow> finite (range s1) 
  \<Longrightarrow> Max (range s2) \<le> (2 ^ t) * (max (Max (range s1)) (max_constant c1))"
proof (induction t arbitrary: c1 s1 m1)
  case (Suc t)
  obtain c1' s1' m1' where "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c1', s1', m1')" "(c1', s1', m1') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c2, s2, m2)"
    using \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c2, s2, m2)\<close>
    by auto
  have "Max (range s2) \<le> (2 ^ t) * (max (Max (range s1')) (max_constant c1'))"
    using Suc.IH \<open>finite (range s1)\<close>
      \<open>(c1', s1', m1') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c2, s2, m2)\<close> \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c1', s1', m1')\<close> 
      finite_range_stays_finite_step 
    by blast
  also have "... \<le> (2 ^ t) * 
    (max (2 * (max (Max (range s1)) (max_constant c1))) (max_constant c1'))"
    using one_step_Max_increase[OF \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c1', s1', m1')\<close> \<open>finite (range s1)\<close>]
    by simp
  also have "... \<le> (2 ^ Suc t) *
      (max (max (Max (range s1)) (max_constant c1))) (max_constant c1')"
    by simp
  also have "... \<le> (2 ^ Suc t) * max (Max (range s1)) (max_constant c1)"
    using max_constant_not_increasing_step[OF \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c1', s1', m1')\<close>]
    by simp
  finally show ?case by simp
qed auto

text \<open> We show that there always is a linear bound for the memory consumption. \<close>

lemma linear_bound: "(c1, s1) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s2 \<Longrightarrow> finite (range s1)
  \<Longrightarrow> is_memory_bound_GC c1 s1 ((num_variables c1) 
      * (t + bit_length (max 1 (max (Max (range s1)) (max_constant c1)))))"
proof -
  let ?b = "(num_variables c1) 
      * (t + bit_length (max 1 (max (Max (range s1)) (max_constant c1))))"

  assume "(c1, s1) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s2" "finite (range s1)"

  have "(c1, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c', s', 0) \<Longrightarrow> state_memory c' s' \<le> ?b" for t' c' s' 
  proof -
    assume "(c1, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c', s', 0)"
    hence "finite (range s')"
      using \<open>finite (range s1)\<close> finite_range_stays_finite
      by auto

    have "Max (range s') \<le> (2 ^ t') * (max (Max (range s1)) (max_constant c1))"
      using Max_increase \<open>(c1, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c', s', 0)\<close> \<open>finite (range s1)\<close> 
      by auto
    also have "... \<le> (2 ^ t) * (max (Max (range s1)) (max_constant c1))"
      using atomic_step_cant_run_longer_than_big_step
        \<open>(c1, s1) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s2\<close> \<open>(c1, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c', s', 0)\<close>
      by simp

    finally have "state_memory c' s' \<le> num_variables c' 
          * bit_length ((2 ^ t) * (max (Max (range s1)) (max_constant c1)))" 
      using Max_register_bounds_state_memory[OF \<open>finite (range s')\<close>]
      by (meson bit_length_monotonic dual_order.trans mult_le_cancel1)
    also have "... \<le>  num_variables c' 
          * bit_length ((2 ^ t) * (max 1 (max (Max (range s1)) (max_constant c1))))"
      using bit_length_monotonic
      by simp          

    finally show "state_memory c' s' \<le> ?b"
      using num_variables_not_increasing[OF \<open>(c1, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> (c', s', 0)\<close>] order_trans
      by(fastforce simp: bit_length_of_power_of_two)
  qed
  thus ?thesis by(auto simp: is_memory_bound_GC_def)
qed

lemma linear_bound': "(c1, s1) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s2 \<Longrightarrow> (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP,s2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> is_memory_bound c1 s1 ((num_variables c1) 
      * (Suc t' + bit_length (max 1 (max (Max (range s1)) (max_constant c1)))))"
  by (meson Memory.linear_bound small_to_big)

corollary linear_bound'_atomic: "(c1, s1) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s2 \<Longrightarrow> (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP,s2) \<Longrightarrow> finite (range s1)
  \<Longrightarrow> is_memory_bound_GC c1 s1 ((num_variables c1) 
      * (Suc t' + bit_length (max 1 (max (Max (range s1)) (max_constant c1)))))"
  using linear_bound' memory_bound_to_small_step by blast

inductive
  the_cheapest_assign :: "com \<times> state \<Rightarrow> aexp \<times> state \<Rightarrow> bool" ("_ \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A _" 55) 
  (* up to, and including this computation point *)
  where
  (* this is funny and probably unwanted, can be solved by dedicating a state to have 0
     skip costs without influencing the semantics *)
SkipTCA: "(SKIP,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (A(N 0), s)"|
AssignTCA: "(x ::= a,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a,s)" |
SeqTCA: "\<lbrakk>(c1,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2;  (c2,s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3 ; C3 = C1 + C2; (c1,s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1) ; (c2,s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2,sa2)\<rbrakk> 
   \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (if(assign_costs a1 sa1 \<le> assign_costs a2 sa2) then (a1,sa1) else (a2,sa2))" |
IfTrueTCA: "\<lbrakk>s b \<noteq> 0; (c1,s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1)\<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1)" |
IfFalseTCA: "\<lbrakk> s b = 0; (c2,s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2,sa2)\<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2,sa2)" |
WhileFalseTCA: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (A(N 0), s)" |
WhileTrueTCA: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3; C3 = C1 + C2 + 1; 
             (c,s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1) ; (WHILE b \<noteq>0 DO c,s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2,sa2)\<rbrakk> 
          \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (if(assign_costs a1 sa1 \<le> assign_costs a2 sa2) then (a1,sa1) else (a2,sa2))" 

lemmas the_cheapest_assign_induct = the_cheapest_assign.induct[split_format(complete), OF BS_Generalized_Cost_axioms, consumes 1]

subsubsection\<open>Proof automation\<close>

declare the_cheapest_assign.intros[simp,intro]

text\<open>Rule inversion:\<close>

inductive_cases SkipTCAE[elim!]: "(SKIP,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca"
inductive_cases AssignTCAE[elim!]: "(x::=a,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca"
inductive_cases SeqTCAE[elim]: "(c1;;c2,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca"
inductive_cases IfTCAE[elim!]: "(IF b\<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca"
inductive_cases WhileTCAE[elim]: "(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca"


abbreviation "aexp_cost_decurried x \<equiv> aexp_cost (fst x) (snd x)"

lemma THE_ca: "(c, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s' \<Longrightarrow> \<exists>ca . (c,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca"
proof (induction c s t s' rule: big_step_tG_induct)
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  then show ?case by fast
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  obtain ca sa wa wsa  where "(c, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (ca, sa)" "(WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (wa, wsa)"
    using "7.IH"(1) "7.IH"(2) by auto
  then show ?case apply (cases "(assign_costs ca sa\<ge> assign_costs wa wsa)")
    using "7.hyps"(1) "7.hyps"(2) "7.hyps"(3) apply blast
    using "7.hyps"(1) "7.hyps"(2) "7.hyps"(3) by blast
qed auto

lemma tca_correct: "(c,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a,sa) \<Longrightarrow> (c, s) \<rightarrow>\<^bsup>ta\<^esup> ((x ::= a');;ca,sa') 
                \<Longrightarrow> (c, s) \<rightarrow>\<^bsup>t\<^esup> (SKIP,s') \<Longrightarrow> assign_costs a sa \<le> assign_costs a' sa'"
proof(induction c s a sa arbitrary: ta x a' ca sa' t s' rule: the_cheapest_assign_induct)
  case (1 s)
  then show ?case 
        apply auto
    by (metis Small_StepT.SkipE com.distinct(3) old.prod.inject rel_pow.simps)
next
  case (2 xa a s)
  from 2 have "(xa ::= a, s) \<rightarrow> (SKIP, s(xa := aval a s))"
    by simp
  from this \<open>(xa ::= a, s) \<rightarrow>\<^bsup>ta\<^esup> (x ::= a';; ca, sa')\<close> have False 
    by (metis "2.prems"(2) big_step_t.Assign big_step_t_determ2 com.distinct(3) com.distinct(9) nless_le not_less_eq old.prod.inject small_step_cant_continue_after_reaching_SKIP small_step_progress small_step_t_deterministic small_to_big)
  then show ?case by simp
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3 a1 sa1 a2 sa2)
  then show ?case sorry
next
  case (4 s b c1 s1 a1 sa1 c2)
  then show ?case sorry
next
  case (5 s b c2 s2 a2 sa2 c1)
  then show ?case sorry
next
  case (6 s b c)
  then show ?case sorry
next
  case (7 s1 b c C1 s2 C2 s3 C3 a1 sa1 a2 sa2)
  then show ?case sorry
qed

lemma least_aexp[simp]: "aexp_cost (A(N 0)) s = 0"
  by simp

lemma tca_SKIP[simp]: "(THE a. (SKIP, s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a) = ((A(N 0)), s)"
  by blast

lemma tca_Assign[simp]: "(THE b. (x ::= a,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A b) = (a, s)"
  by blast

lemma tca_cost_deterministic: "cs \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A tca \<Longrightarrow> cs \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A tca' \<Longrightarrow> tca = tca'"
  apply (induction cs tca arbitrary: tca' rule: the_cheapest_assign.induct)
        apply blast
       apply auto[1]
  sorry


(*Possible solutions:
 -Define the input size of a state and work with O notation.
 -Concretely calculate the bound (sum of all assigns)
 -Amortization would work but does it make sense?*)


lemma the_last_skip_of_bs: "(c, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<exists>t'. (c, s) \<Rightarrow>\<^bsup>Suc t'\<^esup> s'"
  apply (induction c s t s' rule: big_step_t_induct) apply auto
subgoal proof -
  fix x :: "char list" and a :: aexp and sa :: "char list \<Rightarrow> nat"
  have f1: "\<forall>cs a f. (cs ::= a, f) \<Rightarrow>\<^bsup> Suc (Suc 0) \<^esup> f (cs := aval a f)"
    using big_step_t.Assign by moura
  have "sa(x := aval a sa) = (\<lambda>cs. if cs = x then aval a sa else sa cs)"
    by auto
  then have "\<exists>n. (x ::= a, sa) \<Rightarrow>\<^bsup> Suc n \<^esup> \<lambda>cs. if cs = x then aval a sa else sa cs"
    using f1 by metis
  then show "\<exists>n. (x ::= a, sa) \<Rightarrow>\<^bsup> Suc n \<^esup> \<lambda>cs. if cs = x then aval a sa else sa cs"
    by (smt (z3))
qed
  apply fastforce[3]
  apply fastforce
  apply fastforce
  by force

lemma least_factor: " (c, s) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s' \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup> t'\<^esup> s'
  \<Longrightarrow> \<exists>n. (x \<ge> n) 
   \<Longrightarrow> (f x) \<le> assign_costs (fst (THE ca. (c,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca)) (snd  (THE ca. (c,s) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A ca))
      \<Longrightarrow> t' * f x \<le> t + 1 "
proof(induction c s t s' arbitrary: t' x f rule: big_step_tG_induct)
  case (1 s)
  then show ?case by auto 
next
  case (2 xa a s)
  then show ?case apply auto 
    sorry
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  from THE_ca[OF \<open>(c1, s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2\<close>]
  THE_ca[OF \<open>(c2, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3\<close>]
  obtain a1 sa1 a2 sa2 where \<open>(c1,s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1)\<close> \<open>(c2,s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2,sa2)\<close>
    by auto
  then show ?case 
  proof (cases "assign_costs a1 sa1 \<le> assign_costs a2 sa2 ")
    case True
    from SeqTCA[OF \<open>(c1, s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2\<close> \<open>(c2, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3\<close> \<open>C3 = C1 + C2\<close>
         \<open>(c1,s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1)\<close> \<open>(c2,s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2,sa2)\<close>] True
    have \<open> (c1;; c2, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1,sa1)\<close> by auto
    from \<open>(c1;; c2, s1) \<Rightarrow>\<^bsup>  t' \<^esup> s3\<close>
    obtain C1'' C2''  s2' where \<open>(c1, s1) \<Rightarrow>\<^bsup>  C1'' \<^esup> s2'\<close>  \<open>(c2, s2') \<Rightarrow>\<^bsup>  C2'' \<^esup> s3\<close> \<open>t' = C1'' + C2''\<close>
      using big_step_tG_t_same_comp by blast
    have \<open>s2 = s2'\<close> 
      by (meson "3.hyps"(1) \<open>(c1, s1) \<Rightarrow>\<^bsup> C1'' \<^esup> s2'\<close> big_step_tG_t_same_comp local.bigstep_det)
    hence \<open>(c1, s1) \<Rightarrow>\<^bsup> C1'' \<^esup> s2\<close>  \<open>(c2, s2) \<Rightarrow>\<^bsup> C2'' \<^esup> s3\<close> 
       apply (simp add: \<open>(c1, s1) \<Rightarrow>\<^bsup>  C1'' \<^esup> s2'\<close>)
      by (simp add: \<open>(c2, s2') \<Rightarrow>\<^bsup>   C2'' \<^esup> s3\<close> \<open>s2 = s2'\<close>)
    from \<open>f x \<le> assign_costs (fst (THE a. (c1;; c2, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a))
        (snd (THE a. (c1;; c2, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a))\<close>
    have \<open>f x \<le> assign_costs (fst (THE a. (c1, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a)) (snd (THE a. (c1, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a))\<close>     
        by (metis (no_types, lifting) BS_Generalized_Cost.tca_cost_deterministic BS_Generalized_Cost_axioms \<open>(c1, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1, sa1)\<close> \<open>(c1;; c2, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1, sa1)\<close> the_equality)
    from "3.IH"(1)[OF \<open>(c1, s1) \<Rightarrow>\<^bsup>  C1'' \<^esup> s2\<close> \<open>\<exists>n. n \<le> x\<close>] this 
    have \<open>(C1''- 1) * f x \<le> C1 - 1\<close> by blast
    hence \<open>(C1''- 1) * f x \<le> C1\<close> 
      by simp
    have \<open>f x \<le> assign_costs (fst (THE a. (c2, s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a)) (snd (THE a. (c2, s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a))\<close>
      by (smt (verit, del_insts) BS_Generalized_Cost.tca_cost_deterministic BS_Generalized_Cost_axioms True \<open>(c1, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a1, sa1)\<close> \<open>(c2, s2) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A (a2, sa2)\<close> \<open>f x \<le> assign_costs (fst (THE a. (c1, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a)) (snd (THE a. (c1, s1) \<Rightarrow>\<^sub>T\<^sub>C\<^sub>A a))\<close> fst_conv le_trans snd_conv the_equality)
    from "3.IH"(2)[OF \<open>(c2, s2) \<Rightarrow>\<^bsup>   C2'' \<^esup> s3\<close> \<open>\<exists>n. n \<le> x\<close>] this 
    have \<open> C2'' * f x \<le> C2 - 1\<close> sorry
    have \<open>C1 > 0\<close> \<open>C2 > 0\<close> using bigstep_progress[OF \<open>(c1, s1) \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2\<close>]
          bigstep_progress[OF \<open>(c2, s2) \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3\<close>] by simp+
    from \<open>C1 > 0\<close> \<open>C2 > 0\<close> \<open> C2'' * f x \<le> C2 - 1\<close> \<open> C1'' * f x \<le> C1 - 1\<close> have \<open>C1' * f x + C2' * f x \<le> C1 + C2 - 1 - 1\<close>
      by simp
    hence \<open>C1' * f x + C2' * f x  + 1  - 1 \<le> C1 + C2 - 1 - 1\<close> by simp
    hence \<open>C1' * f x + C2' * f x  + 1  \<le> C1 + C2 - 1 \<close> using \<open>C1 > 0\<close> \<open>C2 > 0\<close>
      by simp
    then show ?thesis 
  next
    case False
    then show ?thesis sorry
  qed
next
  case (4 s b c1 C t C' c2)
  then show ?case sorry
next
  case (5 s b c2 C t C' c1)
  then show ?case sorry
next
  case (6 s b c)
  then show ?case sorry
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  then show ?case sorry
qed




end
end
