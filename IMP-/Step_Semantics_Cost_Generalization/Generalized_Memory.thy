\<^marker>\<open>creator Florian Kessler\<close>

theory Generalized_Memory
  imports Big_Step_Atomic_Step_Equivalence Small_Step_Atomic_Step_Equivalence "HOL-Library.Discrete" "Max_Constant_GC" "../Memory"
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

lemma small_steps_of_GC: "(c1, s1) \<Rightarrow>\<^sub>G\<^bsup>t\<^esup> s2 \<Longrightarrow> \<exists>t' . (c1, s1) \<rightarrow>\<^bsup>t'\<^esup> (SKIP,s2) \<and> t' *  "

end
end
