\<^marker>\<open>creator Florian Keßler\<close>

section "IMP- Max Constant"

theory Max_Constant_GC
  imports "Atomic_StepT_GC" "../Max_Constant"
begin


text \<open>We define functions to derive the constant with the highest value and enumerate all variables 
  in IMP- programs. \<close>

context BS_Generalized_Cost begin

lemma max_constant_not_increasing_step:
  "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c2, s2, m2) \<Longrightarrow> max_constant c2 \<le> max_constant c1"
  by (induction c1 s1 m1 c2 s2 m2 rule: atomic_step_GC_induct) auto

lemma all_variables_subset_step: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c2, s2, m2)  
  \<Longrightarrow> set (all_variables c2) \<subseteq> set (all_variables c1)" 
  apply(induction c1 s1 m1 c2 s2 m2 rule: atomic_step_GC_induct)
  by auto

lemma num_variables_not_increasing_step: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c2, s2, m2)
  \<Longrightarrow> num_variables c2 \<le> num_variables c1" 
  apply(induction c1 s1 m1 c2 s2 m2 rule: atomic_step_GC_induct)
  using subset_then_length_remdups_le[OF all_variables_subset_step] 
        apply(auto simp: num_variables_def length_remdups_card_conv)
        apply (meson List.finite_set card_mono finite_Un sup.cobounded1 sup.cobounded2 le_SucI)+
  by (simp add: insert_absorb)

lemma num_variables_not_increasing: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (c2, s2, m2)
  \<Longrightarrow> num_variables c2 \<le> num_variables c1" 
proof (induction t arbitrary: c1 s1 m1)
  case (Suc t)
  then obtain c3 s3 m3 where "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c3, s3, m3)" "(c3, s3, m3) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>  t \<^esup> (c2, s2, m2)"
    by auto
  then show ?case
    using num_variables_not_increasing_step[OF \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c3, s3, m3)\<close>] 
      Suc.IH[OF \<open>(c3, s3, m3) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>  t \<^esup> (c2, s2, m2)\<close>]
    by simp
qed auto


end
end