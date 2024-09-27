theory AExp_Order imports Main "../Aexp" Big_StepT_Generalized_Cost_Final begin



datatype assign_pair = AP aexp state


instantiation assign_pair :: order
begin

fun less_eq_assign_pair :: "assign_pair \<Rightarrow> assign_pair \<Rightarrow> bool" where
 "(AP a1 s1) \<le> (AP a2 s2)= ((assign_costs a1 s1) \<le> (aval a2 s2))" 

definition less_assign_pair :: "assign_pair \<Rightarrow> assign_pair \<Rightarrow> bool" where
  "(ap1 :: assign_pair) < ap2 \<equiv> (ap1 \<le> ap2 \<and> \<not> ap2 \<le> ap1)"

instance 
proof (standard, goal_cases)
  case (1 x y)
  then show ?case 
    by (simp add: less_assign_pair_def)
next
  case (2 x)
  then show ?case by (induction x) auto
next
  case (3 x y z)
  then show ?case apply (induction x y arbitrary: z rule:less_eq_assign_pair.induct)
    apply auto 
    using less_eq_assign_pair.elims(3) by fastforce
next
  case (4 x y)
  then show ?case apply (induction x y  rule: less_eq_assign_pair.induct) apply auto
    try
qed

end

end

end