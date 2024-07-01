theory Vars_for_GC imports "../Vars" Big_StepT_Generalized_Cost_Final "../Eq_On"

begin

sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

context BS_Generalized_Cost begin

lemma var_unchanged: "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> set (vars c) \<Longrightarrow> s v = t v"
  apply (induction c s z t  rule: big_step_tG_induct)
  using BS_Generalized_Cost_axioms
  apply simp
  subgoal using BS_Generalized_Cost_axioms 
    by simp
  by simp+

lemma fresh_var_changed: "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> set (vars c) \<Longrightarrow> (c,s(v:=y)) \<Rightarrow>\<^sub>G\<^bsup>g\<^esup> t' \<Longrightarrow> t' = t(v:=y)"
proof (induction c s z t arbitrary: g t' rule: big_step_tG_induct)
  case (1 s)
  then show ?case 
  using BS_Generalized_Cost_axioms by simp
next
  case (2 x a s)
  then show ?case 
  using BS_Generalized_Cost_axioms by auto
qed auto

lemma lvars_unchanged: "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> lvars c \<Longrightarrow> s v = t v"
  apply (induction c s z t arbitrary:  rule: big_step_tG_induct)
  using BS_Generalized_Cost_axioms by simp+

lemma subst_costs:
  "\<lbrakk>(subst m (x ::= a),s) \<Rightarrow>\<^sub>G\<^bsup> z \<^esup> t' \<rbrakk> \<Longrightarrow> z = assign_costs (subst m a) s"
  unfolding eq_on_def by (auto simp:  aval_eq_if_eq_on_vars[unfolded eq_on_def])   


lemma atom_Val_costs: 
  "\<lbrakk> s = s' o m on S; set (vars a) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow>  atomVal_cost (subst m a) s' = atomVal_cost a s" unfolding eq_on_def
  apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
  by (induction a)  auto

lemma atom_Val_cost_noninterference:
 "set (vars a) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> atomVal_cost a s = atomVal_cost a s'"
  by (induction a) auto
  
lemma aexp_costs: 
  "\<lbrakk> s = s' o m on S; set (vars a) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow>  aexp_cost (subst m a) s' = aexp_cost a s"unfolding eq_on_def
  apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
  apply (induction a) apply auto
  by (metis atom_Val_costs comp_def eq_onI)+

lemma aexp_costs_noninterference:
 "set (vars a) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> aexp_cost a s = aexp_cost a s'"
  using atom_Val_cost_noninterference by (induction a) auto

lemma subst_costs_assign:
  "\<lbrakk> s = s' o m on S; set (vars a) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow>  assign_costs (subst m a) s' = assign_costs a s" unfolding eq_on_def
  apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
  apply (induction a) apply auto
  sorry

lemma assign_costs_noninterference:
 "set (vars a) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> assign_costs a s = assign_costs a s'"
  using atom_Val_cost_noninterference sorry

lemma obtain_existing: 
  assumes "\<exists>t'. P t'"
  obtains t' where "P t'"
  using assms by auto

lemma subst_sound':
  "\<lbrakk> (c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t' z'. (subst m c,s') \<Rightarrow>\<^sub>G\<^bsup>z'\<^esup> t' \<and> t = t' o m on S"
proof (induction c s z t arbitrary: s' rule: big_step_tG_induct)
  case (1 s)
  have "(subst m SKIP, s') \<Rightarrow>\<^sub>G\<^bsup> skip_costs s' \<^esup> s'"
    by simp
  then show ?case using "1.prems"(1) by auto
next
  case  (2 x a s) then show ?case unfolding eq_on_def
    apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
    apply (standard)+
     apply (simp add: BS_Generalized_Cost_axioms)
    apply (standard)+
     apply (metis "2.prems"(1) aval_eq_if_eq_on_vars aval_subst eq_on_subset fun_upd_same inj_on_subset)
    by (simp add: inj_on_contraD)
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  have "set (vars c1) \<subseteq> S" and "set (vars c2) \<subseteq> S" using \<open>set (vars (c1;; c2)) \<subseteq> S\<close> by auto
  have "\<exists>s2' z'. (((subst m c1, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2') \<and> s2 = s2' \<circ> m on S)"
    using \<open>s1 = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c1) \<subseteq> S\<close> "3.IH"(1)[of s']
    by blast
  then obtain s2' z' where 1: "(subst m c1, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2'" "s2 = s2' \<circ> m on S"    
    by force
  have "\<exists>t' z'. ((subst m c2, s2') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> t' \<and> s3 = t' \<circ> m on S)"
    using \<open>s2 = s2' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c2) \<subseteq> S\<close> "3.IH"(2)[of s2']
    by blast
 (* Works with WhileTrue; Esoteric*)
  with Seq obtain s3' z'' where 2: "(subst m c2, s2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s3'" "s3 = s3' \<circ> m on S" unfolding eq_on_def
    by blast
  let ?z''' = "z' + z''"
  have "(subst m (c1;; c2), s') \<Rightarrow>\<^sub>G\<^bsup> ?z''' \<^esup> s3'"
    using  1 2 Seq by auto
  then show ?case unfolding eq_on_def using \<open>s3 = s3' \<circ> m on S\<close> by blast
next
  case (4 s b c1 C t C' c2)
  have "set (vars c1) \<subseteq> S" and "set (vars c2) \<subseteq> S" using \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> by auto
  have "\<exists>s2' z'. (((subst m c1, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2') \<and> t = s2' \<circ> m on S)"
    using \<open>s = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c1) \<subseteq> S\<close> "4.IH"(1)[of s']
    by blast
  then obtain s2' z' where 1: "(subst m c1, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2'" "t = s2' \<circ> m on S"    
    by force
  have "s'(m b) \<noteq> 0" using \<open>s b \<noteq> 0\<close> \<open>s = s' \<circ> m on S\<close>  \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "(subst m (IF b\<noteq>0 THEN c1 ELSE c2), s') \<Rightarrow>\<^sub>G\<^bsup> z' + 1 \<^esup> s2'"
    using 1 IfTrue \<open>s'(m b) \<noteq> 0\<close> by auto
  then show ?case unfolding eq_on_def using \<open>t = s2' \<circ> m on S\<close> by blast
next
  case (5 s b c2 C t C' c1)
  have "set (vars c1) \<subseteq> S" and "set (vars c2) \<subseteq> S" using \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> by auto
  have "\<exists>s2' z'. (((subst m c2, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2') \<and> t = s2' \<circ> m on S)"
    using \<open>s = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c2) \<subseteq> S\<close> "5.IH"(1)[of s']
    by blast
  then obtain s2' z' where 1: "(subst m c2, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2'" "t = s2' \<circ> m on S"    
    by force
  have "s'(m b) = 0" using \<open>s b = 0\<close> \<open>s = s' \<circ> m on S\<close>  \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "(subst m (IF b\<noteq>0 THEN c1 ELSE c2), s') \<Rightarrow>\<^sub>G\<^bsup> z' + 1 \<^esup> s2'"
    using 1 IfFalse \<open>s'(m b) = 0\<close> by auto
  then show ?case unfolding eq_on_def using \<open>t = s2' \<circ> m on S\<close> by blast
next
  case (6 s b c) 
  have "s'(m b) = 0" using \<open>s b = 0\<close> \<open>s = s' \<circ> m on S\<close> \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "(subst m (WHILE b\<noteq>0 DO c), s') \<Rightarrow>\<^sub>G\<^bsup> while_exit_costs s' \<^esup> s'"
    using \<open>s'(m b) = 0\<close> 
    using big_step_tG.WhileFalse by auto
  then show ?case 
    using "6.prems"(1) by auto
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  have "set (vars c) \<subseteq> S" using \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> by auto
  have "\<exists>s2' z'. (((subst m c, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2') \<and> s2 = s2' \<circ> m on S)"
    using \<open>s1 = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c) \<subseteq> S\<close>  "7.IH"(1)[of s']
    by blast
  then obtain s2' z' where 1: "(subst m c, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2'" "s2 = s2' \<circ> m on S"    
    by force
  have "\<exists>t' z'. ((subst m (WHILE b\<noteq>0 DO c), s2') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> t' \<and> s3 = t' \<circ> m on S)"
    using \<open>s2 = s2' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> "7.IH"(2)[of s2']
    by blast
  with WhileTrue obtain s3' z'' where 2: "(subst m (WHILE b\<noteq>0 DO c), s2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s3'" "s3 = s3' \<circ> m on S" unfolding eq_on_def
    by blast
  have "s'(m b) \<noteq> 0" using \<open>s1 b \<noteq> 0\<close> \<open>s1 = s' \<circ> m on S\<close> \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "((WHILE m b\<noteq>0 DO subst m c), s2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s3'"
    using \<open>(subst m (WHILE b\<noteq>0 DO c), s2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s3'\<close> by auto
  let ?z''' = "z' + z'' + 1"
  have " (WHILE m b\<noteq>0 DO (subst m c), s') \<Rightarrow>\<^sub>G\<^bsup> ?z''' \<^esup> s3'"
    using \<open>s'(m b) \<noteq> 0\<close> 1 \<open>((WHILE m b\<noteq>0 DO subst m c), s2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s3'\<close>  WhileTrue by auto
    then show ?case unfolding eq_on_def using \<open>s3 = s3' \<circ> m on S\<close> by force
qed 


(* TODO: Skip issue. Cost may still be different *)
lemma subst_costs_unchanged:
  "\<lbrakk> (c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t' . (subst m c,s') \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t'"
proof (induction c s z t arbitrary: s' rule: big_step_tG_induct)
  case (1 s)
  then show ?case unfolding eq_on_def apply auto sorry
next
  case (2 x a s)
  then show ?case unfolding eq_on_def
    apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
    by (metis "2.prems"(1) BS_Generalized_Cost.aexp_costs BS_Generalized_Cost_axioms Suc_eq_plus1 big_step_tG.Assign)
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  then show ?case unfolding eq_on_def
    apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
    by (metis (full_types) "3.IH"(1) "3.IH"(2) "3.prems"(1) local.bigstep_det local.compose_programs_1 subst_sound')
next
  case (4 s b c1 C t C' c2)
  have "set (vars c1) \<subseteq> S" and "set (vars c2) \<subseteq> S" using \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> by auto
  have "\<exists>s2'. (((subst m c1, s') \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s2'))"
    using \<open>s = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c1) \<subseteq> S\<close> "4.IH"(1)[of s']
    by blast
  then obtain s2'  where 1: "(subst m c1, s') \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s2'"   
    by force
  have "s'(m b) \<noteq> 0" using \<open>s b \<noteq> 0\<close> \<open>s = s' \<circ> m on S\<close>  \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "(subst m (IF b\<noteq>0 THEN c1 ELSE c2), s') \<Rightarrow>\<^sub>G\<^bsup> C + 1 \<^esup> s2'"
    using 1 IfTrue \<open>s'(m b) \<noteq> 0\<close> by auto
  then show ?case unfolding eq_on_def 
    using "4.hyps"(3) by blast
next
  case (5 s b c2 C t C' c1)
  have "set (vars c1) \<subseteq> S" and "set (vars c2) \<subseteq> S" using \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> by auto
  have "\<exists>s2' . (((subst m c2, s') \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s2'))"
    using \<open>s = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c2) \<subseteq> S\<close> "5.IH"(1)[of s']
    by blast
  then obtain s2' where 1: "(subst m c2, s') \<Rightarrow>\<^sub>G\<^bsup> C \<^esup> s2'"   
    by force
  have "s'(m b) = 0" using \<open>s b = 0\<close> \<open>s = s' \<circ> m on S\<close>  \<open>set (vars (IF b\<noteq>0 THEN c1 ELSE c2)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "(subst m (IF b\<noteq>0 THEN c1 ELSE c2), s') \<Rightarrow>\<^sub>G\<^bsup> C + 1 \<^esup> s2'"
    using 1 IfFalse \<open>s'(m b) = 0\<close> by auto
  then show ?case unfolding eq_on_def 
    using "5.hyps"(3) by blast
next
  case (6 s b c)
  then show ?case sorry
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  have "set (vars c) \<subseteq> S" using \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> by auto
  have "\<exists>s2'. (((subst m c, s') \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2'))"
    using \<open>s1 = s' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars c) \<subseteq> S\<close>  "7.IH"(1)[of s']
    by blast
  then obtain s2' where 1: "(subst m c, s') \<Rightarrow>\<^sub>G\<^bsup> C1 \<^esup> s2'"    
    by force
  have \<open>s2 = s2' \<circ> m on S\<close> using subst_sound' big_step_t_cost_determ2 
    by (metis "1" "7.hyps"(2) "7.prems"(1) "7.prems"(3) BS_Generalized_Cost.big_step_t_state_determ2 BS_Generalized_Cost_axioms \<open>set (vars c) \<subseteq> S\<close>)
  have "\<exists>t' . ((subst m (WHILE b\<noteq>0 DO c), s2') \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> t')"
    using \<open>s2 = s2' \<circ> m on S\<close>  \<open>inj_on m S\<close> \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> "7.IH"(2)[of s2']
    by blast
  with WhileTrue obtain s3' where 2: "(subst m (WHILE b\<noteq>0 DO c), s2')  \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3'"  unfolding eq_on_def
    by blast
  have "s'(m b) \<noteq> 0" using \<open>s1 b \<noteq> 0\<close> \<open>s1 = s' \<circ> m on S\<close> \<open>set (vars (WHILE b\<noteq>0 DO c)) \<subseteq> S\<close> unfolding eq_on_def by auto
  have "((WHILE m b\<noteq>0 DO subst m c), s2')  \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3'"
    using \<open>(subst m (WHILE b\<noteq>0 DO c), s2')  \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3'\<close> by auto
  let ?z''' = "C1 + C2 + 1"
  have " (WHILE m b\<noteq>0 DO (subst m c), s') \<Rightarrow>\<^sub>G\<^bsup> ?z''' \<^esup> s3'"
    using \<open>s'(m b) \<noteq> 0\<close> 1 \<open>((WHILE m b\<noteq>0 DO subst m c), s2')  \<Rightarrow>\<^sub>G\<^bsup> C2 \<^esup> s3'\<close>  WhileTrue by auto
    then show ?case unfolding eq_on_def using \<open>C3 = C1 + C2 + 1\<close> by auto
qed

lemma subst_sound:
  "\<lbrakk> (c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t' . (subst m c,s') \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t' \<and> t = t' o m on S"
  using subst_sound' subst_costs_unchanged by (metis big_step_t_state_determ2)

lemma subst_complete':
  "\<lbrakk> (subst m c,s') \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t'; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t z'. (c,s) \<Rightarrow>\<^sub>G\<^bsup>z'\<^esup> t \<and> t = t' o m on S"
proof (induction "subst m c" s' z t' arbitrary: c s rule: big_step_tG_induct)
  case (1 s)
  then show ?case apply (cases c) by auto 
next
  case (2 x a  s' c s)
  then obtain x' a' where defs: "c = x' ::= a'" "x = m x'" "a = subst m a'" by (cases c) auto
  moreover have "(x' ::= a',s) \<Rightarrow>\<^sub>G\<^bsup>assign_costs a s' \<^esup> s(x' := aval a' s)" apply auto
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) Suc_eq_plus1 calculation(1) calculation(3) local.ASSnot subst_costs_assign)
  moreover have "s(x' := aval a' s) = s'(x := aval a s') \<circ> m on S"
    (* Error about online proof reconstruction *)
    by (smt (verit) "2.hyps" "2.prems"(1) "2.prems"(2) "2.prems"(3) big_step_tG.Assign big_step_t_state_determ2 calculation(1) subst_sound') 
  ultimately show ?case 
    by metis
next
  case (3 c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z c s\<^sub>1')
  then show ?case using 3 apply (cases c) apply auto
    by (metis (no_types, lifting) big_step_tG.Seq)
next
  case (4 s b c\<^sub>1 x t z c\<^sub>2 c s')
  then show ?case apply (cases c) apply auto
(* Timed out, trusting that false case works similarly *)
    by (smt (verit) "4.hyps"(1) "4.hyps"(4) big_step_tG.IfTrue comp_apply eq_onE)
next
  case (5 s b c2 C t C' c1)
  then show ?case apply (cases c) apply auto
    by (smt (verit) "5.hyps"(1) "5.hyps"(4) big_step_tG.IfFalse comp_apply eq_onE)
next
  case (6 s b c\<^sub>1 c s')
  then show ?case apply (cases c) apply auto 
    by (metis big_step_tG.WhileFalse comp_def eq_onD)
next
  case (7 s\<^sub>1 b c\<^sub>1 x s\<^sub>2 y s\<^sub>3 z c s\<^sub>1')
  then obtain c\<^sub>1' b' where [simp]: "c = WHILE b'\<noteq>0 DO c\<^sub>1'" "m b' = b" "c\<^sub>1 = subst m c\<^sub>1'" by (cases c) auto
  with 7 have "set (vars c\<^sub>1') \<subseteq> S" by auto 
  with "7.hyps"(3)[OF _ "7.prems"(1) this "7.prems"(3)] obtain s\<^sub>2' z' where
    1: "(c\<^sub>1', s\<^sub>1') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s\<^sub>2'" "s\<^sub>2' = s\<^sub>2 \<circ> m on S" by auto 
  with "7.hyps"(5)[OF _ this(2) "7.prems"(2) "7.prems"(3)] obtain s\<^sub>3' z'' where
    2: "(WHILE b'\<noteq>0 DO c\<^sub>1', s\<^sub>2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s\<^sub>3'" "s\<^sub>3' = s\<^sub>3 \<circ> m on S" by auto
  from 1 2 "7.hyps"(1,6) "7.prems"(1,2) have
    "(WHILE b'\<noteq>0 DO c\<^sub>1', s\<^sub>1')  \<Rightarrow>\<^sub>G\<^bsup> z' + z'' + 1 \<^esup> s\<^sub>3'" "s\<^sub>3' = s\<^sub>3 \<circ> m on S" unfolding eq_on_def using Seq_tE_While_init While_tE apply auto
    by (metis "7.hyps"(1) Suc_eq_plus1 \<open>m b' = b\<close> big_step_tG.WhileTrue)
  thus ?case by auto
qed

lemma subst_complete:
  "\<lbrakk> (subst m c,s') \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t'; s = s' o m on S; set (vars c) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow> \<exists>t . (c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<and> t = t' o m on S"
  using subst_complete' subst_costs_unchanged  by (metis local.bigstep_det)


lemma subst_id_atomVal: "subst id (c:: atomExp) = c"
  by (cases c) auto

corollary subst_id_aexp: "subst id (c::aexp) = c"
  using subst_id_atomVal by (cases c)  auto

corollary subst_id_com: "subst id (c::com) = c"
  using subst_id_aexp by (induction c) auto

lemma noninterference': 
  "(c,s) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t \<Longrightarrow> set (vars c) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> \<exists>t' z'. (c,s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> t' \<and> t = t' on S"
proof (induction c s x t arbitrary: s' rule: big_step_tG_induct)
  case (1 s)
  then show ?case sorry
next
  case (2 x a s)
  then show ?case unfolding eq_on_def
    apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
    by (metis "2.prems"(2) aval_eq_if_eq_on_vars big_step_tG.Assign eq_on_subset fun_upd_other fun_upd_same)
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  have "set (vars c1) \<subseteq> S" and "set (vars c2) \<subseteq> S" using \<open>set (vars (c1;; c2)) \<subseteq> S\<close> by auto
  have "\<exists>s2' z'. (((c1, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2') \<and> s2 = s2'  on S)"
    using \<open>s1 = s' on S\<close>  \<open>set (vars c1) \<subseteq> S\<close> "3.IH"(1)[of s']
    by blast
  then obtain s2' z' where 1: "(c1, s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> s2'" "s2 = s2' on S"    
    by force
  have "\<exists>t' z'. ((c2, s2') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> t' \<and> s3 = t' on S)"
    using \<open>s2 = s2' on S\<close>  \<open>set (vars c2) \<subseteq> S\<close> "3.IH"(2)[of s2']
    by blast
  with Seq obtain s3' z'' where 2: "(c2, s2')  \<Rightarrow>\<^sub>G\<^bsup> z'' \<^esup> s3'" "s3 = s3' on S" unfolding eq_on_def
    by blast
  let ?z''' = "z' + z''"
  have "((c1;; c2), s') \<Rightarrow>\<^sub>G\<^bsup> ?z''' \<^esup> s3'"
    using  1 2 Seq by auto
  then show ?case unfolding eq_on_def using \<open>s3 = s3' on S\<close> 
    by (metis "1"(1) "2"(1) "3.IH"(1) "3.IH"(2) "3.hyps"(3) "3.prems"(2) \<open>set (vars c1) \<subseteq> S\<close> \<open>set (vars c2) \<subseteq> S\<close> eq_onD local.bigstep_det)
next
  case (4 s b c1 C t C' c2)
  then show ?case apply auto 
    by (metis "4.hyps"(1) big_step_tG.IfTrue eq_on_def)
next
  case (5 s b c2 C t C' c1)
  then show ?case apply auto 
    by (metis big_step_tG.IfFalse eq_on_def)
next
  case (6 s b c)
  then show ?case  apply auto 
    by (metis big_step_tG.WhileFalse eq_on_def)
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  then show ?case apply auto 
    by (metis (mono_tags, lifting) "7.hyps"(1) big_step_tG.WhileTrue eq_onE)
qed 

lemma noninterference: 
  "(c,s) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t \<Longrightarrow> set (vars c) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> \<exists>t'. (c,s') \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t' \<and> t = t' on S"
  using subst_complete[of id] subst_id_com 
  by (smt (verit, ccfv_threshold) BS_Generalized_Cost.big_step_t_state_determ2 BS_Generalized_Cost_axioms comp_id inj_on_id subst_costs_unchanged)
end
end