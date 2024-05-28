theory Vars_for_GC imports Big_StepT_Generalized_Cost_Final "../Eq_On"
begin



sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

class vars =
  fixes vars :: "'a \<Rightarrow> vname list"

class subst = vars +
  fixes subst :: "(vname \<Rightarrow> vname) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes subst_vars[simp]: "set (vars (subst m c)) = m ` set (vars c)"

instantiation atomExp :: vars
begin

fun vars_atomExp :: "atomExp \<Rightarrow> vname list" where
"vars_atomExp (V var) = [var]" |
"vars_atomExp (N _) = []"

instance ..

end

instantiation atomExp :: subst
begin

fun subst_atomExp :: "(vname \<Rightarrow> vname) \<Rightarrow> atomExp \<Rightarrow> atomExp" where
"subst m (V var) = V (m var)" |
"subst m (N n) = N n"

instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed

end

instantiation aexp :: vars
begin

fun vars_aexp :: "aexp \<Rightarrow> vname list" where
"vars (A e) = vars e" |
"vars (Plus e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 @ vars e\<^sub>2" |
"vars (Sub e\<^sub>1 e\<^sub>2) = vars e\<^sub>1 @ vars e\<^sub>2" |
"vars (Parity e) = vars e" |
"vars (RightShift e) = vars e"

instance ..

end

instantiation aexp :: subst
begin

fun subst_aexp :: "(vname \<Rightarrow> vname) \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst m (A e) = A (subst m e)" |
"subst m (Plus e\<^sub>1 e\<^sub>2) = Plus (subst m e\<^sub>1) (subst m e\<^sub>2)" |
"subst m (Sub e\<^sub>1 e\<^sub>2) = Sub (subst m e\<^sub>1) (subst m e\<^sub>2)" |
"subst m (Parity e) = Parity (subst m e)" |
"subst m (RightShift e) = RightShift (subst m e)"

instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed

end


lemma atomVal_eq_if_eq_on_vars[simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> atomVal a s\<^sub>1 = atomVal a s\<^sub>2"
  by (induction a) auto

lemma aval_eq_if_eq_on_vars [simp]:
  "s\<^sub>1 = s\<^sub>2 on set (vars a) \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
  apply (induction a)
  apply auto 
  using atomVal_eq_if_eq_on_vars eq_on_subset
  apply (metis sup.cobounded1 sup.cobounded2)+
  done

fun lvars :: "com \<Rightarrow> vname set" where
"lvars SKIP = {}" |
"lvars (x::=e) = {x}" |
"lvars (c1;;c2) = lvars c1 \<union> lvars c2" |
"lvars (IF b\<noteq>0 THEN c1 ELSE c2) = lvars c1 \<union> lvars c2" |
"lvars (WHILE b\<noteq>0 DO c) = lvars c"

instantiation com :: vars
begin

fun vars_com :: "com \<Rightarrow> vname list" where
"vars SKIP = []" |
"vars (x::=e) = x#vars e" |
"vars (c1;;c2) = vars c1 @ vars c2" |
"vars (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars c1 @ vars c2" |
"vars (WHILE b\<noteq>0 DO c) = b#vars c"

instance ..

end

instantiation com :: subst
begin

fun subst_com :: "(vname \<Rightarrow> vname) \<Rightarrow> com \<Rightarrow> com" where
"subst m SKIP = SKIP" |
"subst m (x::=e) = (m x) ::= subst m e" |
"subst m (c\<^sub>1;;c\<^sub>2) = subst m c\<^sub>1;; subst m c\<^sub>2" |
"subst m (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) = IF m b\<noteq>0 THEN subst m c\<^sub>1 ELSE subst m c\<^sub>2" |
"subst m (WHILE b\<noteq>0 DO c) = WHILE m b\<noteq>0 DO subst m c"

instance
proof (standard, goal_cases)
  case (1 m c)
  then show ?case by (induction c) auto
qed

end

lemma atomVal_subst[simp]: "inj_on m (set (vars a)) \<Longrightarrow> atomVal (subst m a) s = (atomVal a (s o m))"
  by (induction a) auto

lemma aval_subst[simp]: "inj_on m (set (vars a)) \<Longrightarrow> aval (subst m a) s = aval a (s o m)"
  by (induction a) (auto simp add: inj_on_Un)

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

lemma aexp_costs: 
  "\<lbrakk> s = s' o m on S; set (vars a) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow>  aexp_cost (subst m a) s' = aexp_cost a s"unfolding eq_on_def
  apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
  apply (induction a) apply auto
  by (metis atom_Val_costs comp_def eq_onI)+

lemma subst_costs_assign:
  "\<lbrakk> s = s' o m on S; set (vars (x ::= a)) \<subseteq> S; inj_on m S \<rbrakk>
    \<Longrightarrow>  assign_costs (subst m a) s' = assign_costs a s" unfolding eq_on_def
  apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
  apply (induction a) apply auto
  by (metis atom_Val_costs comp_eq_dest_lhs eq_onI)+
  term "(m x) ::= subst m a"

lemma obtain_existing: 
  assumes "\<exists>t'. P t'"
  obtains t' where "P t'"
  sledgehammer
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
    \<Longrightarrow> \<exists>t' z' . (subst m c,s') \<Rightarrow>\<^sub>G\<^bsup>z'\<^esup> t' \<and> t = t' o m on S"
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

lemma noninterference': 
  "(c,s) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> t \<Longrightarrow> set (vars c) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> \<exists>t' z'. (c,s') \<Rightarrow>\<^sub>G\<^bsup> z' \<^esup> t' \<and> t = t' on S"
proof (induction c s x t arbitrary: s' rule: big_step_tG_induct)
  case (1 s)
  then show ?case by auto 
next
  case (2 x a s)
  then show ?case unfolding eq_on_def
    apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
    by (metis "2.prems"(2) aval_eq_if_eq_on_vars big_step_tG.Assign eq_on_subset fun_upd_other fun_upd_same)
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  then show ?case  unfolding eq_on_def
    apply (auto simp: subset_inj_on subsetD inj_on_contraD aval_eq_if_eq_on_vars[unfolded eq_on_def])
    sorry
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
  case (Assign x a s)
  then show ?case 
    using aval_eq_if_eq_on_vars big_step_t.Assign eq_on_def eq_on_subset fun_upd_apply set_subset_Cons vars_com.simps(2) by fastforce
next
  case (WhileTrue s1 b c x s2 y s3 z)
  then show ?case apply auto
    by (metis (mono_tags, lifting) WhileTrue.hyps(1) WhileTrue.hyps(4) big_step_t.WhileTrue eq_onE)
qed fastforce+


end