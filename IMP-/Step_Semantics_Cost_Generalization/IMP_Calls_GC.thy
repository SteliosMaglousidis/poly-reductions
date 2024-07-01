
theory IMP_Calls_GC imports  "../IMP_Calls" Vars_for_GC Big_StepT_Generalized_Cost_Final begin

unbundle no_com_syntax
unbundle com'_syntax

context BS_Generalized_Cost begin

inductive
  big_step_t'_GC :: "com' \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^sub>G''\<^bsup> _\<^esup>  _" 55)
where
Skip': "(SKIP',s) \<Rightarrow>\<^sub>G'\<^bsup> skip_costs s \<^esup> s"|
Assign': "(x ::= a,s) \<Rightarrow>\<^sub>G'\<^bsup> assign_costs a s \<^esup> s(x := aval a s)" |
Seq': "\<lbrakk> (c1,s1) \<Rightarrow>\<^sub>G'\<^bsup> C1 \<^esup> s2;  (c2,s2) \<Rightarrow>\<^sub>G'\<^bsup> C2 \<^esup> s3 ; C3 = C1 + C2 \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^sub>G'\<^bsup> C3 \<^esup> s3" |
IfTrue': "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>\<^sub>G'\<^bsup> C \<^esup> t; C'= Suc C \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G'\<^bsup> C' \<^esup> t" |
IfFalse': "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>\<^sub>G'\<^bsup> C \<^esup> t; C'= Suc C \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^sub>G'\<^bsup> C' \<^esup> t" |
WhileFalse': "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^sub>G'\<^bsup> while_exit_costs s \<^esup> s" |
WhileTrue': "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^sub>G'\<^bsup> C1 \<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G'\<^bsup> C2 \<^esup> s3; C1 + C2 + 1 = C3\<rbrakk>
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^sub>G'\<^bsup> C3 \<^esup> s3" |
\<comment> \<open>The only change: The called program is executed on a state that agrees on all the variables in
    the subprogram. In the caller, only the result variable is affected.\<close>
Call': "(c,s) \<Rightarrow>\<^sub>G\<^bsup> z \<^esup> t \<Longrightarrow> (CALL c RETURN r,s) \<Rightarrow>\<^sub>G'\<^bsup>  z \<^esup> (s(r:=t r))"

text \<open>For compilation to IMP-, skip to final proof.\<close>

declare big_step_t'_GC.intros[intro]

thm big_step_t'_GC.induct

lemmas big_step_t'_GC_induct = big_step_t'_GC.induct[split_format(complete), 
    OF BS_Generalized_Cost_axioms, consumes 1]

inductive_cases Skip'_tE[elim!]: "(SKIP',s) \<Rightarrow>\<^sub>G'\<^bsup>  x \<^esup> t"
inductive_cases Assign'_tE[elim!]: "(x ::= a,s) \<Rightarrow>\<^sub>G'\<^bsup> p \<^esup> t"
inductive_cases Seq'_tE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^sub>G'\<^bsup>  p \<^esup> s3"
inductive_cases If'_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^sub>G'\<^bsup>  x \<^esup> t"
inductive_cases Call'_tE[elim!]: " (CALL c RETURN v,s) \<Rightarrow>\<^sub>G'\<^bsup>  z \<^esup> t"

inductive_cases While'_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^sub>G'\<^bsup>  x \<^esup> t"
lemma Seq'': "\<lbrakk> (c1,s1) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> s2;  (c2,s2) \<Rightarrow>\<^sub>G'\<^bsup> y \<^esup> s3  \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^sub>G'\<^bsup> x + y \<^esup> s3"
  by auto
end


context BS_Generalized_Cost begin

lemma state_determ:
  "(c,s) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> t \<Longrightarrow> (c,s) \<Rightarrow>\<^sub>G'\<^bsup>  x' \<^esup> t' \<Longrightarrow> t = t'"
proof (induction  arbitrary: x' t' rule: big_step_t'_GC.induct)
  case IfFalse' then show ?case by (metis If'_tE verit_comp_simplify1(1))
next
  case WhileTrue' then show ?case by (metis While'_tE)
next
  case Call' then show ?case using bigstep_det by fastforce
qed fastforce+

lemma cost_determ: 
  "(c,s) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> t \<Longrightarrow> (c,s) \<Rightarrow>\<^sub>G'\<^bsup>  x' \<^esup> t \<Longrightarrow> x = x'"
proof (induction  arbitrary: x' rule: big_step_t'_GC.induct)
  case (Skip' s)
  then show ?case by fastforce
next
  case (Assign' x a s)
  then show ?case by fastforce
next
  case (Seq' c1 s1 C1 s2 c2 C2 s3 C3)
  then show ?case 
    by (metis Seq'_tE state_determ)
next
  case (IfTrue' s b c1 C t C' c2)
  then show ?case by fastforce
next
  case (IfFalse' s b c2 C t C' c1)
  then show ?case 
    apply(elim If'_tE) 
     apply linarith
    by (metis (no_types, lifting) add.commute plus_1_eq_Suc)
next
  case (WhileFalse' s b c)
  then show ?case by fastforce
next
  case (WhileTrue' s1 b c C1 s2 C2 s3 C3)
  then show ?case proof-
    obtain q1 q2 s2' where "
   ((c, s1) \<Rightarrow>\<^sub>G'\<^bsup>  q1 \<^esup> s2') \<and>
   ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G'\<^bsup>  q2 \<^esup> s3) \<and> x' = 1 + q1 + q2"
      using WhileTrue'.hyps(1) WhileTrue'.prems by auto
    have "s2' = s2" 
      using WhileTrue'.hyps(2) \<open>((c, s1) \<Rightarrow>\<^sub>G'\<^bsup> q1 \<^esup> s2') \<and> ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G'\<^bsup> q2 \<^esup> s3) \<and> x' = 1 + q1 + q2\<close> state_determ by auto
    moreover have "q1 = C1"
    proof- have "(c, s1) \<Rightarrow>\<^sub>G'\<^bsup>  q1 \<^esup> s2" 
        using \<open>((c, s1) \<Rightarrow>\<^sub>G'\<^bsup>  q1 \<^esup> s2') \<and> ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G'\<^bsup>  q2 \<^esup> s3) \<and> x' = 1 + q1 + q2\<close> calculation by auto
      thus ?thesis 
        using WhileTrue'.IH(1) by auto
    qed
    moreover have "q2 = C2"
    proof- have "(WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^sub>G'\<^bsup> q2 \<^esup> s3" 
        using \<open>((c, s1) \<Rightarrow>\<^sub>G'\<^bsup> q1 \<^esup> s2') \<and>
   ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G'\<^bsup> q2 \<^esup> s3) \<and> x' = 1 + q1 + q2\<close> calculation by auto
      thus ?thesis 
        by (simp add: WhileTrue'.IH(2))
    qed
    moreover have "x' = 1 + C1 + C2" 
    proof-
      have "x' = 1 + q1 + q2" using \<open>((c, s1) \<Rightarrow>\<^sub>G'\<^bsup> q1 \<^esup> s2') \<and> ((WHILE b\<noteq>0 DO c, s2') \<Rightarrow>\<^sub>G'\<^bsup> q2 \<^esup> s3) \<and> x' = 1 + q1 + q2\<close>
        by simp
      thus ?thesis using calculation(2-3)
        by (simp add: \<open>x' = 1 + q1 + q2\<close>)
    qed
    ultimately show ?thesis 
      apply (simp add: WhileTrue'.hyps(4))
      using Suc_eq_plus1 WhileTrue'.hyps(4) by presburger
  qed
next
  case (Call' c s z t r)
  then show ?case using bigstep_det by fastforce
qed


lemma noninterference: 
  "(c,s) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> t \<Longrightarrow> set (vars c) \<subseteq> S \<Longrightarrow> s = s' on S \<Longrightarrow> \<exists>t' x'. (c,s') \<Rightarrow>\<^sub>G'\<^bsup> x' \<^esup> t' \<and> t = t' on S"
proof (induction c s x t arbitrary: s' rule: big_step_t'_GC_induct)
  case (2 x a s)
  then show ?case 
    using aval_eq_if_eq_on_vars big_step_t'_GC.Assign' eq_on_def eq_on_subset fun_upd_apply set_subset_Cons vars_com'.simps(2) by fastforce
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  then show ?case apply auto
    by (metis (mono_tags, lifting) "7.hyps"(1) "7.hyps"(4) big_step_t'_GC.WhileTrue' eq_onE)
next
  case (8 c s z t r)
  then show ?case apply auto using noninterference[of c s z t S s'] by fastforce
qed fastforce+

lemma var'_unchanged: "(c,s) \<Rightarrow>\<^sub>G'\<^bsup>z\<^esup> t \<Longrightarrow> v \<notin> set (vars c) \<Longrightarrow> s v = t v"
  by (induction c s z t rule: big_step_t'_GC_induct) auto

section "Inlining"


fun ssubst_costs where
 "ssubst_costs m s [] = skip_costs s" |      
 "ssubst_costs m s (v#vs) = (assign_costs (A (V v)) s) + ssubst_costs m (s(m v := s v)) vs"

(* Feels like it shouldn't be necessary; Needs deeper analysis*)

inductive size\<^sub>cG :: "com' \<Rightarrow> (char list \<Rightarrow> char list) \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> bool" where
Skip'_size: "size\<^sub>cG SKIP' m s 0"|
Assign'_size: "size\<^sub>cG (x ::= a) m s 0" |
(* To make the predicate total. Should not be used to reason for NT programms *)
Seq'_size_NT: "size\<^sub>cG c\<^sub>1 m s n1 \<Longrightarrow> \<forall>s' x. \<not> (c\<^sub>1,s) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> s' \<Longrightarrow> size\<^sub>cG c\<^sub>2 m s' n2 \<Longrightarrow> size\<^sub>cG (c\<^sub>1;;c\<^sub>2) m s 0" |
Seq'_size: "size\<^sub>cG c\<^sub>1 m s n1 \<Longrightarrow> (c\<^sub>1,s) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> s' \<Longrightarrow> size\<^sub>cG c\<^sub>2 m s' n2 \<Longrightarrow> size\<^sub>cG (c\<^sub>1;;c\<^sub>2) m s (n1 + n2)" |
If'_size: "size\<^sub>cG c\<^sub>1 m s n1 \<Longrightarrow> size\<^sub>cG c\<^sub>2 m s n2 \<Longrightarrow> size\<^sub>cG (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) m s (n1 + n2)" |
While'_size: "size\<^sub>cG c m s n \<Longrightarrow> size\<^sub>cG (WHILE b\<noteq>0 DO c) m s n" |
Call'_size: "size\<^sub>cG (CALL c RETURN r) m s (ssubst_costs m s (vars c))"

inductive_cases Skip'_size_tE[elim!]: "size\<^sub>cG SKIP' m s n"
inductive_cases Assign'_size_tE[elim!]: "size\<^sub>cG (x ::= a) m s n"
inductive_cases Seq'_size_tE[elim!]: "size\<^sub>cG (c\<^sub>1;;c\<^sub>2) m s n"
inductive_cases If'_size_tE[elim!]: "size\<^sub>cG (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) m s n"
inductive_cases Call'_size_tE[elim!]: "size\<^sub>cG (CALL c RETURN r) m s n"
inductive_cases While'_size_tE[elim]: "size\<^sub>cG (WHILE b\<noteq>0 DO c) m s n"

unbundle no_com'_syntax
unbundle com_syntax

lemma size\<^sub>cG_total: "\<exists>n. size\<^sub>cG c m s n"
proof(induction c arbitrary: s m)
  case SKIP'
  then show ?case 
  using Skip'_size by auto[1]
next
  case (Assign' x1 x2)
  then show ?case 
  using Assign'_size by blast
next
  case (Seq' c1 c2)
  then show ?case proof(cases "\<exists> s' x. (c1,s) \<Rightarrow>\<^sub>G'\<^bsup> x \<^esup> s'")
    case True
    from True obtain s' x where " (c1, s) \<Rightarrow>\<^sub>G'\<^bsup> x\<^esup>  s' " by auto
    then show ?thesis 
      by (meson Seq'.IH(1) Seq'.IH(2) Seq'_size)
  next
    case False
    then show ?thesis 
      using Seq'.IH(1) Seq'.IH(2) Seq'_size_NT by blast
  qed
next
  case (If' x1 c1 c2)
  then show ?case 
    by (metis If'_size)
next
  case (While' x1 c)
  then show ?case 
    using While'_size by blast
next
  case (Call' x1 x2)
  then show ?case 
    using Call'_size by blast
qed

lemma ssubst_unchanged: "big_step_tG ((ssubst m vs),s) z t \<Longrightarrow> (\<forall>v\<in>set vs. m v \<notin> set vs) \<Longrightarrow> s = t on set vs"
  unfolding eq_on_def using lvars_ssubst lvars_unchanged image_iff 
  by (metis (mono_tags, lifting)) 

lemma ssubst_costs_correct:
 "(ssubst m vs,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<Longrightarrow> z = ssubst_costs m s vs"
  by (induction m vs arbitrary: s z t rule: ssubst.induct) auto

lemma ssubst_correct:
  "\<lbrakk> inj_on m (set vs); (\<forall>v\<in>set vs. m v \<notin> set vs) \<rbrakk>
    \<Longrightarrow> \<exists>t. (ssubst m vs,s) \<Rightarrow>\<^sub>G\<^bsup>ssubst_costs m s vs\<^esup> t \<and> s = t o m on set vs"
proof (induction vs arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons v vs)
  have 1: "(Assign (m v) (A (V v)),s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs (A (V v)) s\<^esup> s(m v := s v)"
    using Assign[of _ "A (V v)"] by simp
  from Cons obtain t where
    2: "(ssubst m vs, s(m v := s v)) \<Rightarrow>\<^sub>G\<^bsup> ssubst_costs m (s(m v := s v)) vs \<^esup> t" and
    s: "s(m v := s v) = t \<circ> m on set vs" by fastforce
  hence "s(m v := s v) = t \<circ> m on set (v#vs)"
  proof (cases "v\<in>set vs")
    case True then show ?thesis using s by auto
  next
    case False
    with Cons.prems(2) have a: "v \<notin> set (vars (ssubst m vs))" by (induction vs) auto
    hence " v \<notin> m ` set vs" by fastforce
    with False have "m v \<notin> m ` set vs" using \<open>\<forall>va\<in>set (v # vs). m va \<notin> set (v # vs)\<close>
      using Cons.prems(1) by force
    with a have "m v \<notin> set (vars (ssubst m vs))" apply auto
      using Cons.prems(2) by force
    hence "(s(m v := s v)) (m v) = t (m v)"   using var_unchanged[OF 2] by blast
    then show ?thesis using s by auto
  qed
  hence "s = t \<circ> m on set (v # vs)"
    by (metis Cons.prems(2) eq_on_feq1 fun_upd_other list.set_intros(1))
  with 1 2 show ?case unfolding eq_on_def
    apply (simp add: numeral_eq_Suc) 
    by (metis add_Suc big_step_tG.Seq)
qed

subsection "Command transfer"

lemma transfer_sound:
  assumes c_sem: "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t"
      and s: "s = s' on set (vars c)"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
    obtains t'
    where "(transfer m c,s')\<Rightarrow>\<^sub>G\<^bsup>ssubst_costs m s'(vars c) + z\<^esup> t'"
      and "t = t' o m on set (vars c)"
proof -
  from ssubst_correct[OF inj disj] obtain s\<^sub>2 where ssubst_sem:
    "(ssubst m (vars c),s') \<Rightarrow>\<^sub>G\<^bsup>ssubst_costs m s' (vars c)\<^esup> s\<^sub>2" and
    "s' = s\<^sub>2 \<circ> m on set (vars c)" 
    by blast
  with s have s\<^sub>2: "s = s\<^sub>2 o m on set (vars c)" by fastforce

  from subst_sound[OF c_sem this _ inj] obtain t' where
    subst_sem: "(subst m c, s\<^sub>2) \<Rightarrow>\<^sub>G\<^bsup> z \<^esup> t'" and t': "t = t' \<circ> m on set (vars c)" by auto
  with ssubst_sem have "(transfer m c,s')\<Rightarrow>\<^sub>G\<^bsup>ssubst_costs m s' (vars c) + z\<^esup> t'"
    unfolding transfer_def 
    by (simp add: big_step_tG.Seq)
  with t' that show ?thesis by blast
qed

lemma transfer_complete:
  assumes transfer_sem: "(transfer m c,s')\<Rightarrow>\<^sub>G\<^bsup>z'\<^esup> t'"
      and s: "s' = s on set (vars c)"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
  obtains t z
    where "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t" "z' = ssubst_costs m s' (vars c) + z" "t = t' o m on set (vars c)"
proof -
  from ssubst_correct[OF inj disj] obtain s\<^sub>2' where
     s\<^sub>2': "(ssubst m (vars c), s') \<Rightarrow>\<^sub>G\<^bsup> ssubst_costs m s' (vars c) \<^esup> s\<^sub>2'" "s' = s\<^sub>2' \<circ> m on set (vars c)"
    by blast
  with transfer_sem[unfolded transfer_def] obtain z where
   subst_sem: "(subst m c,s\<^sub>2') \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t'" and z: "z' = ssubst_costs m s' (vars c) + z"
    using bigstep_det by fastforce 
  from s s\<^sub>2' have "s = s\<^sub>2' o m on set (vars c)" by fastforce 
  from subst_complete[OF subst_sem this _ inj] that z show ?thesis by auto
qed

lemma transfer_unchanged:
  assumes transfer_sem: "(transfer m c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t"
      and inj: "inj_on m (set (vars c))"
      and disj: "(\<forall>v\<in>set (vars c). m v \<notin> set (vars c))"
    shows "s = t on UNIV - m ` set (vars c)"
proof -
  from transfer_sem obtain s\<^sub>2 x y where
    ssubst_sem: "(ssubst m (vars c),s)\<Rightarrow>\<^sub>G\<^bsup>x\<^esup> s\<^sub>2" and
    subst_sem: "(subst m c,s\<^sub>2)\<Rightarrow>\<^sub>G\<^bsup>y\<^esup> t" unfolding transfer_def by auto
  from ssubst_correct[OF inj disj] have "s = s\<^sub>2 o m on set (vars c)"
    using \<open>(ssubst m (vars c), s) \<Rightarrow>\<^sub>G\<^bsup> x \<^esup> s\<^sub>2\<close> bigstep_det by blast

  have "s = s\<^sub>2 on UNIV - m ` set (vars c)"
    using disj ssubst_sem ssubst_unchanged
    by (auto simp add: lvars_unchanged)
  moreover have "s\<^sub>2 = t  on UNIV - m ` set (vars c)" using var_unchanged subst_sem by auto
  ultimately show "s = t on UNIV - m ` set (vars c)" by fastforce
qed

lemma inline1_unchanged:
  assumes inline1_sem: "(inline1 S c r,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t"
      and S: "set (r#vars c) \<subseteq> set S"
    shows "s = t on set S - {r}"
proof -
  let ?m = "fresh S"
  have inj: "inj_on ?m (set (vars c))" and disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))"
    using S fresh fresh_inj inj_on_subset by auto

  from inline1_sem obtain s\<^sub>1 z\<^sub>1 z\<^sub>2  s\<^sub>2 z z\<^sub>3 where
    to_sem: "((?m r) ::= A (V r),s) \<Rightarrow>\<^sub>G\<^bsup>z\<^sub>1\<^esup> s\<^sub>1" and
    "(transfer ?m c;;r ::= A (V (?m r)),s\<^sub>1)\<Rightarrow>\<^sub>G\<^bsup>z\<^sub>2\<^esup> t" and
    transfer_sem: "(transfer ?m c,s\<^sub>1)\<Rightarrow>\<^sub>G\<^bsup>z\<^esup> s\<^sub>2" and
    from_sem: "(r ::= A (V (?m r)),s\<^sub>2)\<Rightarrow>\<^sub>G\<^bsup>z\<^sub>3\<^esup> t"
    unfolding inline1_def apply auto
    by (smt (verit, ccfv_threshold) Seq_costs_split big_step_tG.Seq inline1_def inline1_sem)

  hence s\<^sub>1: "s\<^sub>1 = s(?m r := s r)" "t = s\<^sub>2(r := s\<^sub>2(?m r))" by auto
  moreover have "s\<^sub>1 = s\<^sub>2 on set S" using transfer_unchanged[OF transfer_sem inj disj] 
    by force

  ultimately show "s = t on set S - {r}"
    using fresh apply auto
    by (smt (verit) DiffE eq_on_def fresh fun_upd_other singletonI)
qed

lemma inline1_sound:
  assumes c_sem: "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t"
      and s: "s = s' on set (r#vars c)"
      and S: "set (r#vars c) \<subseteq> set S"
  obtains zr tr
    where "(inline1 S c r,s') \<Rightarrow>\<^sub>G\<^bsup>zr\<^esup> tr"
      and "t r = tr r" "assign_costs (A (V r)) s' +
               (ssubst_costs (fresh S) (s'(fresh S r := s' r)) (vars c) + z) +
               assign_costs (A (V r)) t = zr"
proof -
  let ?m = "fresh S" let ?s\<^sub>1' = "s'((?m r) := s' r)" let ?z' = "ssubst_costs ?m ?s\<^sub>1' (vars c) + z"

  have inj: "inj_on ?m (set (vars c))" using S fresh_inj inj_on_subset by auto
  have disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))" using S fresh by auto

  have 1: "((?m r) ::= A (V r),s') \<Rightarrow>\<^sub>G\<^bsup>assign_costs (A (V r)) s'\<^esup> ?s\<^sub>1'"
    using big_step_tG.Assign[of "?m r" "A (V r)" s'] by auto
  have s\<^sub>1': "s = ?s\<^sub>1' on set (vars c)" using S s by fastforce



  obtain s\<^sub>2' where
    2: "(transfer ?m c, ?s\<^sub>1') \<Rightarrow>\<^sub>G\<^bsup>?z'\<^esup> s\<^sub>2'" and s\<^sub>2': "t = s\<^sub>2' \<circ> ?m on set (vars c)"
    using transfer_sound[OF c_sem s\<^sub>1' inj disj] by blast

  then obtain tr where
    3: "(r ::= A (V (?m r)),s\<^sub>2') \<Rightarrow>\<^sub>G\<^bsup> assign_costs (A (V (?m r))) s\<^sub>2'\<^esup> tr" and tr: "tr = s\<^sub>2'(r := s\<^sub>2'(?m r))"
    using big_step_tG.Assign[of r "A (V (?m r))" s\<^sub>2'] by auto

  from 1 2 3 s\<^sub>1' have res: "(inline1 S c r,s')\<Rightarrow>\<^sub>G\<^bsup>assign_costs (A (V r)) s' + ?z' + assign_costs (A (V (?m r))) s\<^sub>2'\<^esup> tr"
    unfolding inline1_def using Seq by meson

  have "t r = tr r"
  proof (cases "r \<in> set (vars c)")
    case True
    from tr have "tr r = (s\<^sub>2' o ?m) r" by auto
    with True show ?thesis using s\<^sub>2' by auto
  next
    case False
    hence "?m r \<notin> set (vars (transfer ?m c))"
      by (smt (verit, best) S Un_iff fresh fresh_inj inj_on_image_mem_iff list.set_intros(1) set_subset_Cons set_transfer subsetD subset_inj_on)

    with 2 have "?s\<^sub>1' (?m r) = s\<^sub>2' (?m r)"
      using var_unchanged by blast

    then show ?thesis using s tr c_sem False var_unchanged by fastforce
  qed
  have "assign_costs (A (V r)) t = assign_costs ((subst ?m (A (V r)))) s\<^sub>2'"
    using subst_costs_assign 
    using \<open>t r = tr r\<close> tr by force
  hence ascs: "assign_costs (A (V r)) t = assign_costs (A (V (fresh S r))) s\<^sub>2'"
    by simp
  then show ?thesis using that res ascs 
    using \<open>t r = tr r\<close> by auto
qed

lemma inline1_complete:
  assumes inline_sem: "(inline1 S c r,s') \<Rightarrow>\<^sub>G\<^bsup>zr\<^esup> tr"
      and s: "s = s' on set (r#vars c)"
      and S: "set (r#vars c) \<subseteq> set S"
  obtains z t
    where "(c,s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<and> tr r = t r \<and> assign_costs (A (V r)) s' +
               (ssubst_costs (fresh S) (s'(fresh S r := s' r)) (vars c) + z) +
               assign_costs (A (V r)) tr = zr"
proof -
  let ?m = "fresh S" let ?s\<^sub>1' = "s'((?m r) := s' r)"

  have inj: "inj_on ?m (set (vars c))" using S fresh_inj inj_on_subset by auto
  have disj: "(\<forall>v\<in>set (vars c). ?m v \<notin> set (vars c))" using S fresh by auto

  have 1: "((?m r) ::= A (V r),s') \<Rightarrow>\<^sub>G\<^bsup>assign_costs (A (V r)) s'\<^esup> ?s\<^sub>1'"
    using big_step_tG.Assign[of "?m r" "A (V r)" s'] by auto
  have s\<^sub>1': "?s\<^sub>1' = s on set (vars c)" using S s by fastforce

  from inline_sem obtain t' z' where
    2: "(transfer ?m c,?s\<^sub>1') \<Rightarrow>\<^sub>G\<^bsup>z'\<^esup> t'" and z': "assign_costs (A (V r)) s' + z' + assign_costs (A (V r)) tr = zr"
    unfolding inline1_def by fastforce
  from transfer_complete[OF 2 s\<^sub>1' inj disj] obtain t z where
    c_sem: "(c, s)  \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t" and
    z: "z' = ssubst_costs (fresh S) (s'(fresh S r := s' r)) (vars c) + z" and
    t: "t = t' \<circ> fresh S on set (vars c)" by metis

  obtain tr' where
    3: "(r ::= A (V (?m r)),t')\<Rightarrow>\<^sub>G\<^bsup>assign_costs (A (V (?m r))) t'\<^esup> tr'" and tr: "tr' = t'(r := t'(?m r))"
    using big_step_tG.Assign[of r "A (V (?m r))" t'] by auto

  moreover from z have "(inline1 S c r,s')\<Rightarrow>\<^sub>G\<^bsup>assign_costs (A (V r)) s' + ssubst_costs ?m ?s\<^sub>1' (vars c) + z + assign_costs (A (V (?m r))) t'\<^esup> tr'"
    unfolding inline1_def using Seq[OF 1 2] Seq[OF _ 3] 
    by (metis (no_types, lifting) add.assoc)

  ultimately have tr': "tr' = tr"
    using bigstep_det inline_sem by blast

  have "tr' r = t r"
  proof (cases "r \<in> set (vars c)")
    case True
    from tr have "tr' r = (t' o ?m) r" by auto
    with True show ?thesis using t by fastforce
  next
    case False
    hence "?m r \<notin> set (vars (transfer ?m c))"
      by (smt (verit, best) S Un_iff fresh fresh_inj inj_on_image_mem_iff list.set_intros(1) set_subset_Cons set_transfer subsetD subset_inj_on)

    with 2 have "?s\<^sub>1' (?m r) = t' (?m r)"
      using var_unchanged by blast

     show ?thesis  using s tr c_sem False  \<open>(s'(fresh S r := s' r)) (fresh S r) = t' (fresh S r)\<close> var_unchanged by fastforce
   qed

  then show ?thesis using that c_sem z z' tr' by auto
qed

section \<open>Program inlining\<close>

lemma inline_S_sound_costs_lb: 
  "\<lbrakk>(c',s') \<Rightarrow>\<^sub>G'\<^bsup>z'\<^esup> t'; size\<^sub>cG c' (fresh S) s' n; s'= s on set S; set (vars c') \<subseteq> set S\<rbrakk>
    \<Longrightarrow> \<exists>t z. (inline_S S c',s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<and> t = t' on set S \<and> z' \<le> z"
proof(induction c' s' z' t' arbitrary:  n s rule: big_step_t'_GC_induct)
  case (1 s)
  then show ?case sorry
next
  case (2 x a s')
  have  "(x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s \<^esup> s(x := aval a s)" 
    using big_step_tG.Assign by auto
  hence 1: "(inline_S S (Assign' x a), s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s \<^esup> s(x := aval a s)"
    by auto
  from \<open>set (vars (Assign' x a)) \<subseteq> set S\<close> have "set (vars a) \<subseteq> set S" by auto
  hence  "assign_costs a s = assign_costs a s'" using assign_costs_noninterference 
    using "2.prems"(2) 
    using "2.prems"(1) 
    by simp
  hence 2: "assign_costs a s' \<le> assign_costs a s  \<and> assign_costs a s  \<le> assign_costs a s'"
    by simp
  from \<open>set (vars a) \<subseteq> set S\<close> have 3: "s(x := aval a s) = s'(x := aval a s') on set S"
    using "2.prems"(2) "2.prems"(3) local.noninterference 
    using "2.prems"(1) 
    by fastforce
  from 1 2 3 show ?case 
    by (metis "2.prems"(2) "2.prems"(3) Assign'_tE \<open>(x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s \<^esup> s (x := aval a s)\<close> \<open>set (vars a) \<subseteq> set S\<close> aexp_costs_noninterference local.Assign_tE)
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  from \<open>set (vars (Seq' c1 c2)) \<subseteq> set S\<close> have "set (vars c1) \<subseteq> set S" "set (vars c2) \<subseteq> set S"
    by simp+
  from \<open>size\<^sub>cG (Seq' c1 c2) (fresh S) s1 n\<close> \<open>(c1, s1) \<Rightarrow>\<^sub>G'\<^bsup> C1\<^esup>  s2\<close> obtain n1 n2 where
      "size\<^sub>cG c1 (fresh S) s1 n1" "size\<^sub>cG c2 (fresh S) s2 n2" "n = n1 + n2"
    using BS_Generalized_Cost.state_determ BS_Generalized_Cost_axioms by blast
  from "3.IH"(1)[OF \<open>size\<^sub>cG c1 (fresh S) s1 n1\<close> \<open>s1 = s on set S\<close> \<open>set (vars c1) \<subseteq> set S\<close>]
  obtain t1 z1 where "(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z1 \<^esup> t1 " "t1 = s2 on set S" " C1 \<le> z1" 
    by auto
  have \<open>s2 = t1 on set S\<close> 
    using \<open>t1 = s2 on set S\<close> by auto
  from "3.IH"(2)[OF \<open>size\<^sub>cG c2 (fresh S) s2 n2\<close> \<open>s2 = t1 on set S\<close> \<open>set (vars c2) \<subseteq> set S\<close>]
  obtain t2 z2 where "(inline_S S c2, t1) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2 " " t2 = s3 on set S " "C2 \<le> z2"
    by blast
  have "(Seq (inline_S S c1) (inline_S S c2), s) \<Rightarrow>\<^sub>G\<^bsup> z1 + z2 \<^esup> t2"
    using BS_Generalized_Cost_axioms \<open>(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z1 \<^esup> t1\<close> \<open>(inline_S S c2, t1) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close> by blast
  hence "(inline_S S (Seq' c1  c2), s) \<Rightarrow>\<^sub>G\<^bsup> z1 + z2 \<^esup> t2" by auto
  have "C1 + C2 \<le> z1 + z2"
    using \<open>C1 \<le> z1\<close> \<open>C2 \<le> z2\<close> by simp
  hence "C1 + C2 \<le> z1 + z2"
    by simp
  hence "C3 \<le> z1 + z2 "
    using \<open>C3 = C1 + C2\<close> 
    by simp
  hence "C3 \<le> z1 + z2"
    by simp
  hence "C3 \<le> z1 + z2"
    by (auto simp: algebra_simps)
  hence "C3 \<le> z1 + z2"
    using \<open>C3 = C1 + C2\<close> by (auto simp: algebra_simps)
  hence "C3 \<le> z1 + z2"
    using \<open>C3 = C1 + C2\<close> by (auto simp: algebra_simps)
  then show ?case 
    using \<open>(inline_S S (Seq' c1 c2), s) \<Rightarrow>\<^sub>G\<^bsup> z1 + z2 \<^esup> t2\<close> \<open>(inline_S S c2, t1) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close> \<open>t2 = s3 on set S\<close> by blast
next
  case (4 s' b c1 C t C' c2)
  from \<open>size\<^sub>cG (If' b c1 c2) (fresh S) s' n\<close> obtain n1 n2 x'  where
      "size\<^sub>cG c1 (fresh S) s' n1""size\<^sub>cG c2 (fresh S) s' n2" "n = n1 + n2"
    by auto
  from \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> have "set (vars c1) \<subseteq> set S" "set (vars c2) \<subseteq> set S"
    by simp+have "b \<in> set S" 
     using \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> by fastforce 
   hence "s b \<noteq> 0" 
     using \<open>s' = s on set S\<close> \<open>s' b \<noteq> 0\<close> by auto
  from "4.IH"[OF \<open>size\<^sub>cG c1 (fresh S) s' n1 \<close> \<open>s' = s on set S\<close> \<open>set (vars c1) \<subseteq> set S\<close>] 
  obtain t2 z2 where "(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2 " "t2 = t on set S " "C \<le> z2"
    by auto 
  from IfTrue[of s b "(inline_S S c1)" z2 t2 _ "(inline_S S c2)"]
  have 1: "(If b (inline_S S c1) (inline_S S c2), s) \<Rightarrow>\<^sub>G\<^bsup> z2 + 1\<^esup> t2" 
    using \<open>s b \<noteq> 0 \<close> \<open>(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close>
    by (simp add: big_step_tG.IfTrue)
  have "Suc C \<le> Suc z2"
    using \<open>C \<le> z2\<close> by auto
  hence "C' \<le> Suc z2"
    by (simp add: \<open>C' = Suc C\<close>)
  hence "C' \<le> Suc z2"
    by (auto simp: algebra_simps)
  hence 3: "C' \<le> Suc z2"
    using \<open>n = n1 + n2\<close> by auto
  from 1 3  show ?case 
    by (metis Suc_eq_plus1 \<open>t2 = t on set S\<close> inline_S.simps(4))
next
  case (5 s' b c2 C t C' c1)
  from \<open>size\<^sub>cG (If' b c1 c2) (fresh S) s' n\<close> obtain n1 n2 x'  where
      "size\<^sub>cG c1 (fresh S) s' n1""size\<^sub>cG c2 (fresh S) s' n2" "n = n1 + n2"
    by auto
  from \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> have "set (vars c1) \<subseteq> set S" "set (vars c2) \<subseteq> set S"
    by simp+have "b \<in> set S" 
     using \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> by fastforce 
   hence "s b = 0" 
     using \<open>s' = s on set S\<close> \<open>s' b = 0\<close> by auto
  from "5.IH"[OF \<open>size\<^sub>cG c2 (fresh S) s' n2 \<close> \<open>s' = s on set S\<close> \<open>set (vars c2) \<subseteq> set S\<close>] 
  obtain t2 z2 where "(inline_S S c2, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2 " "t2 = t on set S " "C \<le> z2"
    by auto 
  from IfFalse[of s b "(inline_S S c1)" z2 t2 _ "(inline_S S c2)"]
  have 1: "(If b (inline_S S c1) (inline_S S c2), s) \<Rightarrow>\<^sub>G\<^bsup> z2 + 1\<^esup> t2" 
    using \<open>s b = 0 \<close> \<open>(inline_S S c2, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close>
    by (simp add: big_step_tG.IfFalse)
  have "Suc C \<le> Suc z2"
    using \<open>C \<le> z2\<close> by auto
  hence "C' \<le> Suc z2"
    by (simp add: \<open>C' = Suc C\<close>)
  hence "C' \<le> Suc z2"
    by (auto simp: algebra_simps)
  hence 3: "C' \<le> Suc z2"
    using \<open>n = n1 + n2\<close> by auto
  from 1 3  show ?case 
    by (metis Suc_eq_plus1 \<open>t2 = t on set S\<close> inline_S.simps(4))
next
  case (6 s b c)
  then show ?case sorry
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  from \<open>s1 b \<noteq> 0\<close> \<open>set (vars (While' b c)) \<subseteq> set S\<close> \<open> s1 = s on set S\<close> have \<open>s b \<noteq> 0\<close> by auto
  from \<open>set (vars (While' b c)) \<subseteq> set S\<close> have \<open>set (vars c) \<subseteq> set S\<close> by auto
  from \<open>size\<^sub>cG (While' b c) (fresh S) s1 n\<close> have \<open>size\<^sub>cG c (fresh S) s1 n\<close> by auto
  obtain n2 where "size\<^sub>cG (While' b c) (fresh S) s2 n2"
    using size\<^sub>cG_total by blast
  from "7.IH"(1)[OF \<open>size\<^sub>cG c (fresh S) s1 n\<close> \<open>s1 = s on set S\<close> \<open>set (vars c) \<subseteq> set S\<close>]
  obtain C1' s2' where 1: \<open>(inline_S S c, s) \<Rightarrow>\<^sub>G\<^bsup> C1' \<^esup> s2' \<close>\<open> s2' = s2 on set S \<close> \<open> C1 \<le> C1'\<close> by auto
  hence \<open>s2 = s2' on set S\<close> by auto
  from "7.IH"(2)[OF \<open>size\<^sub>cG (While' b c) (fresh S) s2 n2\<close> \<open>s2 = s2' on set S\<close> \<open>set (vars (While' b c)) \<subseteq> set S\<close>]
  obtain C2' s3' where 2: \<open>(inline_S S (While' b c), s2') \<Rightarrow>\<^sub>G\<^bsup> C2' \<^esup> s3' \<close>\<open> s3' = s3 on set S \<close> \<open>C2 \<le> C2'\<close> by auto
  hence \<open>((While b (inline_S S c)), s2') \<Rightarrow>\<^sub>G\<^bsup> C2' \<^esup> s3'\<close> by auto
  from \<open>(inline_S S c, s) \<Rightarrow>\<^sub>G\<^bsup> C1' \<^esup> s2' \<close> \<open>((While b (inline_S S c)), s2') \<Rightarrow>\<^sub>G\<^bsup> C2' \<^esup> s3'\<close>  \<open>s b \<noteq> 0\<close>
  have \<open>((While b (inline_S S c)), s) \<Rightarrow>\<^sub>G\<^bsup> C1' + C2' + 1 \<^esup> s3'\<close> 
    by (simp add: big_step_tG.WhileTrue)
  hence \<open>(inline_S S (While' b c), s)  \<Rightarrow>\<^sub>G\<^bsup> C1' + C2' + 1 \<^esup> s3'\<close> by auto    
  from \<open>C1 \<le> C1'\<close> \<open>C2 \<le> C2'\<close> \<open>C1 + C2 + 1 = C3\<close> have "C3 \<le> C1' + C2' + 1" by simp 
  from \<open>(inline_S S (While' b c), s)  \<Rightarrow>\<^sub>G\<^bsup> C1' + C2' + 1 \<^esup> s3'\<close> \<open> s3' = s3 on set S\<close> \<open>C3 \<le> C1' + C2' + 1\<close> show ?case
    by auto
next
  case (8 c s' z t r)
  hence prems: "s' = s on set (r # vars c)" "set (r # vars c) \<subseteq> set S" 
    using eq_onI eq_on_subset vars_com'.simps(6) by fastforce+

  then obtain zr tr where
    inline: "(inline1 S c r, s) \<Rightarrow>\<^sub>G\<^bsup>  zr \<^esup> tr" "t r = tr r" 
    "assign_costs (A (V r)) s + (ssubst_costs (fresh S) (s(fresh S r := s r)) (vars c) + z) +
               assign_costs (A (V r)) t = zr"
    using inline1_sound[OF \<open>(c, s') \<Rightarrow>\<^sub>G\<^bsup> z \<^esup> t\<close> \<open>s' = s on set (r # vars c)\<close> \<open>set (r # vars c) \<subseteq> set S\<close>] by auto
  with "8.prems"(1) inline1_unchanged[OF inline(1) prems(2)] have "tr = s'(r := tr r) on set S"
    using "8.prems"(2) fun_upd_apply by fastforce
  with inline have " (inline_S S (Call' c r), s) \<Rightarrow>\<^sub>G\<^bsup>  zr \<^esup> tr \<and> tr = s'(r := t r) on set S \<and> z \<le> zr" by simp
  then show ?case by blast
qed

lemma inline_S_sound_costs_lb: 
  "\<lbrakk>(c',s') \<Rightarrow>\<^sub>G'\<^bsup>z'\<^esup> t'; size\<^sub>cG c' (fresh S) s' n; s'= s on set S; set (vars c') \<subseteq> set S\<rbrakk>
    \<Longrightarrow> \<exists>t z. (inline_S S c',s) \<Rightarrow>\<^sub>G\<^bsup>z\<^esup> t \<and> t = t' on set S \<and> z \<le> z' + (z' + 1) * n"
proof(induction c' s' z' t' arbitrary:  n s rule: big_step_t'_GC_induct)
  case (1 s)
  then show ?case sorry
next
  case (2 x a s')
  have  "(x ::= a, s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s \<^esup> s(x := aval a s)" 
    using big_step_tG.Assign by auto
  hence 1: "(inline_S S (Assign' x a), s) \<Rightarrow>\<^sub>G\<^bsup> assign_costs a s \<^esup> s(x := aval a s)"
    by auto
  from \<open>set (vars (Assign' x a)) \<subseteq> set S\<close> have "set (vars a) \<subseteq> set S" by auto
  hence  "assign_costs a s = assign_costs a s'" using assign_costs_noninterference 
    using "2.prems"(2) 
    using "2.prems"(1) 
    by simp
  hence 2: "assign_costs a s' \<le> assign_costs a s  \<and> assign_costs a s  \<le> assign_costs a s'"
    by simp
  from \<open>set (vars a) \<subseteq> set S\<close> have 3: "s(x := aval a s) = s'(x := aval a s') on set S"
    using "2.prems"(2) "2.prems"(3) local.noninterference 
    using "2.prems"(1) 
    by fastforce
  from 1 2 3 show ?case 
    by (metis \<open>assign_costs a s = assign_costs a s'\<close> le_add1)
next
  case (3 c1 s1 C1 s2 c2 C2 s3 C3)
  from \<open>set (vars (Seq' c1 c2)) \<subseteq> set S\<close> have "set (vars c1) \<subseteq> set S" "set (vars c2) \<subseteq> set S"
    by simp+
  from \<open>size\<^sub>cG (Seq' c1 c2) (fresh S) s1 n\<close> \<open>(c1, s1) \<Rightarrow>\<^sub>G'\<^bsup> C1\<^esup>  s2\<close> obtain n1 n2 where
      "size\<^sub>cG c1 (fresh S) s1 n1" "size\<^sub>cG c2 (fresh S) s2 n2" "n = n1 + n2"
    using BS_Generalized_Cost.state_determ BS_Generalized_Cost_axioms by blast
  from "3.IH"(1)[OF \<open>size\<^sub>cG c1 (fresh S) s1 n1\<close> \<open>s1 = s on set S\<close> \<open>set (vars c1) \<subseteq> set S\<close>]
  obtain t1 z1 where "(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z1 \<^esup> t1 " "t1 = s2 on set S" " z1 \<le> C1 + (C1 + 1) * n1" 
    by auto
  have \<open>s2 = t1 on set S\<close> 
    using \<open>t1 = s2 on set S\<close> by auto
  from "3.IH"(2)[OF \<open>size\<^sub>cG c2 (fresh S) s2 n2\<close> \<open>s2 = t1 on set S\<close> \<open>set (vars c2) \<subseteq> set S\<close>]
  obtain t2 z2 where "(inline_S S c2, t1) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2 " " t2 = s3 on set S " "z2 \<le> C2 + (C2 + 1) * n2"
    by blast
  have "(Seq (inline_S S c1) (inline_S S c2), s) \<Rightarrow>\<^sub>G\<^bsup> z1 + z2 \<^esup> t2"
    using BS_Generalized_Cost_axioms \<open>(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z1 \<^esup> t1\<close> \<open>(inline_S S c2, t1) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close> by blast
  hence "(inline_S S (Seq' c1  c2), s) \<Rightarrow>\<^sub>G\<^bsup> z1 + z2 \<^esup> t2" by auto
  have "C1 + C2 \<le> z1 + z2"
    using \<open>C1 \<le> z1\<close> \<open>C2 \<le> z2\<close> by simp
  hence "C1 + C2 \<le> z1 + z2"
    by simp
  hence "C3 \<le> z1 + z2 "
    using \<open>C3 = C1 + C2\<close> 
    by simp
  hence "C3 \<le> z1 + z2"
    by simp
  hence "C3 \<le> z1 + z2"
    by (auto simp: algebra_simps)
  hence "C3 \<le> z1 + z2"
    using \<open>C3 = C1 + C2\<close> by (auto simp: algebra_simps)
  hence "C3 \<le> z1 + z2"
    using \<open>C3 = C1 + C2\<close> by (auto simp: algebra_simps)
  then show ?case 
    using \<open>(inline_S S (Seq' c1 c2), s) \<Rightarrow>\<^sub>G\<^bsup> z1 + z2 \<^esup> t2\<close> \<open>(inline_S S c2, t1) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close> \<open>t2 = s3 on set S\<close> by blast
next
  case (4 s' b c1 C t C' c2)
  from \<open>size\<^sub>cG (If' b c1 c2) (fresh S) s' n\<close> obtain n1 n2 x'  where
      "size\<^sub>cG c1 (fresh S) s' n1""size\<^sub>cG c2 (fresh S) s' n2" "n = n1 + n2"
    by auto
  from \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> have "set (vars c1) \<subseteq> set S" "set (vars c2) \<subseteq> set S"
    by simp+have "b \<in> set S" 
     using \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> by fastforce 
   hence "s b \<noteq> 0" 
     using \<open>s' = s on set S\<close> \<open>s' b \<noteq> 0\<close> by auto
  from "4.IH"[OF \<open>size\<^sub>cG c1 (fresh S) s' n1 \<close> \<open>s' = s on set S\<close> \<open>set (vars c1) \<subseteq> set S\<close>] 
  obtain t2 z2 where "(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2 " "t2 = t on set S " "C \<le> z2"
    by auto 
  from IfTrue[of s b "(inline_S S c1)" z2 t2 _ "(inline_S S c2)"]
  have 1: "(If b (inline_S S c1) (inline_S S c2), s) \<Rightarrow>\<^sub>G\<^bsup> z2 + 1\<^esup> t2" 
    using \<open>s b \<noteq> 0 \<close> \<open>(inline_S S c1, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close>
    by (simp add: big_step_tG.IfTrue)
  have "Suc C \<le> Suc z2"
    using \<open>C \<le> z2\<close> by auto
  hence "C' \<le> Suc z2"
    by (simp add: \<open>C' = Suc C\<close>)
  hence "C' \<le> Suc z2"
    by (auto simp: algebra_simps)
  hence 3: "C' \<le> Suc z2"
    using \<open>n = n1 + n2\<close> by auto
  from 1 3  show ?case 
    by (metis Suc_eq_plus1 \<open>t2 = t on set S\<close> inline_S.simps(4))
next
  case (5 s' b c2 C t C' c1)
  from \<open>size\<^sub>cG (If' b c1 c2) (fresh S) s' n\<close> obtain n1 n2 x'  where
      "size\<^sub>cG c1 (fresh S) s' n1""size\<^sub>cG c2 (fresh S) s' n2" "n = n1 + n2"
    by auto
  from \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> have "set (vars c1) \<subseteq> set S" "set (vars c2) \<subseteq> set S"
    by simp+have "b \<in> set S" 
     using \<open>set (vars (If' b c1 c2)) \<subseteq> set S\<close> by fastforce 
   hence "s b = 0" 
     using \<open>s' = s on set S\<close> \<open>s' b = 0\<close> by auto
  from "5.IH"[OF \<open>size\<^sub>cG c2 (fresh S) s' n2 \<close> \<open>s' = s on set S\<close> \<open>set (vars c2) \<subseteq> set S\<close>] 
  obtain t2 z2 where "(inline_S S c2, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2 " "t2 = t on set S " "C \<le> z2"
    by auto 
  from IfFalse[of s b "(inline_S S c1)" z2 t2 _ "(inline_S S c2)"]
  have 1: "(If b (inline_S S c1) (inline_S S c2), s) \<Rightarrow>\<^sub>G\<^bsup> z2 + 1\<^esup> t2" 
    using \<open>s b = 0 \<close> \<open>(inline_S S c2, s) \<Rightarrow>\<^sub>G\<^bsup> z2 \<^esup> t2\<close>
    by (simp add: big_step_tG.IfFalse)
  have "Suc C \<le> Suc z2"
    using \<open>C \<le> z2\<close> by auto
  hence "C' \<le> Suc z2"
    by (simp add: \<open>C' = Suc C\<close>)
  hence "C' \<le> Suc z2"
    by (auto simp: algebra_simps)
  hence 3: "C' \<le> Suc z2"
    using \<open>n = n1 + n2\<close> by auto
  from 1 3  show ?case 
    by (metis Suc_eq_plus1 \<open>t2 = t on set S\<close> inline_S.simps(4))
next
  case (6 s b c)
  then show ?case sorry
next
  case (7 s1 b c C1 s2 C2 s3 C3)
  from \<open>s1 b \<noteq> 0\<close> \<open>set (vars (While' b c)) \<subseteq> set S\<close> \<open> s1 = s on set S\<close> have \<open>s b \<noteq> 0\<close> by auto
  from \<open>set (vars (While' b c)) \<subseteq> set S\<close> have \<open>set (vars c) \<subseteq> set S\<close> by auto
  from \<open>size\<^sub>cG (While' b c) (fresh S) s1 n\<close> have \<open>size\<^sub>cG c (fresh S) s1 n\<close> by auto
  obtain n2 where "size\<^sub>cG (While' b c) (fresh S) s2 n2"
    using size\<^sub>cG_total by blast
  from "7.IH"(1)[OF \<open>size\<^sub>cG c (fresh S) s1 n\<close> \<open>s1 = s on set S\<close> \<open>set (vars c) \<subseteq> set S\<close>]
  obtain C1' s2' where 1: \<open>(inline_S S c, s) \<Rightarrow>\<^sub>G\<^bsup> C1' \<^esup> s2' \<close>\<open> s2' = s2 on set S \<close> \<open> C1' \<le> C1 + (C1 + 1) * n\<close> by auto
  hence \<open>s2 = s2' on set S\<close> by auto
  from "7.IH"(2)[OF \<open>size\<^sub>cG (While' b c) (fresh S) s2 n2\<close> \<open>s2 = s2' on set S\<close> \<open>set (vars (While' b c)) \<subseteq> set S\<close>]
  obtain C2' s3' where 2: \<open>(inline_S S (While' b c), s2') \<Rightarrow>\<^sub>G\<^bsup> C2' \<^esup> s3' \<close>\<open> s3' = s3 on set S \<close> \<open> C2' \<le> C2 + (C2 + 1) * n2\<close>  by auto
  hence \<open>((While b (inline_S S c)), s2') \<Rightarrow>\<^sub>G\<^bsup> C2' \<^esup> s3'\<close> by auto
  from \<open>(inline_S S c, s) \<Rightarrow>\<^sub>G\<^bsup> C1' \<^esup> s2' \<close> \<open>((While b (inline_S S c)), s2') \<Rightarrow>\<^sub>G\<^bsup> C2' \<^esup> s3'\<close>  \<open>s b \<noteq> 0\<close>
  have \<open>((While b (inline_S S c)), s) \<Rightarrow>\<^sub>G\<^bsup> C1' + C2' + 1 \<^esup> s3'\<close> 
    by (simp add: big_step_tG.WhileTrue)
  hence \<open>(inline_S S (While' b c), s)  \<Rightarrow>\<^sub>G\<^bsup> C1' + C2' + 1 \<^esup> s3'\<close> by auto    
  from \<open>C1 \<le> C1'\<close> \<open>C2 \<le> C2'\<close> \<open>C1 + C2 + 1 = C3\<close> have "C3 \<le> C1' + C2' + 1" by simp 
  from \<open>(inline_S S (While' b c), s)  \<Rightarrow>\<^sub>G\<^bsup> C1' + C2' + 1 \<^esup> s3'\<close> \<open> s3' = s3 on set S\<close> \<open>C3 \<le> C1' + C2' + 1\<close> show ?case
    by auto
next
  case (8 c s' z t r)
  hence prems: "s' = s on set (r # vars c)" "set (r # vars c) \<subseteq> set S" 
    using eq_onI eq_on_subset vars_com'.simps(6) by fastforce+

  then obtain zr tr where
    inline: "(inline1 S c r, s) \<Rightarrow>\<^sub>G\<^bsup>  zr \<^esup> tr" "t r = tr r" 
    "assign_costs (A (V r)) s + (ssubst_costs (fresh S) (s(fresh S r := s r)) (vars c) + z) +
               assign_costs (A (V r)) t = zr"
    using inline1_sound[OF \<open>(c, s') \<Rightarrow>\<^sub>G\<^bsup> z \<^esup> t\<close> \<open>s' = s on set (r # vars c)\<close> \<open>set (r # vars c) \<subseteq> set S\<close>] by auto
  with "8.prems"(1) inline1_unchanged[OF inline(1) prems(2)] have "tr = s'(r := tr r) on set S"
    using "8.prems"(2) fun_upd_apply by fastforce
  with inline have " (inline_S S (Call' c r), s) \<Rightarrow>\<^sub>G\<^bsup>  zr \<^esup> tr \<and> tr = s'(r := t r) on set S \<and> z \<le> zr" by simp
  then show ?case by blast
qed


lemma inline_S_complete:
  assumes "(inline_S S c',s) \<Rightarrow>\<^bsup>z\<^esup> t" "s= s' on set S" "set (vars c') \<subseteq> set S"
  shows "\<exists>z' t'. (c',s') \<Rightarrow>'\<^bsup>z'\<^esup> t' \<and> t = t' on set S \<and> z' \<le> z \<and> z < (z' + 1) * (1 + size\<^sub>c c')"
  using assms
proof (induction "inline_S S c'" s z t arbitrary: c' s' rule: big_step_t_induct)
  case (Skip s)
  then show ?case by (cases c') (auto simp: inline1_def)
next
  case (Assign x a s)
  then show ?case 
    apply (cases c')
    apply (auto simp: inline1_def split: if_splits)
    by (smt (verit) Assign' aval_eq_if_eq_on_vars dual_order.refl eq_on_def eq_on_subset fun_upd_apply lessI)
next
  case (Seq c\<^sub>1 s\<^sub>1 x s\<^sub>2 c\<^sub>2 y s\<^sub>3 z c')
  then show ?case
  proof (cases c')
    case (Seq' c\<^sub>1' c\<^sub>2')
    with Seq obtain x' s\<^sub>2'  y' s\<^sub>3' where
      "(c\<^sub>1', s') \<Rightarrow>'\<^bsup> x'\<^esup>  s\<^sub>2'"
      "s\<^sub>2 = s\<^sub>2' on set S"
      "x' \<le> x \<and> x < (x' + 1) * (1 + size\<^sub>c c\<^sub>1')"
      "(c\<^sub>2', s\<^sub>2') \<Rightarrow>'\<^bsup> y'\<^esup>  s\<^sub>3'"
      "s\<^sub>3 = s\<^sub>3' on set S"
      "y' \<le> y \<and> y < (y' + 1) * (1 + size\<^sub>c c\<^sub>2')"
      by auto metis
    hence
      "(Seq' c\<^sub>1' c\<^sub>2', s') \<Rightarrow>'\<^bsup> x' + y'\<^esup>  s\<^sub>3' \<and> s\<^sub>3 = s\<^sub>3' on set S \<and> x' + y' \<le> z"
      "z < (x' + y' + 1) * (1 + size\<^sub>c (Seq' c\<^sub>1' c\<^sub>2'))" using Seq.hyps(5) by (auto simp: algebra_simps)
    thus ?thesis using Seq' by auto
  next
    case (Call' c r)
    with Seq.prems Seq.hyps(1,3,5,6) have 1: "(inline1 S c r,s\<^sub>1)\<Rightarrow>\<^bsup> z \<^esup> s\<^sub>3"  "s' = s\<^sub>1 on set (r # vars c)" "set (r # vars c) \<subseteq> set S"
      by (auto simp add: inline1_def) blast
    from inline1_complete[OF this] obtain z' t where
      c_sem: "(c, s') \<Rightarrow>\<^bsup> z' \<^esup> t" and t: "s\<^sub>3 r = t r" and z': "2 * length (vars c) + z' + 5 = z" by metis
    with big_step_t'.Call' Call' have "(c',s') \<Rightarrow>'\<^bsup> z' \<^esup> s'(r := t r)" by simp
    have "s\<^sub>1 = s\<^sub>3 on set S - {r}" using inline1_unchanged[OF 1(1) 1(3)] .
    from z' Call' have " z < (z' + 1) * (1 + size\<^sub>c c')" by (auto simp: algebra_simps)
    thus ?thesis
      using Seq.prems(1) \<open>(c', s') \<Rightarrow>'\<^bsup> z' \<^esup> s'(r := t r)\<close> \<open>s\<^sub>1 = s\<^sub>3 on set S - {r}\<close> t z' by auto fastforce
  qed (use Seq.hyps(6) in auto)
next
  case (IfTrue s b c\<^sub>1 x t y c\<^sub>2)
  then obtain c\<^sub>1' c\<^sub>2' where c': "c' = If' b c\<^sub>1' c\<^sub>2'" by (cases c') (auto simp: inline1_def)
  with IfTrue obtain x' t' where 
    "(c\<^sub>1', s') \<Rightarrow>'\<^bsup>x'\<^esup> t' \<and> t = t' on set S \<and> x' \<le> x" "x < (x' + 1) * (1 + size\<^sub>c c\<^sub>1')" by auto blast
  moreover have "s' b \<noteq> 0" using IfTrue c' by auto
  ultimately have "(If' b c\<^sub>1' c\<^sub>2', s') \<Rightarrow>'\<^bsup> x' + 1\<^esup>  t' \<and> t = t' on set S \<and> x' + 1 \<le> y" using IfTrue by auto 
  moreover from \<open>y = x + 1\<close> \<open> x < (x' + 1) * (1 + size\<^sub>c c\<^sub>1')\<close>
  have "y < ((x' + 1) + 1) * (1 + size\<^sub>c c')" using c' by (auto simp: algebra_simps)
  ultimately have "(c', s') \<Rightarrow>'\<^bsup> x' + 1\<^esup>  t' \<and> t = t' on set S \<and> x' + 1 \<le> y \<and> y < (x' + 1 + 1) * (1 + size\<^sub>c c')" using c' by auto
  thus ?case by blast 
next
  case (IfFalse s b c\<^sub>2 x t y c\<^sub>1)
  then obtain c\<^sub>1' c\<^sub>2' where c': "c' = If' b c\<^sub>1' c\<^sub>2'" by (cases c') (auto simp: inline1_def)
  with IfFalse obtain x' t' where 
    "(c\<^sub>2', s') \<Rightarrow>'\<^bsup>x'\<^esup> t' \<and> (t = t' on set S) \<and> x' \<le> x" "x < (x' + 1) * (1 + size\<^sub>c c\<^sub>2')" by auto blast
  moreover have "s' b = 0" using IfFalse c' by auto
  ultimately have "(If' b c\<^sub>1' c\<^sub>2', s') \<Rightarrow>'\<^bsup> x' + 1\<^esup>  t' \<and> t = t' on set S \<and> x' + 1 \<le> y" using IfFalse by auto
  moreover from \<open>y = x + 1\<close> \<open> x < (x' + 1) * (1 + size\<^sub>c c\<^sub>2')\<close>
  have "y < ((x' + 1) + 1) * (1 + size\<^sub>c c')" using c' by (auto simp: algebra_simps)
  ultimately have "(c', s') \<Rightarrow>'\<^bsup> x' + 1\<^esup>  t' \<and> t = t' on set S \<and> x' + 1 \<le> y \<and> y < (x' + 1 + 1) * (1 + size\<^sub>c c')" using c' by auto
  thus ?case by blast 
next
  case (WhileFalse s b c)
  then show ?case 
    apply (cases c') 
    apply (auto simp: inline1_def trans_le_add1 le_Suc_eq WhileFalse') by fastforce
next
  case (WhileTrue s\<^sub>1 b c\<^sub>1 x s\<^sub>2 y s\<^sub>3 z c' s\<^sub>1')
  then obtain c\<^sub>1' where c'[simp]: "c' = While' b c\<^sub>1'" by (cases c') (auto simp: inline1_def)
  with WhileTrue obtain s\<^sub>2' x' where 1: "(c\<^sub>1', s\<^sub>1') \<Rightarrow>'\<^bsup> x' \<^esup> s\<^sub>2'" "s\<^sub>2 = s\<^sub>2' on set S" " x' \<le> x" "x < (x' + 1) * (1 + size\<^sub>c c')" by auto metis
  with WhileTrue c' obtain s\<^sub>3' y' where 2: "(While' b c\<^sub>1', s\<^sub>2') \<Rightarrow>'\<^bsup> y' \<^esup> s\<^sub>3'" "s\<^sub>3 = s\<^sub>3' on set S" "y' \<le> y" "y < (y' + 1) * (1 + size\<^sub>c c')" 
    apply auto by (metis WhileTrue.hyps(7) WhileTrue.prems(2) c' size\<^sub>c.simps(3))
  from c' WhileTrue.prems WhileTrue.hyps(1) have b: "s\<^sub>1' b \<noteq> 0" by auto
  with 1 2 c' have "(While' b c\<^sub>1', s\<^sub>1') \<Rightarrow>'\<^bsup> 1 + x' + y' \<^esup> s\<^sub>3'" "1 + x' + y' \<le> 1 + x + y"
    using WhileTrue'[of s\<^sub>1', OF b] by auto
  moreover from  \<open>1 + x + y = z\<close> \<open>x < (x' + 1) * (1 + size\<^sub>c c')\<close> \<open>y < (y' + 1) * (1 + size\<^sub>c c')\<close>
  have "z < (x' + y' + 1 + 1) * (1 + size\<^sub>c c')" by (auto simp: algebra_simps)
  ultimately have "(c', s\<^sub>1') \<Rightarrow>'\<^bsup>(x' + y' + 1)\<^esup>  s\<^sub>3' \<and> s\<^sub>3 = s\<^sub>3' on set S \<and> (x' + y' + 1) \<le> z \<and> z < ((x' + y' + 1) + 1) * (1 + size\<^sub>c c')"
    using c' 2 WhileTrue.hyps(6) by auto
  thus ?case by blast
qed

definition inline :: "com' \<Rightarrow> com" where
  "inline c = inline_S (vars c) c"


theorem inline_sound:
  assumes c_sem: "(c,s') \<Rightarrow>'\<^bsup>z'\<^esup> t'"
      and s: "s' = s on set (vars c)"
  obtains z t
    where "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
      and "t = t' on set (vars c)"
      and "z' \<le> z" "z \<le> (z' + 1) * (1 + size\<^sub>c c)"
  unfolding inline_def using inline_S_sound[OF c_sem s] by auto

theorem inline_complete:
  assumes inline_sem: "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
      and s: "s = s' on set (vars c)"
  obtains z' t'
   where "(c,s') \<Rightarrow>'\<^bsup>z'\<^esup> t'"
     and "t = t' on set (vars c)" "z' \<le> z" "z \<le> (z' + 1) * (1 + size\<^sub>c c)"
  unfolding inline_def using inline_S_complete[OF inline_sem[unfolded inline_def] s] by auto


text \<open>Final correctness theorem (for refinements)\<close>
corollary inline:
  assumes "(inline c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
  obtains z' t'
    where "(c,s) \<Rightarrow>'\<^bsup>z'\<^esup> t'"
      and "t = t' on set (vars c)"
      and "z' \<le> z" "z \<le> (z' + 1) * (1 + size\<^sub>c c)"
  using inline_complete[where ?s'=s,OF assms] by auto

end