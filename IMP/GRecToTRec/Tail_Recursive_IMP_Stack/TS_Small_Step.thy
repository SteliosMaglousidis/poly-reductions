theory TS_Small_Step
  imports IMP_Tailcall_Stacked
begin

section \<open>Semantics for small-step-ish reasoning (loops)\<close>
text \<open>Big-step semantics that just returns true for Tail\<close>
inductive
  stail_step :: "(tscom \<times> state \<times> fstack) \<Rightarrow> nat \<Rightarrow> (state \<times> fstack \<times> bool) \<Rightarrow> bool" ("\<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tssSkip: "\<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,False)" |
tssAssign: "\<turnstile>(x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack, False)" |
tssSeq: "\<lbrakk>\<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,False); \<turnstile> (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3,CONT) ; z=x+y \<rbrakk> \<Longrightarrow> \<turnstile> (c1;;c2,s1,stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3,CONT)" |
tssIfTrue: "\<lbrakk> s b \<noteq> 0;  \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',CONT); y=x+1 \<rbrakk> \<Longrightarrow> \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',CONT)" |
tssIfFalse: "\<lbrakk> s b = 0; \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',CONT); y=x+1  \<rbrakk> \<Longrightarrow> \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',CONT)" |
tssCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> \<turnstile> (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,False)" |
tssTail: "\<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 \<^esup> (s,stack,True)" |
tsPush: "\<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x),False)" |
tsPop: "stack x = Cons v vx \<Longrightarrow>  \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := hd (stack x)), stack(x := (tl (stack x))),False)" 

code_pred stail_step . 

declare stail_step.intros[intro]

lemmas stail_step_induct = stail_step.induct[split_format(complete)]

inductive_cases stailSkip_tE[elim!]: "\<turnstile> (tsSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"
inductive_cases stailAssign_tE[elim!]: "\<turnstile> (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases stailSeq_tE[elim!]: "\<turnstile> (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (s3,b)"
inductive_cases stailIf_tE[elim!]: "\<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT)"
inductive_cases stailCall_tE[elim!]: "\<turnstile> (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b)"
inductive_cases stailTail_tE[elim]: "\<turnstile> (tsTAIL,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"
inductive_cases stailPush_tE[elim]: "\<turnstile> (PUSH v,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases stailPop_tE[elim]: "\<turnstile> (POP v,s) \<Rightarrow>\<^bsup>x \<^esup> t"

text \<open>Closure of tails\<close>
inductive
  stail_steps :: "tscom \<Rightarrow> tscom \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack  \<Rightarrow> bool" ("_ \<turnstile>''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55) for d
where
tFalse: "\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',False) \<Longrightarrow> d \<turnstile>'(c,s,stack)\<Rightarrow>\<^bsup>z \<^esup> (t,stack')" |
tTrue: "\<turnstile>(c,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,True) \<Longrightarrow> d \<turnstile>'(d,s2,stack2)\<Rightarrow>\<^bsup>y \<^esup> (s3,stack3) \<Longrightarrow> d \<turnstile>'(c,s1,stack1)\<Rightarrow>\<^bsup>x+y \<^esup> (s3,stack3)"

code_pred stail_steps .

declare stail_steps.intros[intro]
declare stail_steps.cases[elim]

lemmas stail_steps_induct = stail_steps.induct[split_format(complete)]

lemma no_stails_no_step: "\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',b) \<Longrightarrow> \<not>stails c \<Longrightarrow> \<not>b"
  by (induction c s stack z t stack' b rule: stail_step_induct) auto

lemma no_tails_sem: "\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',b) \<Longrightarrow> \<not>stails c \<Longrightarrow>  d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack')"
proof (induction c s stack z t stack' b rule: stail_step_induct) 
  case (tssSeq c1 s1 stack1 x s2 stack2 c2 y s3 stack3 CONT z)
  then show ?case 
    by auto
next
  case (tssIfTrue s b c1 stack x t stack' CONT y c2)
  then show ?case 
    by auto
next
  case (tssIfFalse s b c2 stack x t stack' CONT y c1)
  then show ?case 
    by auto
next
  case (tssTail s stack)
  then show ?case 
    by auto
qed blast+

lemma stail_step_deterministic: 
  "\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',b) \<Longrightarrow> \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z'\<^esup> (t',stack'',b') \<Longrightarrow> z = z' \<and> t = t' \<and> stack'' = stack' \<and> b = b'" 
proof (induction c s stack z t stack' b arbitrary: z' t' stack'' b' rule: stail_step_induct)
  case (tssIfTrue s b c c1 stack x t stack' y c2)
  then show ?case 
    by fastforce
next
  case (tssIfFalse s b c2 stack x t stack' CONT y c1)
  from \<open>s b = 0\<close> \<open> \<turnstile>(IF b\<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>z'\<^esup>  (t', stack'', b')\<close> obtain x' where
     \<open>\<turnstile> (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup>  (t', stack'',b')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t' \<and> stack'' = stack' \<and> CONT = b'\<close>
    using tssIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> tssIfFalse.hyps(3))
next
  case (tssCall C s z t c r stack)
  then show ?case 
    using bigstep_det by blast           
qed (blast | fastforce)+ 

end