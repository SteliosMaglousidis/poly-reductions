theory ProofLanguage
  imports Com_Tagged
begin


unbundle no com_syntax and com'_syntax and no tscom_syntax

declare [[syntax_ambiguity_warning=false]]

type_synonym stack = "val list" 

type_synonym fstack = "vname \<Rightarrow> stack"

text "Syntactic sugar to write stacks:"
definition empty_stack ("<[]>") where
  "empty_stack \<equiv> \<lambda>x. []"

fun push_many_stack :: "fstack \<Rightarrow> state \<Rightarrow> vname list \<Rightarrow> fstack" where
"push_many_stack stack s [] = stack" |
"push_many_stack stack s (v#vs) = push_many_stack (stack(v := s v # stack v)) s vs"

fun pop_many_stack :: "fstack \<Rightarrow> vname list \<Rightarrow> fstack" where
"pop_many_stack stack [] = stack" |
"pop_many_stack stack (v#vs) = 
  (case stack v of [] \<Rightarrow> pop_many_stack stack vs 
               | sv#svs \<Rightarrow> pop_many_stack (stack(v := svs)) vs)"

fun pop_many_state :: "state \<Rightarrow> fstack \<Rightarrow> vname list \<Rightarrow> state" where
"pop_many_state s stack [] = s" |
"pop_many_state s stack (v#vs) = 
  (case stack v of [] \<Rightarrow> pop_many_state s stack vs 
               | sv#svs \<Rightarrow> pop_many_state (s(v := sv)) (stack(v := svs)) vs)"

datatype
  pcom = pSKIP
      | pAssign vname aexp
      | pSeq    pcom  pcom
      | pIf     vname pcom pcom
      | pCall   com vname
      | pRec nat
      | pPush  vname 
      | pPop  vname 


open_bundle pcom_syntax begin
notation pAssign ("_ ::= _" [1000, 61] 61)  and
         pSeq ("_;;/ _"  [60, 61] 60) and
         pIf ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         pCall ("CALL _ RETURN _")and
         pRec ("RECURSE _" [61] 61) and
         pPush ("PUSH _" [61] 61) and
         pPop ("POP _" [61] 61)
end
unbundle no com'_syntax 

section \<open>General recursion semantics for the stack language\<close>

inductive
  pbig_step_t :: "pcom \<Rightarrow> pcom \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack \<Rightarrow> bool" ("_ \<turnstile>\<^sub>P _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
pSkip: "c \<turnstile>\<^sub>P (pSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack)" |
pAssign: "c \<turnstile>\<^sub>P (x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack)" |
pSeq: "\<lbrakk>c \<turnstile>\<^sub>P (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2) ; c \<turnstile>\<^sub>P (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3) ; z=x+y\<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>P (c1;;c2, s1, stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3)" |
pIfTrue: "\<lbrakk>s b \<noteq> 0;  c \<turnstile>\<^sub>P (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>P (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack')" |
pIfFalse: "\<lbrakk>s b = 0; c \<turnstile>\<^sub>P (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>P (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack')" |
pCall: "(C,s) \<Rightarrow>\<^bsup> z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>P (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack)" |
\<comment> \<open>New rule\<close>
pTail: "c \<turnstile>\<^sub>P (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> ts \<Longrightarrow> c \<turnstile>\<^sub>P (RECURSE n,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> ts"|
pPush: "c \<turnstile>\<^sub>P (PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x))" |
pPop: "stack x = Cons v vx \<Longrightarrow> c \<turnstile>\<^sub>P (POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := v), stack(x := vx))" 

bundle pbig_step_syntax
begin
notation pbig_step_t ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

code_pred pbig_step_t .

declare pbig_step_t.intros[intro]

lemmas pbig_step_t_induct = pbig_step_t.induct[split_format(complete)]

inductive_cases gsSkip_tE[elim!]: "c \<turnstile>\<^sub>P (pSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsAssign_tE[elim!]: "c \<turnstile>\<^sub>P (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases gsSeq_tE[elim!]: "c  \<turnstile>\<^sub>P (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases gsIf_tE[elim!]: "c \<turnstile>\<^sub>P (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsCall_tE[elim!]: "c \<turnstile>\<^sub>P (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases gsTail_tE[elim]: "c \<turnstile>\<^sub>P (RECURSE n,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsPush_tE[elim]: "c \<turnstile>\<^sub>P (PUSH v,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsPop_tE[elim]: "c \<turnstile>\<^sub>P (POP v,s) \<Rightarrow>\<^bsup>x \<^esup> t"

instantiation pcom :: vars
begin

fun vars_pcom :: "pcom \<Rightarrow> vname list" where
"vars_pcom (x ::= a)  = x # vars a" |
"vars_pcom (c\<^sub>1;;c\<^sub>2) = vars_pcom c\<^sub>1 @ vars_pcom c\<^sub>2" |
"vars_pcom (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars_pcom c1 @ vars_pcom c2" |
"vars_pcom (CALL c RETURN r) = r#vars c" |
"vars_pcom (PUSH x)  = [x]" |
"vars_pcom (POP x)  = [x]" |
"vars_pcom _ = []"

instance ..

end

lemma p_deterministic: 
  "d \<turnstile>\<^sub>P (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack') \<Longrightarrow> d \<turnstile>\<^sub>P (c,s,stack) \<Rightarrow>\<^bsup>z'\<^esup> (t',stack'') \<Longrightarrow> z = z' \<and> t = t' \<and> stack'' = stack'" 
proof (induction d c s stack z t stack' arbitrary: z' t' stack'' rule: pbig_step_t_induct)
  case (pIfTrue s b c c1 stack x t stack' y c2)
  then show ?case 
    by fastforce
next
  case (pIfFalse s b c c2 stack x t stack' y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>\<^sub>P (IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>z'\<^esup>  (t', stack'')\<close> obtain x' where
     \<open>c \<turnstile>\<^sub>P (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup>  (t', stack'')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t' \<and> stack'' = stack'\<close>
    using pIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> pIfFalse.hyps(3))
next
  case (pCall C s z t c r stack)
  then show ?case 
    using bigstep_det by blast
qed (blast | fastforce)+

lemma pnoninterference:
  "\<lbrakk>c' \<turnstile>\<^sub>P (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c' \<turnstile>\<^sub>P (c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),stack')"
proof (induction c' c s stack x t stack' rule: pbig_step_t_induct)
  case (pAssign c x a s stack)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using pbig_step_t.pAssign[of c x a "s(v:=y)" stack] by argo
next
  case (pCall C s z t c r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using pbig_step_t.pCall[OF Call, of c r] state by metis
next
  case (pPush c x s stack)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (PUSH x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_pcom.simps(5))
  hence \<open>(s(v := y)) x = s x\<close> by simp
  then show ?case 
    by (metis pbig_step_t.pPush)
next
  case (pPop stack x va vx c s)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (POP x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_pcom.simps(6))
  hence \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by auto
  have \<open>c \<turnstile>\<^sub>P (POP x, s(v := y), stack) \<Rightarrow>\<^bsup>Suc 0\<^esup>  (s(v := y,x := va), stack(x := vx))\<close>
    using \<open>stack x = va # vx\<close> pbig_step_t.pPop by simp
  then show ?case using \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by argo
qed auto+

fun 





end