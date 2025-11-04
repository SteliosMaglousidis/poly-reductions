theory IMP_Tailcall_Stacked
  imports IMP.IMP_Calls 
begin

unbundle no com_syntax and com'_syntax

declare [[syntax_ambiguity_warning=false]]

type_synonym stack = "val list" 

type_synonym fstack = "vname \<Rightarrow> stack"

text "Syntactic sugar to write stacks:"
definition empty_stack ("<[]>") where
  "empty_stack \<equiv> \<lambda>x. []"

datatype
  tscom = tsSKIP
      | tsPush  vname 
      | tsPop  vname 
      | tsAssign vname aexp
      | tsSeq    tscom  tscom
      | tsIf     vname tscom tscom
      | tsCall   com vname
      | tsTAIL

open_bundle tscom_syntax begin
notation tsSKIP ("SKIP") and
         tsAssign ("_ ::= _" [1000, 61] 61)  and
         tsSeq ("_;;/ _"  [60, 61] 60) and
         tsIf ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         tsCall ("CALL _ RETURN _") and
         tsTAIL ("TAIL") and
         tsPush ("PUSH _" [61] 61) and
         tsPop ("POP _" [61] 61)
end
unbundle no com'_syntax 

inductive
  tsbig_step_t :: "tscom \<Rightarrow> tscom \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tsSkip: "c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack)" |
tAssign: "c \<turnstile>(x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack)" |
tSeq: "\<lbrakk>c \<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2) ; c \<turnstile> (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3) ; z=x+y\<rbrakk> \<Longrightarrow> c \<turnstile> (c1;;c2, s1, stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3)" |
tIfTrue: "\<lbrakk>s b \<noteq> 0;  c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack')" |
tIfFalse: "\<lbrakk>s b = 0; c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack')" |
tCall: "(C,s) \<Rightarrow>\<^bsup> z \<^esup> t \<Longrightarrow> c \<turnstile> (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack)" |
\<comment> \<open>New rule\<close>
tTail: "c \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> ts \<Longrightarrow> c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> ts"|
tsPush: "c \<turnstile>(PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x))" |
tsPop: "stack x = Cons v vx \<Longrightarrow> c \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := v), stack(x := vx))" 

bundle tsbig_step_syntax
begin
notation tsbig_step_t ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

code_pred tsbig_step_t .

declare tsbig_step_t.intros[intro]

lemmas tsbig_step_t_induct = tsbig_step_t.induct[split_format(complete)]

inductive_cases tSkip_tE[elim!]: "c \<turnstile> (tsSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tAssign_tE[elim!]: "c \<turnstile> (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases tSeq_tE[elim!]: "c \<turnstile> (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases tIf_tE[elim!]: "c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tCall_tE[elim!]: "c \<turnstile> (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases tTail_tE[elim]: "c \<turnstile> (tsTAIL,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tPush_tE[elim]: "c \<turnstile> (PUSH v,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tPop_tE[elim]: "c \<turnstile> (POP v,s) \<Rightarrow>\<^bsup>x \<^esup> t"

instantiation tscom :: vars
begin

fun vars_tscom :: "tscom \<Rightarrow> vname list" where
"vars_tscom (x ::= a)  = x # vars a" |
"vars_tscom (c\<^sub>1;;c\<^sub>2) = vars_tscom c\<^sub>1 @ vars_tscom c\<^sub>2" |
"vars_tscom (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars_tscom c1 @ vars_tscom c2" |
"vars_tscom (CALL c RETURN r) = r#vars c" |
"vars_tscom (PUSH x)  = [x]" |
"vars_tscom (POP x)  = [x]" |
"vars_tscom _ = []"

instance ..

end

fun stails :: "tscom \<Rightarrow> bool" where
  "stails tsTAIL \<longleftrightarrow> True" |
  "stails (c1;;c2) \<longleftrightarrow> stails c1 \<or> stails c2" |
  "stails (IF b\<noteq>0 THEN c1 ELSE c2) \<longleftrightarrow> stails c1 \<or> stails c2" |
  "stails _ \<longleftrightarrow> False"

fun sinvar :: "tscom \<Rightarrow> bool" where
  "sinvar (c\<^sub>1;;c\<^sub>2) \<longleftrightarrow> \<not>stails c\<^sub>1 \<and> sinvar c\<^sub>2" |
  "sinvar (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> sinvar c\<^sub>1 \<and> sinvar c\<^sub>2" |
  "sinvar _ \<longleftrightarrow> True"

lemma no_stails_invar[simp]: "\<not>stails c \<Longrightarrow> sinvar c"
  by (induction c) auto

lemma ts_deterministic: 
  "d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack') \<Longrightarrow> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z'\<^esup> (t',stack'') \<Longrightarrow> z = z' \<and> t = t' \<and> stack'' = stack'" 
proof (induction d c s stack z t stack' arbitrary: z' t' stack'' rule: tsbig_step_t_induct)
  case (tIfTrue s b c c1 stack x t stack' y c2)
  then show ?case 
    by fastforce
next
  case (tIfFalse s b c c2 stack x t stack' y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>z'\<^esup>  (t', stack'')\<close> obtain x' where
     \<open>c \<turnstile> (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup>  (t', stack'')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t' \<and> stack'' = stack'\<close>
    using tIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> tIfFalse.hyps(3))
next
  case (tCall C s z t c r stack)
  then show ?case 
    using bigstep_det by blast
qed (blast | fastforce)+

lemma tsnoninterference:
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>(c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (r(v:=y),stack')"
proof (induction c' c s stack x r stack' rule: tsbig_step_t_induct)
  case (tAssign c x a s stack)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using tsbig_step_t.tAssign[of c x a "s(v:=y)" stack] by argo
next
  case (tCall C s z t c r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using tsbig_step_t.tCall[OF Call, of c r] state by metis
next
  case (tsPush c x s stack)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (PUSH x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_tscom.simps(5))
  hence \<open>(s(v := y)) x = s x\<close> by simp
  then show ?case 
    by (metis tsbig_step_t.tsPush)
next
  case (tsPop stack x va vx c s)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (POP x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_tscom.simps(6))
  hence \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by auto
  have \<open>c \<turnstile> (POP x, s(v := y), stack) \<Rightarrow>\<^bsup>Suc 0\<^esup>  (s(v := y,x := va), stack(x := vx))\<close>
    using \<open>stack x = va # vx\<close>  tsbig_step_t.tsPop by simp
  then show ?case using \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by argo
qed auto+

lemma tsnoninterference':
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r(v:= s v),stack')"
  using tsnoninterference by (metis fun_upd_triv)

lemma tsnoninterference_empty: 
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) = empty; set (vars c') = empty\<rbrakk> \<Longrightarrow> s = r"
  using tsnoninterference' by (metis empty_iff empty_subsetI ext fun_upd_idem_iff ts_deterministic)

lemma ts_stack_noninterference:
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>(c,s,stack(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'(v:=y))"
proof (induction c' c s stack x r stack' rule: tsbig_step_t_induct)
  case (tAssign c x a s stack)
  thus ?case by blast
next
  case (tCall C s z t c r stack)
  thus ?case by blast
next
  case (tsPush c x s stack)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (PUSH x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_tscom.simps(5))
  hence \<open>(stack(v := y)) x = stack x\<close> by simp
  then show ?case
    by (metis \<open>v \<noteq> x\<close> fun_upd_twist tsbig_step_t.tsPush)
next
  case (tsPop stack x va vx c s)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (POP x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_tscom.simps(6))
  hence \<open>(stack(v := y, x := vx)) = (stack(x := vx, v := y))\<close> by auto
  have \<open>c \<turnstile> (POP x, s, stack(v := y)) \<Rightarrow>\<^bsup>Suc 0\<^esup>  (s(x := va), stack(v := y,x := vx))\<close>
    using \<open>stack x = va # vx\<close>  tsbig_step_t.tsPop  \<open>v \<noteq> x\<close> by auto
  then show ?case using \<open>(stack(v := y, x := vx)) = (stack(x := vx, v := y))\<close> by argo
qed auto+

lemma ts_stack_noninterference':
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'(v:= stack v))"
  using ts_stack_noninterference by (metis fun_upd_triv)

lemma ts_stack_noninterference_empty: 
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) = empty; set (vars c') = empty\<rbrakk> \<Longrightarrow> stack = stack'"
  using ts_stack_noninterference' by (metis empty_iff empty_subsetI ext fun_upd_idem_iff ts_deterministic)

lemma tsnoninterference_override_on: 
"\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (r,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S\<rbrakk> \<Longrightarrow> r = override_on s r S"
  unfolding override_on_def by (metis (no_types, opaque_lifting) fun_upd_idem_iff ts_deterministic tsnoninterference')

lemma tPop_tE': 
  assumes "c \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s', stack')"
  obtains v vx where "stack x = Cons v vx" "s' x = v" "stack' x = vx"
  using assms by fastforce

lemma push_pop_idemp : " c' \<turnstile>(PUSH x ;; POP x,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s,stack)"
proof-
  have "c' \<turnstile>(PUSH x ,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s,stack(x := s x # stack x))" by auto
  have \<open>c' \<turnstile>(POP x ,s,stack(x := s x # stack x)) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := s x),stack(x :=  stack x))\<close>
    by (metis fun_upd_same fun_upd_upd tsPop)
  hence \<open>c' \<turnstile>(POP x ,s,stack(x := s x # stack x)) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s,stack)\<close>
    by simp
  then show ?thesis
    using \<open>c' \<turnstile>(PUSH x ,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s,stack(x := s x # stack x))\<close>
          \<open>c' \<turnstile>(POP x ,s,stack(x := s x # stack x)) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s,stack)\<close>
    by auto
qed

lemma push_pop : "c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack') \<Longrightarrow> c'\<turnstile>(PUSH x ;; POP x ;; c,s,stack) \<Rightarrow>\<^bsup>Suc (Suc z) \<^esup> (t,stack')"
  using push_pop_idemp by fastforce

lemma ts_seq_is_noop[simp]: "c' \<turnstile> (tsSKIP, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<longleftrightarrow> (t = Suc 0 \<and> s = s')" 
  by (metis surj_pair tSkip_tE tsSkip)

lemma ts_seq_skip[simp]: "c'\<turnstile> (c ;; tsSKIP, s,stack) \<Rightarrow>\<^bsup>Suc t\<^esup> (s',stack') \<longleftrightarrow> c'\<turnstile> (c, s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack')"
  by fastforce 

lemma pop_pushed: "c'\<turnstile>(POP x,s,stack(x := v # stack x)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s(x := v),stack)"
  by (metis (mono_tags, lifting) fun_upd_same fun_upd_triv fun_upd_upd tsPop)

lemma pop_pushed': "c'\<turnstile>(POP x,s',stack(x := (s x) # stack x)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s'(x := s x),stack)"
  by (metis pop_pushed)


section \<open>General recursion semantics for the stack language\<close>

inductive
  gsbig_step_t :: "tscom \<Rightarrow> tscom \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack \<Rightarrow> bool" ("_ \<turnstile>\<^sub>G\<^sub>s _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
gsSkip: "c \<turnstile>\<^sub>G\<^sub>s (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack)" |
gsAssign: "c \<turnstile>\<^sub>G\<^sub>s (x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack)" |
gsSeq: "\<lbrakk>c \<turnstile>\<^sub>G\<^sub>s (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2) ; c \<turnstile>\<^sub>G\<^sub>s (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3) ; z=x+y\<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>G\<^sub>s (c1;;c2, s1, stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3)" |
gsIfTrue: "\<lbrakk>s b \<noteq> 0;  c \<turnstile>\<^sub>G\<^sub>s (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>G\<^sub>s (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack')" |
gsIfFalse: "\<lbrakk>s b = 0; c \<turnstile>\<^sub>G\<^sub>s (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>G\<^sub>s (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack')" |
gsCall: "(C,s) \<Rightarrow>\<^bsup> z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>G\<^sub>s (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack)" |
\<comment> \<open>New rule\<close>
gsTail: "c \<turnstile>\<^sub>G\<^sub>s (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> ts \<Longrightarrow> c \<turnstile>\<^sub>G\<^sub>s (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> ts"|
gsPush: "c \<turnstile>\<^sub>G\<^sub>s (PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x))" |
gsPop: "stack x = Cons v vx \<Longrightarrow> c \<turnstile>\<^sub>G\<^sub>s (POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := v), stack(x := vx))" 

bundle gsbig_step_syntax
begin
notation gsbig_step_t ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

code_pred gsbig_step_t .

declare gsbig_step_t.intros[intro]

lemmas gsbig_step_t_induct = gsbig_step_t.induct[split_format(complete)]

inductive_cases gsSkip_tE[elim!]: "c \<turnstile>\<^sub>G\<^sub>s (tsSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsAssign_tE[elim!]: "c \<turnstile>\<^sub>G\<^sub>s (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases gsSeq_tE[elim!]: "c  \<turnstile>\<^sub>G\<^sub>s (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases gsIf_tE[elim!]: "c \<turnstile>\<^sub>G\<^sub>s (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsCall_tE[elim!]: "c \<turnstile>\<^sub>G\<^sub>s (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases gsTail_tE[elim]: "c \<turnstile>\<^sub>G\<^sub>s (tsTAIL,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsPush_tE[elim]: "c \<turnstile>\<^sub>G\<^sub>s (PUSH v,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases gsPop_tE[elim]: "c \<turnstile>\<^sub>G\<^sub>s (POP v,s) \<Rightarrow>\<^bsup>x \<^esup> t"

lemma gs_deterministic: 
  "d \<turnstile>\<^sub>G\<^sub>s (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack') \<Longrightarrow> d \<turnstile>\<^sub>G\<^sub>s (c,s,stack) \<Rightarrow>\<^bsup>z'\<^esup> (t',stack'') \<Longrightarrow> z = z' \<and> t = t' \<and> stack'' = stack'" 
proof (induction d c s stack z t stack' arbitrary: z' t' stack'' rule: gsbig_step_t_induct)
  case (gsIfTrue s b c c1 stack x t stack' y c2)
  then show ?case 
    by fastforce
next
  case (gsIfFalse s b c c2 stack x t stack' y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>\<^sub>G\<^sub>s (IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>z'\<^esup>  (t', stack'')\<close> obtain x' where
     \<open>c \<turnstile>\<^sub>G\<^sub>s (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup>  (t', stack'')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t' \<and> stack'' = stack'\<close>
    using gsIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> gsIfFalse.hyps(3))
next
  case (gsCall C s z t c r stack)
  then show ?case 
    using bigstep_det by blast
qed (blast | fastforce)+

lemma gsnoninterference:
  "\<lbrakk>c' \<turnstile>\<^sub>G\<^sub>s (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c' \<turnstile>\<^sub>G\<^sub>s (c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),stack')"
proof (induction c' c s stack x t stack' rule: gsbig_step_t_induct)
  case (gsAssign c x a s stack)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using gsbig_step_t.gsAssign[of c x a "s(v:=y)" stack] by argo
next
  case (gsCall C s z t c r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using gsbig_step_t.gsCall[OF Call, of c r] state by metis
next
  case (gsPush c x s stack)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (PUSH x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_tscom.simps(5))
  hence \<open>(s(v := y)) x = s x\<close> by simp
  then show ?case 
    by (metis gsbig_step_t.gsPush)
next
  case (gsPop stack x va vx c s)
  have \<open>v \<noteq> x\<close> using \<open>set (vars (POP x)) \<subseteq> S\<close> \<open>v \<notin> S\<close> 
    by (metis list.set_intros(1) subset_iff vars_tscom.simps(6))
  hence \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by auto
  have \<open>c \<turnstile>\<^sub>G\<^sub>s (POP x, s(v := y), stack) \<Rightarrow>\<^bsup>Suc 0\<^esup>  (s(v := y,x := va), stack(x := vx))\<close>
    using \<open>stack x = va # vx\<close> gsbig_step_t.gsPop by simp
  then show ?case using \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by argo
qed auto+


section \<open>Big step semantics that additionally count recursive calls\<close>

inductive
  tsbig_step_t_recs :: "tscom \<Rightarrow> tscom \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack \<times> nat \<Rightarrow> bool" ("_ \<turnstile>#REC _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
tsrSkip: "c \<turnstile>#REC (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,0)" |
tsrAssign: "c \<turnstile>#REC (x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,0)" |
tsrSeq: "\<lbrakk>c \<turnstile>#REC (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,n1) ; c \<turnstile>#REC (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3,n2) ; z=x+y ; n3 = n1 + n2\<rbrakk> \<Longrightarrow> c \<turnstile>#REC (c1;;c2, s1, stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3,n3)" |
tsrIfTrue: "\<lbrakk>s b \<noteq> 0; c \<turnstile>#REC (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile>#REC (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
tsrIfFalse: "\<lbrakk>s b = 0; c \<turnstile>#REC (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1\<rbrakk> \<Longrightarrow> c \<turnstile>#REC (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
tsrCall: "(C,s) \<Rightarrow>\<^bsup> z \<^esup> t \<Longrightarrow> c \<turnstile>#REC (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,0)" |
\<comment> \<open>New rule\<close>
tsrTail: "c \<turnstile>#REC (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s',stack',n) \<Longrightarrow> c \<turnstile>#REC (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (s',stack',Suc n)"|
tsrPush: "c \<turnstile>#REC (PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x),0)" |
tsrPop: "stack x = Cons v vx \<Longrightarrow> c \<turnstile>#REC (POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := v), stack(x := vx),0)" 

bundle tsbig_step_t_recs_syntax
begin
notation tsbig_step_t_recs ("_ \<turnstile>#REC _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

code_pred tsbig_step_t_recs .

declare tsbig_step_t_recs.intros[intro]

lemmas tsbig_step_t_recs_induct = tsbig_step_t_recs.induct[split_format(complete)]

inductive_cases tsSkip_tE[elim!]: "c \<turnstile>#REC (tsSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tsAssign_tE[elim!]: "c \<turnstile>#REC (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases tsSeq_tE[elim!]: "c \<turnstile>#REC (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases tsIf_tE[elim!]: "c \<turnstile>#REC (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tsCall_tE[elim!]: "c \<turnstile>#REC (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases tsTail_tE[elim]: "c \<turnstile>#REC (tsTAIL,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tsPush_tE[elim]: "c \<turnstile>#REC (PUSH v,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases tsPop_tE[elim]: "c \<turnstile>#REC (POP v,s) \<Rightarrow>\<^bsup>x \<^esup> t"

lemma tsrecs_deterministic: 
  "d \<turnstile>#REC (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n) \<Longrightarrow> d \<turnstile>#REC (c,s,stack) \<Rightarrow>\<^bsup>z'\<^esup> (t',stack'',n') \<Longrightarrow> z = z' \<and> t = t' \<and> stack'' = stack' \<and> n = n'" 
proof (induction d c s stack z t stack' n arbitrary: z' t' stack'' n' rule: tsbig_step_t_recs_induct)
  case (tsrIfTrue s b c c1 stack x t stack' y c2)
  then show ?case 
    by fastforce
next
  case (tsrIfFalse s b c c2 stack x t stack' n y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>#REC (IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>z'\<^esup>  (t', stack'',n')\<close> obtain x' where
     \<open>c \<turnstile>#REC (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup>  (t', stack'',n')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t' \<and> stack'' = stack' \<and> n = n'\<close>
    using tsrIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> tsrIfFalse.hyps(3))
next
  case (tsrCall C s z t c r stack)
  then show ?case 
    using bigstep_det by blast
qed (blast | fastforce)+

lemma tsrecs_sound: "d \<turnstile>#REC (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',n) \<Longrightarrow> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack')"
  by  (induction d c s stack t s' stack' n  rule: tsbig_step_t_recs_induct) blast+

lemma tsrecs_complete: "d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack') \<Longrightarrow> \<exists>n . d \<turnstile>#REC (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',n)"
  by (induction d c s stack t s' stack' rule: tsbig_step_t_induct) blast+

lemma tsrecs_correct: "\<exists>n . d \<turnstile>#REC (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',n) \<equiv> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack')" 
  by (smt (verit, del_insts) tsrecs_complete tsrecs_sound)

end


(*
lemma step_complete: 

lemma small_sound: "d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack') \<Longrightarrow> sinvar c \<Longrightarrow> sinvar d \<Longrightarrow> d \<turnstile>' (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack')"
proof (induction d c s stack z t stack' rule: tsbig_step_t_induct)
  case (tsSkip c s stack)
  then show ?case sorry
next
  case (tAssign c x a s stack)
  then show ?case sorry
next
  case (tSeq c c1 s1 stack1 x s2 stack2 c2 y s3 stack3 z)
  then show ?case sorry
next
  case (tIfTrue s b c c1 stack x t stack' y c2)
  then show ?case sorry
next
  case (tIfFalse s b c c2 stack x t stack' y c1)
  then show ?case sorry
next
  case (tCall C s z t c r stack)
  then show ?case sorry
next
  case (tTail c s stack z a b)
  then show ?case sorry
next
  case (tsPush c x s stack)
  then show ?case sorry
next
  case (tsPop stack x v vx c s)
  then show ?case sorry
qed
  case (tAssign c x a s stack)
  then show ?case by blast
next
  case (tSeq c c1 s1 ss1 x s2 ss2 c2 y s3 ss3 z)
  hence "c \<turnstile>'(c1, s1, ss1) \<Rightarrow>\<^bsup>x\<^esup>  (s2,ss2)" "c \<turnstile>'(c2, s2, ss2) \<Rightarrow>\<^bsup>y\<^esup>  (s3,ss3)" by auto
  from this tSeq show ?case 
    case tFalse
    hence \<open>\<turnstile>(c1;; c2, s1, ss1) \<Rightarrow>\<^bsup>z\<^esup>  (s3, ss3, )\<close>
    then show ?thesis 
  next
    case (tTrue x s2 stack2 y)
    then show ?thesis sorry
  qed
next
  case (tIfTrue s b c c1 ss x t st y c2)
  hence "c \<turnstile>'(c1, s, ss) \<Rightarrow>\<^bsup>x\<^esup>  (t, st)" by auto
  from this tIfTrue show ?case apply (cases) apply auto apply force
    by (metis Suc_eq_plus1 local.tIfTrue(1) plus_nat.simps(2) stail_step.IfTrue stail_steps.intros(2))
next
  case (tsPush c v i s stack)
  then show ?case by blast
next
  case (tsPop c v i s stack)
  then show ?case by blast
next
   case (tIfFalse s b c c2 ss x t st y c1)
  hence " c \<turnstile>'(c2, s, ss) \<Rightarrow>\<^bsup>x\<^esup>  (t, st)" by auto
  from this tIfFalse show ?case apply (cases) apply auto apply force
    by (metis Suc_eq_plus1 add_Suc tTrue stail_step.IfFalse)
next
  case (tTail c s ss z t ts)
  hence "c \<turnstile>'(c, s, ss) \<Rightarrow>\<^bsup>z\<^esup>  (t, ts)" by simp
  moreover have "\<turnstile>(tsTAIL,s,ss) \<Rightarrow>\<^bsup>5 \<^esup> (s,ss,True)"
    by (metis Tail)
  ultimately show ?case by auto
qed auto

lemma small_complete: "d \<turnstile>' (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> invar c \<Longrightarrow> invar d \<Longrightarrow> d \<turnstile> (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
proof (induction c s z t rule: tail_steps_induct)
  case (tFalse c s z t)
  then show ?case
    by (induction c s z t False rule: tail_step_induct) auto
next
  case (tTrue c s1 x s2 y s3)
  then show ?case
  proof (induction c s1 x s2 True arbitrary:  rule: tail_step_induct)
    case (Seq c1 s1 x s2 c2 y s3 z)
    then show ?case using no_tails_sem apply auto
      using ab_semigroup_add_class.add_ac(1) by blast
  qed auto
qed

unbundle no tscom_syntax and com'_syntax


lemma tnoninterference:
  "\<lbrakk>c'\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>(c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),stack')"
proof (induction c' c s stack x t stack' rule: tsbig_step_t_induct)
  case (tAssign c x a s stack)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using tsbig_step_t.tAssign[of c x a "s(v:=y)" stack] by argo
next
  case (tsPush c v i s stack)
  then show ?case 
    by (smt (verit, ccfv_SIG) fun_upd_def in_mono list.set_intros(1) tsbig_step_t.tsPush vars_tscom.simps(2))
next
  case (tsPop c v i s stack)
  then show ?case
    by (metis (no_types, lifting) fun_upd_twist list.set_intros(1) subset_code(1) tsbig_step_t.tsPop vars_tscom.simps(3))
next
  case (tCall C s z t c r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using tsbig_step_t.tCall[OF Call, of c r] state by metis
qed auto+

lemma noninterference':
  "\<lbrakk>\<turnstile>(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',b); set (vars c) \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> \<turnstile>(c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),stack',b)"
proof (induction c s stack x t stack' b rule: stail_step_induct)
  case (tssAssign x a s stack)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using stail_step.tssAssign[of  x a "s(v:=y)" stack] by argo
next
  case (tssPush v i s stack)
  then show ?case 
    by (smt (verit, ccfv_SIG) fun_upd_def in_mono list.set_intros(1) stail_step.tssPush vars_tscom.simps(2))
next
  case (tssPop v i s stack)
  then show ?case
    by (metis (no_types, lifting) fun_upd_twist list.set_intros(1) subset_code(1) stail_step.tssPop vars_tscom.simps(3))
next
  case (tssCall C s z t  r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from tCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using stail_step.tssCall[OF Call, of r] state by metis
qed auto+

lemma tnoninterference':
  "\<lbrakk>c'\<turnstile>'(c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack'); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>'(c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),stack')"
proof (induction c s stack x t stack' rule: stail_steps_induct)
  case (tFalse c s z t)
  then show ?case
    using noninterference' by blast
next
  case (tTrue c s1 x s2 y s3)
  then show ?case
    by (meson noninterference' stail_steps.tTrue)
qed

section \<open>Translation between tail-call program and while\<close>

fun translate1 :: "vname \<Rightarrow> tcom \<Rightarrow> com'" where
  "translate1 CONT tTAIL = (CONT ::= A (N 1))" |
  "translate1 CONT (tSeq c1 c2) = (translate1 CONT c1);; translate1 CONT c2" |
  "translate1 CONT (tIf b c1 c2) = (IF b\<noteq>0 THEN translate1 CONT c1 ELSE translate1 CONT c2)" |
  "translate1 CONT (tSKIP) = SKIP'" |
  "translate1 CONT (tAssign v a) = (v ::= a)" |
  "translate1 CONT (tCall c r) = Call' c r"

definition translate :: "vname \<Rightarrow> tcom \<Rightarrow> com'" where
  "translate CONT c = WHILE CONT\<noteq>0 DO (CONT::=A (N 0);;translate1 CONT c)"

lemma set_vars_translate1_subs:
  "set (vars (translate1 CONT c)) \<subseteq> insert CONT (set (vars c))"
  by (induction CONT c rule: translate1.induct) auto

lemma subs_set_vars_translate1:
  "set (vars c) \<subseteq> set (vars (translate1 CONT c))"
  by (induction CONT c rule: translate1.induct) auto

lemma set_vars_translate:
  "set (vars (translate CONT c)) = insert CONT (set (vars c))"
  unfolding translate_def
  using set_vars_translate1_subs subs_set_vars_translate1
  by fastforce

lemma no_tail_cont1: "\<lbrakk>(translate1 CONT c,s)\<Rightarrow>'\<^bsup>z\<^esup> t; \<not>tails c; CONT \<notin> set (vars c)\<rbrakk> \<Longrightarrow> t CONT = s CONT"
  by (induction c arbitrary: s t z) (auto, metis)

lemma no_tail_complete1: "\<lbrakk> (translate1 CONT c,s)\<Rightarrow>'\<^bsup>z\<^esup>t; \<not>tails c \<rbrakk> \<Longrightarrow> d \<turnstile> (c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
proof (induction "translate1 CONT c" s z t arbitrary: c rule: big_step_t'_induct)
  case (Skip' s)
  then show ?case by (cases c) auto
next
  case (Assign' x a s)
  then show ?case by (cases c) (auto simp del: fun_upd_apply)
next
  case (Seq' c1 s1 x s2 c2 y s3 z)
  then show ?case by (cases c) auto
next
  case (IfTrue' s b c1 x t y c2)
  then show ?case apply (cases c) using tIfTrue by auto
next
  case (IfFalse' s b c2 x t y c1)
  then show ?case apply (cases c) apply auto
    using Suc_eq_plus1 by blast
next
  case (WhileFalse' s b c)
  then show ?case by (cases c) auto
next
  case (WhileTrue' s1 b c x s2 y s3 z)
  then show ?case by (cases c) auto
next
  case (Call' c s z t r)
  then show ?case by (cases c) auto
qed

lemma no_tail_complete:
  assumes sem: "(translate1 CONT c;;translate CONT c',s)\<Rightarrow>'\<^bsup>2+z\<^esup>t"
      and no_tail: "\<not>tails c"
      and fresh: "CONT \<notin> set (vars c)"
      and start: "s CONT = 0"
    shows "d \<turnstile> (c,s)\<Rightarrow>\<^bsup>z\<^esup> t"
proof -
  from sem obtain t' x' y' where *:"(translate1 CONT c,s)\<Rightarrow>'\<^bsup>x'\<^esup>t'" "(translate CONT c',t')\<Rightarrow>'\<^bsup>y'\<^esup>t" "2 + z = x' + y'" by auto
  with fresh start have "t' CONT = 0"
    by (metis no_tail no_tail_cont1)
  with * have "t' = t" "y' = 2" by (auto simp: translate_def)
  with * no_tail no_tail_complete1 show ?thesis by auto
qed

lemma translate_sound_gen:
  "\<lbrakk> c' \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t; invar c; invar c'; s CONT = 0; CONT \<notin> S; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S\<rbrakk>
     \<Longrightarrow> (translate1 CONT c;;translate CONT c',s) \<Rightarrow>'\<^bsup>Suc(Suc 0)+z\<^esup> t"
proof (induction c' c s z t rule: tbig_step_t_induct)
  case (tAssign c x a s)
  then show ?case by (auto simp: translate_def simp del: fun_upd_apply) fastforce
next
  case (tSeq c c1 s1 x s2 c2 y s3 z)
  hence 1: "(translate1 CONT c1;; translate CONT c, s1) \<Rightarrow>'\<^bsup> Suc (Suc 0) + x\<^esup>  s2" by auto

  from 1 obtain s' x' y' where *:
    "(translate1 CONT c1, s1)\<Rightarrow>'\<^bsup> x'\<^esup>  s'"
    "(translate CONT c, s')\<Rightarrow>'\<^bsup> y'\<^esup> s2"
    "x' + y' = Suc (Suc 0) + x" by auto
  from * have s': "s' CONT = 0" using no_tail_cont1 using tSeq by auto (metis in_mono)
  with * have 11: "(translate1 CONT c1, s1) \<Rightarrow>'\<^bsup> x\<^esup>  s2"
    using translate_def by auto

  from s' * have "s2 CONT = 0"
    using tSeq by auto (metis "11" determ)
  with tSeq have 2: "(translate1 CONT c2;; translate CONT c, s2) \<Rightarrow>'\<^bsup> Suc (Suc 0) + y\<^esup>  s3"
    by auto

  from 11 2 have "(translate1 CONT c1 ;; (translate1 CONT c2;; translate CONT c), s1) \<Rightarrow>'\<^bsup> Suc (Suc 0) + z\<^esup>  s3"
    using \<open>z = x + y\<close> by auto

  then show ?case by auto
next
  case (tCall C s z t c r)
  then show ?case by (auto simp: translate_def simp del: fun_upd_apply) fastforce
next
  case (tTail c s z t)
  hence "(translate1 CONT c;; translate CONT c, s) \<Rightarrow>'\<^bsup> 2 + z\<^esup>  t" by auto
  moreover have "(CONT ::= A (N 0),s(CONT:=1)) \<Rightarrow>'\<^bsup> 2\<^esup> s"
  proof - (* wtf why is this not automatic *)
    have "(CONT ::= A (N 0),s(CONT:=1)) \<Rightarrow>'\<^bsup> 2\<^esup> s(CONT := 0)"
      using Assign'[of CONT "A (N 0)" "s(CONT:=1)"] by (auto simp: eval_nat_numeral)
    moreover from \<open>s CONT = 0\<close> have "s(CONT := 0) = s" by auto
    ultimately show ?thesis by simp
  qed
  ultimately have "((CONT ::= A (N 0);;translate1 CONT c);; translate CONT c, s(CONT:=1)) \<Rightarrow>'\<^bsup> 4 + z\<^esup>  t"
    by fastforce
  with while'_unrolling have "(translate CONT c, s(CONT:=1)) \<Rightarrow>'\<^bsup> 5 + z\<^esup>  t"
    unfolding translate_def by auto
  then show ?case by auto
qed (auto simp: translate_def)

lemma translate_sound:
  assumes c_sem: "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and invar: "invar c"
      and start: "s CONT \<noteq> 0"
      and fresh: "CONT \<notin> set (vars c)"
    shows "(translate CONT c,s) \<Rightarrow>'\<^bsup>5+z\<^esup> t(CONT:=0)"
proof -
  from c_sem fresh have c_sem2: "c \<turnstile> (c,s(CONT := 0)) \<Rightarrow>\<^bsup>z\<^esup> t(CONT:= 0)"
    using tnoninterference by blast

  have "(CONT::=A (N 0),s) \<Rightarrow>'\<^bsup>Suc (Suc 0)\<^esup> s(CONT:=0)" using Assign'[of CONT "A (N 0)" s] by simp

  moreover have "(translate1 CONT c;; translate CONT c, s(CONT:=0)) \<Rightarrow>'\<^bsup> 2+z\<^esup> t(CONT := 0)"
    using translate_sound_gen c_sem2 invar fresh by simp

  ultimately have "((CONT::=A (N 0);;translate1 CONT c);; translate CONT c, s) \<Rightarrow>'\<^bsup> 4+z\<^esup> t(CONT := 0)"
    apply (simp add: numeral_eq_Suc)
    by (smt (verit, ccfv_SIG) Seq'_tE add.assoc add_2_eq_Suc big_step_t'.Seq' numeral_2_eq_2)
  then show "(translate CONT c,s) \<Rightarrow>'\<^bsup>5+z\<^esup> t(CONT := 0)" using while'_unrolling start translate_def by auto
qed

lemma translate1_complete:
  "\<lbrakk> (translate1 CONT c,s)\<Rightarrow>'\<^bsup>z\<^esup>t; s CONT = 0; invar c; set (vars c) \<subseteq> S; CONT \<notin> S \<rbrakk>
     \<Longrightarrow> (if t CONT \<noteq> 0 then \<turnstile>(c,s) \<Rightarrow>\<^bsup>3+z\<^esup> (t(CONT := s CONT),True) else \<turnstile>(c,s) \<Rightarrow>\<^bsup>z\<^esup> (t,False))"
proof (induction "translate1 CONT c" s z t arbitrary: c rule: big_step_t'_induct)
  case (Skip' s)
  then show ?case by (cases c) auto
next
  case (Assign' x a s)
  thus ?case apply (cases c) apply (auto split: if_splits)
    by (metis Tail fun_upd_triv)
next
  case (Seq' c1 s1 x s2 c2 y s3 z)
  then show ?case
    apply (cases c)
         apply (auto split: if_splits)
    subgoal
      by (smt (verit, best) Seq'.hyps(2) add.left_commute no_tails_invar no_tails_no_step tail_step.Seq)
    subgoal
      by (metis Seq'.hyps(2) no_tails_invar no_tails_no_step tail_step.Seq)

    done
next
  case (IfTrue' s b c1 x t y c2)
  then show ?case apply (cases c) apply (auto split: if_splits)
    subgoal
      by (smt (verit) IfTrue'.hyps(1) One_nat_def Suc_1 Suc_eq_plus1 numeral.simps(2) numeral_3_eq_3 plus_1_eq_Suc plus_nat.simps(2) tail_step.IfTrue)
    subgoal
      using IfTrue'.hyps by blast

    done
next
  case (IfFalse' s b c2 x t y c1)
  then show ?case apply (cases c) apply (auto split: if_splits)
    subgoal
          by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_eq_plus1 numeral.simps(2) numeral_3_eq_3 plus_1_eq_Suc plus_nat.simps(2) tail_step.IfFalse)
    subgoal using IfFalse'.hyps by blast

    done
next
  case (WhileFalse' s b c)
  then show ?case apply (cases c) apply auto done
next
  case (WhileTrue' s1 b c x s2 y s3 z)
  then show ?case apply (cases c) apply auto done
next
  case (Call' c s z t r)
  then show ?case apply (cases c) apply auto done
qed

lemma loop_min: "(WHILE b\<noteq>0 DO c, s) \<Rightarrow>'\<^bsup> z\<^esup>  t \<Longrightarrow> (c,s) \<Rightarrow>'\<^bsup>x\<^esup> s2 \<Longrightarrow> s b \<noteq> 0 \<Longrightarrow> z \<ge> 3+x"
  apply (induction "WHILE b\<noteq>0 DO c" s z t rule: big_step_t'_induct) apply simp using determ by fastforce

lemma translate_complete:
  "\<lbrakk> (translate CONT c,s)\<Rightarrow>'\<^bsup>5+z\<^esup>t; s CONT \<noteq> 0; invar c; CONT \<notin> set (vars c) \<rbrakk>
    \<Longrightarrow> c \<turnstile>'(c,s) \<Rightarrow>\<^bsup>z\<^esup> t(CONT:= s CONT)"
proof (induction "translate CONT c" s "5+z" t arbitrary: z rule: big_step_t'_induct)
  case (WhileTrue' s1 b c' x s2 y s3 )

  hence c'_def: "c' = CONT::=A (N 0);;translate1 CONT c" and b_def: "b = CONT" by (auto simp: translate_def)

  have 0: "(CONT::=A (N 0),s1) \<Rightarrow>'\<^bsup>Suc (Suc 0)\<^esup>s1(CONT := 0)"
    using Assign'[of CONT "A (N 0)" s1,simplified] by (simp add: numeral_eq_Suc)

  obtain x' where 1:
    "x' + Suc (Suc 0) = x" "(translate1 CONT c,s1(CONT:=0))\<Rightarrow>'\<^bsup> x'\<^esup>s2"
    using WhileTrue'.hyps (2)[unfolded c'_def] by auto

  show ?case proof (cases "s2 CONT = 0")
    case True
    hence "\<turnstile>(c,s1(CONT:=0)) \<Rightarrow>\<^bsup>x'\<^esup> (s2,False)" using translate1_complete 1 WhileTrue' by fastforce

    moreover from \<open>(WHILE b\<noteq>0 DO c', s2) \<Rightarrow>'\<^bsup> y\<^esup>  s3\<close> have "s2 = s3" "y = Suc (Suc 0)" using True b_def by auto
    ultimately have "\<turnstile>(c,s1) \<Rightarrow>\<^bsup>x'\<^esup> (s3(CONT := s1 CONT),False)"
      using WhileTrue' noninterference'
      by (smt (verit, ccfv_threshold) fun_upd_idem_iff fun_upd_upd order_le_less)
    hence "c \<turnstile>'(c, s1) \<Rightarrow>\<^bsup>x'\<^esup>  s3(CONT := s1 CONT)" by auto
    moreover from  \<open>x' + Suc (Suc 0) = x\<close> \<open>1 + x + y = 5+z\<close> \<open>y = Suc (Suc 0)\<close> have "x' = z" by simp
    ultimately show ?thesis by blast
  next
    case False
    with \<open>(WHILE b\<noteq>0 DO c', s2) \<Rightarrow>'\<^bsup> y\<^esup>  s3\<close> obtain s2' z' where "(c',s2) \<Rightarrow>'\<^bsup>z'\<^esup> s2'"
      using b_def by auto
    hence "z' \<ge> 2" unfolding c'_def by auto
    with loop_min have "y \<ge> 5"
      using False WhileTrue'.hyps(4) \<open>(c', s2) \<Rightarrow>'\<^bsup> z'\<^esup> s2'\<close> b_def by fastforce
    then obtain y' where y'_def: "y = 5 + y'"
      using nat_le_iff_add by blast
    from 1 have 2: "\<turnstile>(c,s1(CONT:=0)) \<Rightarrow>\<^bsup>1+x\<^esup> (s2(CONT := 0), True)"
      using translate1_complete[of CONT c "s1(CONT := 0)" x' s2] False WhileTrue' by (auto simp: numeral_eq_Suc)

    from False WhileTrue' y'_def have "c \<turnstile>'(c, s2) \<Rightarrow>\<^bsup>y'\<^esup>  s3(CONT := s2 CONT)" by auto
    hence 3: "c \<turnstile>'(c, s2(CONT := 0)) \<Rightarrow>\<^bsup>y'\<^esup>  s3(CONT := 0)"
      using tnoninterference' WhileTrue' by (metis fun_upd_upd order.refl)

    from \<open>1 + x + y = 5 + z\<close> y'_def have "c \<turnstile>'(c, s1(CONT := 0)) \<Rightarrow>\<^bsup>z\<^esup>  s3(CONT := 0)"
      using tTrue[OF 2 3] by simp

    then show ?thesis using  WhileTrue' tnoninterference'
      by (metis (mono_tags, lifting) dual_order.refl fun_upd_triv fun_upd_upd)
  qed
qed (auto simp: translate_def)


section \<open>Final compilation\<close>
definition compile :: "tcom \<Rightarrow> com'" where
  "compile c = (let CONT = fresh (vars c) ''CONTINUE'' in CONT::=A (N 1);;translate CONT c)"

lemma set_vars_compile:
  "set (vars (compile c)) = insert (fresh (vars c) ''CONTINUE'') (set (vars c))"
  unfolding compile_def Let_def by (simp add: set_vars_translate)

lemma compile_sound:
  assumes c_sem: "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t"
      and invar: "invar c"
  obtains t' where "(compile c,s) \<Rightarrow>'\<^bsup>7+z\<^esup> t'" and "t = t' on set (vars c)"
proof -
  let ?CONT="fresh (vars c) ''CONTINUE''"
  have 1: "(?CONT::=A (N 1),s) \<Rightarrow>'\<^bsup>2\<^esup> s(?CONT:=1)"
    using Assign'[of ?CONT "A (N 1)" s] by (auto simp: eval_nat_numeral)
  from c_sem have "c \<turnstile> (c,s(?CONT:=1))\<Rightarrow>\<^bsup>z\<^esup> t(?CONT:=1)"
    using fresh tnoninterference by (meson dual_order.refl)

  hence "(translate ?CONT c, s(?CONT:=1)) \<Rightarrow>'\<^bsup> 5 + z\<^esup> t(?CONT := 0)"
    using translate_sound invar fresh by (fastforce simp: numeral_eq_Suc)

  hence "(compile c,s)\<Rightarrow>'\<^bsup> 7 + z\<^esup> t(?CONT := 0)" unfolding compile_def
    using 1 apply (simp add: numeral_eq_Suc)
    by (smt (verit, best) IMP_Calls.Seq'' add_2_eq_Suc numeral_2_eq_2)

  with that show ?thesis by simp
qed


lemma compile_complete_add:
  assumes sem: "(compile c,s) \<Rightarrow>'\<^bsup>z + 7\<^esup> t"
      and invar: "invar c"
  obtains t' where "c \<turnstile> (c,s)\<Rightarrow>\<^bsup>z\<^esup> t'" and "t = t' on set (vars c)"
proof -
  let ?CONT="fresh (vars c) ''CONTINUE''"
  have 1: "(?CONT::=A (N 1),s) \<Rightarrow>'\<^bsup>2\<^esup> s(?CONT:=1)"
    using Assign'[of ?CONT "A (N 1)" s] by (auto simp: eval_nat_numeral)

  with sem[unfolded compile_def] have "(translate ?CONT c, s(?CONT:=1)) \<Rightarrow>'\<^bsup> 5 + z\<^esup> t"
    unfolding compile_def apply (auto simp: numeral_eq_Suc) using Seq'_tE
    by (smt (verit, best) "1" Assign'_tE One_nat_def add_Suc add_left_imp_eq plus_1_eq_Suc)

  hence "c \<turnstile> (c,s(?CONT:=1)) \<Rightarrow>\<^bsup>z\<^esup> t(?CONT:=1)"
    using translate_complete small_complete fresh invar by (fastforce simp: numeral_eq_Suc)

  hence "c \<turnstile> (c,s) \<Rightarrow>\<^bsup>z\<^esup> t(?CONT:=s ?CONT)"
    using tnoninterference[where S="set (vars c)"] fresh invar apply auto
    by (smt (verit, best) dual_order.refl fresh fun_upd_triv fun_upd_upd)

  with that show ?thesis using fresh by auto
qed

lemma compile_time_7_le:
  assumes "(compile c,s) \<Rightarrow>'\<^bsup>z\<^esup> t"
  shows "7 \<le> z"
  using assms
proof (induction "compile c" s z t arbitrary: c rule: big_step_t'_induct)
case (Seq' c1 s1 x s2 c2 y s3 z)
then show ?case
  apply (auto simp: compile_def Let_def translate_def)
  apply (erule While'_tE)
  apply auto
  done
qed (auto simp: compile_def Let_def translate_def)

lemma compile_complete:
  assumes "(compile c,s) \<Rightarrow>'\<^bsup>z\<^esup> t"
      and "invar c"
  obtains t' where "c \<turnstile> (c,s)\<Rightarrow>\<^bsup>z - 7\<^esup> t'" and "t = t' on set (vars c)"
  using assms compile_complete_add compile_time_7_le
  by (metis add.commute le_add_diff_inverse)

end *)