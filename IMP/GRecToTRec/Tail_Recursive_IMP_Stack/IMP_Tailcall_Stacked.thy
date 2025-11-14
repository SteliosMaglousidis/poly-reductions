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

abbreviation if_equals_var ("(IF _/=_ ON _ THEN _/ ELSE _ )"  [0, 0, 0, 0, 61] 61) where
"if_equals_var x v b c1 c2  \<equiv> ((b ::= Sub (V x) (V v)) ;; IF b\<noteq>0 THEN c1 ELSE c2)"

abbreviation if_equals ("(IF _/=_ ON _ THEN _/ ELSE _ )"  [0, 0, 0, 0, 61] 61) where
"if_equals x v b c1 c2  \<equiv> ((b ::= Sub (V x) (N v)) ;; (IF b\<noteq>0 THEN c1 ELSE c2))"

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
