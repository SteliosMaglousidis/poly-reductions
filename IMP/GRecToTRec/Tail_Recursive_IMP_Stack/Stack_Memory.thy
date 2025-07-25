theory Stack_Memory
  imports IMP_Tailcall_Stacked
begin

unbundle tscom_syntax

text \<open>Big-step semantics that count push commands to a specific stack\<close>
inductive
  push_count :: "vname \<Rightarrow> tscom \<Rightarrow> (tscom \<times> state \<times> fstack) \<Rightarrow> nat \<Rightarrow> (state \<times> fstack \<times> nat) \<Rightarrow> bool" ("# _ PUSH _ \<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "# v PUSH c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,0)" |
Assign: "# v PUSH c \<turnstile>(x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,0)" |
Seq: "\<lbrakk># v PUSH c \<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,n1); # v PUSH c \<turnstile> (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3,n2) ; z=x+y \<rbrakk> \<Longrightarrow> # v PUSH c \<turnstile> (c1;;c2,s1,stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3,n1+n2)" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  # v PUSH c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1 \<rbrakk> \<Longrightarrow> # v PUSH c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
IfFalse: "\<lbrakk> s b = 0; # v PUSH c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1  \<rbrakk> \<Longrightarrow> # v PUSH c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> # v PUSH c \<turnstile> (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,0)" |
Tail: "# v PUSH c \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n) \<Longrightarrow> # v PUSH c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (t,stack',n)"|
Push: "# v PUSH c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s,stack(x := s x # stack x),(if x = v then 1 else 0))" |
Pop: "stack x = Cons vx vxs \<Longrightarrow>  # v PUSH c \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := vx), stack(x := vxs), 0)" 

code_pred push_count .

declare push_count.intros[intro]

lemmas push_count_induct = push_count.induct[split_format(complete)]

inductive_cases pcSkip_tE[elim!]: "# y PUSH c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"
inductive_cases pcAssign_tE[elim!]: "# y PUSH c \<turnstile> (x ::= a,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"
inductive_cases pcPush_tE[elim!]: "# y PUSH c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"
inductive_cases pcPop_tE[elim!]: "# y PUSH c \<turnstile> (POP x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"
inductive_cases pcSeq_tE[elim!]: "# y PUSH c \<turnstile> (c1;;c2,s1,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"
inductive_cases pcIf_tE[elim!]: "# y PUSH c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"
inductive_cases pcCall_tE[elim!]: "# y PUSH c \<turnstile> (CALL C RETURN v,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',m)"
inductive_cases pcTail_tE[elim]: "# y PUSH c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',m)"

lemma push_count_monotone: "# i PUSH d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',m) \<Longrightarrow> m \<ge> 0"
  by (induction i d c s stack x t stack' m rule: push_count_induct) auto

lemma push_count_sound: "# i PUSH d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',m) 
                     \<Longrightarrow> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')"
  by (induction i d c s stack x t stack' m rule: push_count_induct) blast+

lemma push_count_deterministic: "# i PUSH d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',m) 
                             \<Longrightarrow> # i PUSH d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t',stack'',m')
                             \<Longrightarrow> t = t' \<and> stack' = stack'' \<and> m = m'"
proof (induction i d c s stack x t stack' m arbitrary: t' stack'' m' rule: push_count_induct)
  case (Pop i c v j s stack n)
  then show ?case by auto
next
  case (Seq v c c1 s1 stack1 x s2 stack2 n1 c2 y s3 stack3 n2 z i)
  then show ?case 
    by (smt (verit, ccfv_SIG) pcSeq_tE push_count_sound ts_deterministic)
next
  case (IfTrue s b i c c1 stack n x t stack' m y c2)
  then show ?case by fastforce
next
  case (IfFalse s b i c c2 stack n x t stack' m y c1)
  then show ?case 
    by (metis add_diff_cancel_left' diff_add_inverse2 less_numeral_extra(3) pcIf_tE
        plus_1_eq_Suc)
next
  case (Call C s z t i c r stack n)
  then show ?case 
    using bigstep_det by blast
next
  case (Tail i c s stack n z t stack' m)
  then show ?case
    by (metis add_left_cancel pcTail_tE)
qed blast+


text \<open>Big-step semantics that count pop commands to a specific stack\<close>
inductive
  pop_count :: "vname \<Rightarrow> tscom \<Rightarrow> (tscom \<times> state \<times> fstack) \<Rightarrow> nat \<Rightarrow> (state \<times> fstack \<times> nat) \<Rightarrow> bool" ("# _ POP _ \<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "# v POP c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,0)" |
Assign: "# v POP c \<turnstile>(x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,0)" |
Seq: "\<lbrakk># v POP c \<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,n1); # v POP c \<turnstile> (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3,n2) ; z=x+y \<rbrakk> \<Longrightarrow> # v POP c \<turnstile> (c1;;c2,s1,stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3,n1 + n2)" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  # v POP c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1 \<rbrakk> \<Longrightarrow> # v POP c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
IfFalse: "\<lbrakk> s b = 0; # v POP c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1  \<rbrakk> \<Longrightarrow> # v POP c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> # v POP c \<turnstile> (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,0)" |
tTail: "# v POP c \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n) \<Longrightarrow> # v POP c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (t,stack',n)"|
Push: "# v POP c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack(x := s x # stack x),0)" | 
Pop: "stack x = Cons vx vxs \<Longrightarrow>  # v POP c \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := vx), stack(x := vxs), if x = v then 1 else 0)" 

code_pred pop_count .

declare pop_count.intros[intro]

lemmas pop_count_induct = pop_count.induct[split_format(complete)]

inductive_cases popcSkip_tE[elim!]: "# v POP c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases popcAssign_tE[elim!]: "# v POP c \<turnstile> (x ::= a,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases popcSeq_tE[elim!]: "# v POP c \<turnstile> (c1;;c2,s1,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases popcIf_tE[elim!]: "# v POP c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases popcCall_tE[elim!]: "# v POP c \<turnstile> (CALL C RETURN v,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n)"
inductive_cases popcTail_tE[elim]: "# v POP c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases popcPush_tE[elim!]: "# v POP c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases popcPop_tE[elim!]: "# v POP c \<turnstile> (POP x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"

      
lemma pop_count_monotone: "# i POP d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',m) \<Longrightarrow> m \<ge> 0"
  by auto


lemma pop_count_sound: "# i POP d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',m) 
                     \<Longrightarrow> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')"
  by (induction i d c s stack x t stack' m rule: pop_count_induct) blast+


text \<open>Intuition is to track how much the stack "forgets" and how much more it "remembers"\<close>
inductive
  stack_memory :: "vname \<Rightarrow> tscom \<Rightarrow> (tscom \<times> state \<times> fstack) \<Rightarrow> nat \<Rightarrow> (state \<times> fstack \<times> int) \<Rightarrow> bool" ("_ STACK _ \<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "v STACK c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,0)" |
Assign: "v STACK c \<turnstile>(x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,0)" |
Seq: "\<lbrakk>v STACK c \<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,n1); v STACK c \<turnstile> (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3,n2) ; z=x+y \<rbrakk> \<Longrightarrow> v STACK c \<turnstile> (c1;;c2,s1,stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3,n1 + n2)" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  v STACK c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1 \<rbrakk> \<Longrightarrow> v STACK c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
IfFalse: "\<lbrakk> s b = 0;  v STACK c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1  \<rbrakk> \<Longrightarrow>  v STACK c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow>  v STACK c \<turnstile> (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,0)" |
tTail: "v STACK c \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n) \<Longrightarrow> v STACK c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (t,stack',n)"|
Push: "v STACK c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack(x := s x # stack x),if x = v then 1 else 0)" | 
Pop: "stack x = Cons vx vxs \<Longrightarrow>  v STACK c \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := vx), stack(x := vxs),if x = v then -1 else 0)" 

code_pred stack_memory .

declare stack_memory.intros[intro]

lemmas stack_memory_induct = stack_memory.induct[split_format(complete)]

inductive_cases smSkip_tE[elim!]: "v STACK c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases smAssign_tE[elim!]: "v STACK c \<turnstile> (x ::= a,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases smSeq_tE[elim!]: "v STACK c \<turnstile> (c1;;c2,s1,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases smIf_tE[elim!]: "v STACK c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases smCall_tE[elim!]: "v STACK c \<turnstile> (CALL C RETURN v,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n)"
inductive_cases smTail_tE[elim]: "v STACK c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases smPush_tE[elim!]: "v STACK c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases smPop_tE[elim!]: "v STACK c \<turnstile> (POP x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"

lemma memory_count: "v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)  \<Longrightarrow> n = int (length (stack' v)) - int (length (stack v))"
by (induction v d c s stack x t stack' n rule: stack_memory_induct) auto

lemma kappa : "n1 < 0 \<Longrightarrow> n2 \<ge> 0 \<Longrightarrow> nat (n1 + n2) = nat(n2) - nat (-n1)"
  by simp

lemma stack_memory_sound: "v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n) 
                     \<Longrightarrow> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')"
  by (induction v d c s stack x t stack' n  rule: stack_memory_induct) blast+


lemma stack_memory_complete: "d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack') 
                              \<Longrightarrow> v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',int (length (stack' v)) - int (length (stack v))) "
  apply (induction d c s stack x t stack' arbitrary: v rule: tsbig_step_t_induct) 
  using memory_count apply auto
        apply (smt (verit, best) stack_memory.Seq)
  apply fastforce
      apply fastforce
  using stack_memory.Push apply presburger
  using stack_memory.Push apply presburger
  using stack_memory.Pop apply presburger
  using stack_memory.Pop by presburger

lemma stack_memory_deterministic: "v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n) 
                              \<Longrightarrow> v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t',stack'',m)
                              \<Longrightarrow> t = t' \<and> stack' = stack'' \<and> x = y \<and> n = m"
  using stack_memory_sound stack_memory_complete ts_deterministic by (metis memory_count)


text \<open>Intuition is to track how much the stack "forgets" and how much more it "remembers"\<close>
inductive
  stack_forget :: "vname \<Rightarrow> tscom \<Rightarrow> (tscom \<times> state \<times> fstack) \<Rightarrow> nat \<Rightarrow> (state \<times> fstack \<times> int) \<Rightarrow> bool" ("_ FORGET _ \<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "v FORGET c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,0)" |
Assign: "v FORGET c \<turnstile>(x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,0)" |
Seq: "\<lbrakk>v FORGET c \<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,m1); 
       v STACK c \<turnstile> (c1,s1,stack1) \<Rightarrow>\<^bsup>x \<^esup> (s2,stack2,n1); v STACK c \<turnstile> (c2,s2,stack2) \<Rightarrow>\<^bsup>y \<^esup> (s3,stack3,n2) ; z=x+y \<rbrakk> 
    \<Longrightarrow> v FORGET c \<turnstile> (c1;;c2,s1,stack1) \<Rightarrow>\<^bsup>z \<^esup> (s3,stack3, m1 + (if n2 < 0 then n1 + n2 else 0))" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  v FORGET c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1 \<rbrakk> \<Longrightarrow> v FORGET c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
IfFalse: "\<lbrakk> s b = 0;  v FORGET c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n); y=x+1  \<rbrakk> \<Longrightarrow>  v FORGET c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack',n)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow>  v FORGET c \<turnstile> (CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,0)" |
tTail: "v FORGET c \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n) \<Longrightarrow> v FORGET c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (t,stack',n)"|
Push: "v FORGET c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack(x := s x # stack x),0)" | 
Pop: "stack x = Cons vx vxs \<Longrightarrow>  v FORGET c \<turnstile>(POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := vx), stack(x := vxs),if x = v then 1 else 0)" 

code_pred stack_forget .

declare stack_forget.intros[intro]

lemmas stack_forget_induct = stack_forget.induct[split_format(complete)]

inductive_cases sfSkip_tE[elim!]: "v FORGET c \<turnstile> (tsSKIP,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases sfAssign_tE[elim!]: "v FORGET c \<turnstile> (x ::= a,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases sfSeq_tE[elim!]: "v FORGET c \<turnstile> (c1;;c2,s1,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases sfIf_tE[elim!]: "v FORGET c \<turnstile> (IF b \<noteq>0 THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases sfCall_tE[elim!]: "v FORGET c \<turnstile> (CALL C RETURN v,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',n)"
inductive_cases sfTail_tE[elim]: "v FORGET c \<turnstile> (tsTAIL,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n)"
inductive_cases sfPush_tE[elim!]: "v FORGET c \<turnstile> (PUSH x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"
inductive_cases sfPop_tE[elim!]: "v FORGET c \<turnstile> (POP x,s,stack) \<Rightarrow>\<^bsup>p \<^esup> (t,stack',n)"


lemma stack_forget_sound: "v FORGET d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n) 
                     \<Longrightarrow> d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')"
  apply (induction v d c s stack x t stack' n rule: stack_forget_induct)
  apply blast
         apply blast
        apply (meson stack_memory_sound tSeq)
  by blast+


lemma stack_memory_deterministic: "v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',n) 
                              \<Longrightarrow> v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t',stack'',m)
                              \<Longrightarrow> t = t' \<and> stack' = stack'' \<and> x = y \<and> n = m"
  using stack_memory_sound stack_memory_complete ts_deterministic by (metis memory_count)


lemma take_drop: "(take n xs) @ ys = xs \<equiv> ys = drop n xs"
  by (smt (verit, ccfv_threshold) append_take_drop_id same_append_eq)

lemma 1: assumes "v STACK c \<turnstile>(c1, s1, stack1) \<Rightarrow>\<^bsup>x\<^esup>  (s2, stack2, n1)" and
    "v STACK c \<turnstile>(c2, s2, stack2) \<Rightarrow>\<^bsup>y\<^esup>  (s3, stack3, n2) " and
    "z = x + y " and
    "take (nat (- n1)) (stack1 v) @ stack2 v = stack1 v" and
    "take (nat n2) (stack3 v) @ stack2 v = stack3 v"
    "0 \<le> n1 + n2"  "\<not> 0 \<le> n1"  "n2 \<ge> 0"
  shows "take (nat (n1 + n2)) (stack3 v) @ stack1 v = stack3 v"
proof-
  have \<open>stack2 v = drop (nat (-n1)) (stack1 v)\<close> 
    using Stack_Memory.take_drop assms(4) by blast
  have \<open>stack2 v = drop (nat n2) (stack3 v)\<close> 
    using Stack_Memory.take_drop assms(5) by blast
  from  \<open>stack2 v = drop (nat (-n1)) (stack1 v)\<close>  \<open>stack2 v = drop (nat n2) (stack3 v)\<close>
  have \<open>drop (nat (-n1)) (stack1 v) =  drop (nat n2) (stack3 v)\<close> by metis

  from this \<open>take (nat n2) (stack3 v) @ stack2 v = stack3 v\<close> 
  have \<open>take (nat n2) (stack3 v) @ (drop (nat (-n1)) (stack1 v)) = stack3 v\<close>
    by simp
  then show ?thesis try


lemma stack_memory: "v STACK d \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (t,stack',n) \<Longrightarrow> 
  (if n \<ge> 0 then (take (nat n) (stack' v)) @ (stack v) = stack' v else 
                  (take (nat (-n)) (stack v)) @ (stack' v) = stack v)"
proof (induction v d c s stack x t stack' n rule: stack_memory_induct)
  case (Skip v c s stack)
  then show ?case by simp
next
  case (Assign v c x a s stack)
  then show ?case by simp
next
  case (Seq v c c1 s1 stack1 x s2 stack2 n1 c2 y s3 stack3 n2 z)
  then show ?case apply auto apply (cases "n1 \<ge> 0")
      apply auto
      apply (cases "n2 \<ge> 0")
    apply auto 
    apply (smt (verit, best) append_eq_appendI append_take_drop_id nat_add_distrib same_append_eq
        take_add)
      apply (smt (verit, best) append_take_drop_id drop_drop nat_add_distrib same_append_eq)
     apply (cases "n2 \<ge> 0")
      apply auto
    subgoal
        
    apply (cases "n1 \<ge> 0")
    apply auto
      apply (cases "n2 \<ge> 0")
      apply auto 
    using memory_count apply force
    using memory_count by force
next
  case (IfTrue s b v c c1 stack x t stack' n y c2)
  then show ?case  by simp
next
  case (IfFalse s b v c c2 stack x t stack' n y c1)
  then show ?case  by simp
next
  case (Call C s z t v c r stack)
  then show ?case  by simp
next
  case (tTail v c s stack z t stack' n)
  then show ?case  by simp
next
  case (Push v c x s stack)
  then show ?case  by simp
next
  case (Pop stack x vx vxs v c s)
  then show ?case try
qed

 
lemma push_count_step: "# i PUSH c \<turnstile> (c,s,stack,n) \<Rightarrow>\<^bsup>x \<^esup> (t,stack',m) 
                    \<Longrightarrow> # i PUSH c \<turnstile> (v ::\<Rightarrow> i ;; c ,s,stack,n) \<Rightarrow>\<^bsup>x \<^esup> (t,stack', m + 1)"



lemma "# i POP d \<turnstile> (c,s,stack,n) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',m) 
   \<Longrightarrow> # i PUSH d \<turnstile> (c,s,stack,n) \<Rightarrow>\<^bsup>z \<^esup> (t,stack',m)
   \<Longrightarrow> length stack > i 
   \<Longrightarrow> d \<turnstile> (c,s,push_i i (s v) stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack')
   \<Longrightarrow> d \<turnstile> ((v ::\<Rightarrow> i);; c ;; (v \<Leftarrow>:: i),s,stack) \<Rightarrow>\<^bsup>z \<^esup> (t,stack')"
  apply(induction i d c s stack n z t stack' m arbitrary: v rule: pop_count_induct)
  apply (smt (z3) list_update_same_conv not_Cons_self2 prod.inject tSkip_tE)
          apply (smt (z3) not_Cons_self2 nth_list_update_eq prod.inject tAssign_tE)
  apply fastforce
        apply fastforce
       apply simp

end