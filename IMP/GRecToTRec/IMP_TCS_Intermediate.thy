theory IMP_TCS_Intermediate
  imports "General_Recursive_IMP/IMP_GRec" 
          "Tail_Recursive_IMP_Stack/IMP_Tailcall_Stacked"
          "Tail_Recursive_IMP_Stack/TsComsExtended"
begin

datatype
  tscom_tagged = tsSKIPTagged
      | tsAssignTagged  vname aexp
      | tsSeqTagged tscom_tagged tscom_tagged
      | tsIfTagged vname tscom_tagged tscom_tagged
      | tsCallTagged com vname
      | tsTailTagged "nat option"
      | tsPushTagged vname
      | tsPopTagged  vname

open_bundle tscom_tagged_syntax begin
notation tsSKIPTagged ("#SKIP") and
         tsAssignTagged ("# _ ::= _" [1000, 61] 61) and
         tsSeqTagged ("_ #;; _" [60, 61] 60) and
         tsIfTagged ("(#IF _/\<noteq>0 THEN _ ELSE _)" [0, 0, 61] 61) and
         tsCallTagged ("#CALL _ RETURN _") and
         tsTailTagged ("#_\<rightharpoonup> TAIL") and
         tsPushTagged ("#PUSH _") and
         tsPopTagged ("#POP _")
end

unbundle tscom_syntax and no com'_syntax and no rcom_syntax

instantiation tscom_tagged :: vars
begin

fun vars_tscom_tagged :: "tscom_tagged \<Rightarrow> vname list" where
"vars_tscom_tagged (# x ::= a)  = x # vars a" |
"vars_tscom_tagged (c\<^sub>1#;;c\<^sub>2) = vars_tscom_tagged c\<^sub>1 @ vars_tscom_tagged c\<^sub>2" |
"vars_tscom_tagged (#IF b\<noteq>0 THEN c1 ELSE c2) = b # vars_tscom_tagged c1 @ vars_tscom_tagged c2" |
"vars_tscom_tagged (#CALL c RETURN r) = r#vars c" |
"vars_tscom_tagged (#PUSH x)  = [x]" |
"vars_tscom_tagged (#POP x)  = [x]" |
"vars_tscom_tagged _ = []"

instance ..

end

fun tag_tscom :: "tscom \<Rightarrow> tscom_tagged" ("#\<lbrakk> _ \<rbrakk>") where
  "tag_tscom (ct1 ;; ct2) = tag_tscom ct1 #;; tag_tscom ct2" |
  "tag_tscom (IF b\<noteq>0 THEN ct1 ELSE ct2) = (#IF b\<noteq>0 THEN tag_tscom ct1 ELSE tag_tscom ct2)" |
  "tag_tscom tsTAIL = (#None\<rightharpoonup> TAIL)" |
  "tag_tscom (tsSKIP) = (#SKIP)" |
  "tag_tscom (x ::= a) = (#x ::= a)" |
  "tag_tscom (CALL v RETURN r) = (#CALL v RETURN r)" |
  "tag_tscom (PUSH v) = (#PUSH v)" |
  "tag_tscom (POP v) = (#POP v)" 

fun untag_tscom :: "tscom_tagged \<Rightarrow> tscom" ("#\<lbrakk> _ \<rbrakk>\<inverse>")where
  "untag_tscom (ct1 #;; ct2) = untag_tscom ct1 ;; untag_tscom ct2" |
  "untag_tscom (#IF b\<noteq>0 THEN ct1 ELSE ct2) = (IF b\<noteq>0 THEN untag_tscom ct1 ELSE untag_tscom ct2)" |
  "untag_tscom (#i\<rightharpoonup> TAIL) = tsTAIL" |
  "untag_tscom (#SKIP) = tsSKIP" |
  "untag_tscom (#x ::= a) = (x ::= a)" |
  "untag_tscom (#CALL v RETURN r) = (CALL v RETURN r)"|
  "untag_tscom (#PUSH v) = (PUSH v)" |
  "untag_tscom (#POP v) = (POP v)" 

lemma tscom_tag_correct : "untag_tscom (tag_tscom c) = c"
  by (induction c rule: tag_tscom.induct) fastforce+

fun no_rp :: "tscom_tagged \<Rightarrow> bool" where
  "no_rp (ct1 #;; ct2) \<longleftrightarrow> no_rp ct1 \<and> no_rp ct2" |
  "no_rp (#IF b\<noteq>0 THEN ct1 ELSE ct2) \<longleftrightarrow> no_rp ct1 \<and> no_rp ct2" |
  "no_rp (#None\<rightharpoonup> TAIL) \<longleftrightarrow> True" |
  "no_rp (#SKIP) \<longleftrightarrow> True" |
  "no_rp (# x ::= a) \<longleftrightarrow> True" |
  "no_rp (#CALL v RETURN r) \<longleftrightarrow> True"|
  "no_rp (#PUSH v) \<longleftrightarrow> True" |
  "no_rp (#POP v) \<longleftrightarrow> True" |
  "no_rp _ \<longleftrightarrow> False" 

fun stails_tagged :: "tscom_tagged \<Rightarrow> bool" where
  "stails_tagged #n\<rightharpoonup> TAIL \<longleftrightarrow> True" |
  "stails_tagged (c1#;;c2) \<longleftrightarrow> stails_tagged c1 \<or> stails_tagged c2" |
  "stails_tagged (#IF b\<noteq>0 THEN c1 ELSE c2) \<longleftrightarrow> stails_tagged c1 \<or> stails_tagged c2" |
  "stails_tagged _ \<longleftrightarrow> False"

fun sinvar_tagged :: "tscom_tagged \<Rightarrow> bool" where
  "sinvar_tagged (c\<^sub>1#;;c\<^sub>2) \<longleftrightarrow> \<not>sinvar_tagged c\<^sub>1 \<and> sinvar_tagged c\<^sub>2" |
  "sinvar_tagged (#IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> sinvar_tagged c\<^sub>1 \<and> sinvar_tagged c\<^sub>2" |
  "sinvar_tagged _ \<longleftrightarrow> True"

fun push_many_tagged :: "vname list \<Rightarrow> tscom_tagged" ("(#PUSH# _ )"  [61] 61) where
"push_many_tagged [] = #SKIP" |
"push_many_tagged (v#vs) = (#PUSH v) #;; push_many_tagged vs" 

fun pop_many_tagged :: "vname list \<Rightarrow> tscom_tagged" ("(#POP# _ )"  [61] 61) where
"pop_many_tagged [] = #SKIP" |
"pop_many_tagged (v#vs) = (#POP v)  #;; pop_many_tagged vs" 

inductive
  last_rec_index :: "tscom_tagged \<Rightarrow> tscom_tagged \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack \<times> nat option \<Rightarrow> bool" ("_ \<turnstile>Rec\<rightharpoonup>i _ \<Rightarrow>\<^bsup> _ \<^esup> _" 55)
  where
iSkip: "c \<turnstile>Rec\<rightharpoonup>i (#SKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,None)" |
iAssign: "c \<turnstile>Rec\<rightharpoonup>i (#x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,None)" |
iSeq: "\<lbrakk>c \<turnstile>Rec\<rightharpoonup>i (c1,s1,stack1) \<Rightarrow>\<^bsup>x\<^esup> (s2,stack2,n) ; c \<turnstile>Rec\<rightharpoonup>i (c2,s2,stack2) \<Rightarrow>\<^bsup>y\<^esup> (s3,stack3,r) ; z=x+y\<rbrakk> \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (c1 #;; c2, s1,stack1) \<Rightarrow>\<^bsup>z\<^esup> (s3,stack3,r)" |
iIfTrue: "\<lbrakk>s b \<noteq> 0; c \<turnstile>Rec\<rightharpoonup>i (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> s'; y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>y \<^esup> s'" |
iIfFalse: "\<lbrakk>s b = 0; c \<turnstile>Rec\<rightharpoonup>i (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> s'; y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>y \<^esup> s'" |
iCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,None)" |
iRec: "c \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> z \<^esup> (s',stack',i) \<Longrightarrow>  c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>TAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (s',stack',n)"|
iPush: "c \<turnstile>Rec\<rightharpoonup>i  (#PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x),None)"|
iPop: "stack x = Cons v vx \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := v), stack(x := vx),None)"
\<comment> \<open>New rule\<close>
bundle last_rec_index
begin
notation last_rec_index ("_ \<turnstile>Rec\<rightharpoonup>i _ \<Rightarrow> _" 55)
end

code_pred last_rec_index .

declare last_rec_index.intros[intro]

lemmas last_rec_index_induct = last_rec_index.induct[split_format(complete)]

inductive_cases iSkip_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#SKIP,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iAssign_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#x ::= a,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iSeq_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (c1#;;c2,s1) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iIf_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iCall_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#CALL C RETURN ret,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iRec_tE[elim]: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>TAIL,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iPush_tE[elim]: "c \<turnstile>Rec\<rightharpoonup>i (#PUSH x,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases iPop_tE[elim]: "c \<turnstile>Rec\<rightharpoonup>i (#POP x,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"


lemma lri_noninterference: 
  "\<lbrakk>c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (s',stack',r); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (s'(v:=y),stack',r)"
proof (induction c' c s stack x s' stack' r rule: last_rec_index_induct)
  case (iAssign c x a s stack )
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using last_rec_index.iAssign[of c x a "s(v:=y)" stack] by argo
next
  case (iCall C s z t c r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from iCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using last_rec_index.iCall[OF Call, of c r] state 
    by metis
next
  case (iRec c s ret z r n)
  then show ?case 
    by blast
next
  case (iPush c x s stack )
  have \<open>v \<noteq> x\<close> using \<open>set (vars #PUSH x) \<subseteq> S\<close> \<open>v \<notin> S\<close> by auto
  hence \<open>(s(v := y)) x = s x\<close> by simp
  then show ?case 
    by (metis last_rec_index.iPush)
next
  case (iPop stack x va vx c s )
  have \<open>v \<noteq> x\<close> using \<open>set (vars #POP x) \<subseteq> S\<close> \<open>v \<notin> S\<close> by auto
  hence \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by auto
  have \<open>c \<turnstile>Rec\<rightharpoonup>i (#POP x, s(v := y), stack) \<Rightarrow>\<^bsup>Suc 0\<^esup>  (s(v := y,x := va), stack(x := vx),None)\<close>
    using \<open>stack x = va # vx\<close> by blast
  then show ?case using \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by argo
qed auto

lemma lri_deterministic:
  "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',r) \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> t' \<^esup> (s'',stack'',r') \<Longrightarrow> t = t' \<and> s' = s'' \<and> stack' = stack'' \<and> r = r'"
proof (induction c' c s stack t s' stack' r arbitrary: t' s'' stack'' r' rule: last_rec_index_induct)
  case (iIfTrue s b c c1 stack x a a b y c2)
  then show ?case by fastforce
next
  case (iIfFalse s b c c2 stack x s' stack' r y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup> t' \<^esup> (s'',stack'', r')\<close> obtain x' where
     \<open>c \<turnstile>Rec\<rightharpoonup>i (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup> (s'',stack'',r')\<close> and \<open>t' = x' + 1\<close>
    by auto
  hence \<open> x' = x \<and> s' = s'' \<and> stack' = stack'' \<and> r = r'\<close>
    using iIfFalse.IH by simp
  then show ?case 
    by (simp add: \<open>t' = x' + 1\<close> iIfFalse.hyps(3))
next
  case (iCall C s z t c r ret)
  then show ?case 
    using bigstep_det by blast
next
  case (iPop stack x v vx c s)
  then show ?case by auto
qed blast+

lemma lri_sound: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',r) \<Longrightarrow> #\<lbrakk> c' \<rbrakk>\<inverse> \<turnstile> (#\<lbrakk> c \<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack')"
proof (induction c' c s stack t s' stack' r rule: last_rec_index_induct)
  case (iAssign c x a s stack)
  then show ?case  
    using tAssign untag_tscom.simps(5) by presburger
next
  case (iCall C s z t c r stack)
  then show ?case 
    using tCall untag_tscom.simps(6) by presburger
next
  case (iPush c x s stack)
  then show ?case 
    using tsPush untag_tscom.simps(7) by presburger
next
  case (iPop stack x v vx c s)
  then show ?case 
    using tsPop untag_tscom.simps(8) by presburger
qed auto

lemma lri_complete: "c' \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack') \<Longrightarrow> #\<lbrakk>c'\<rbrakk> \<turnstile>Rec\<rightharpoonup>i (#\<lbrakk>c\<rbrakk>,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',None)"
proof (induction c' c s stack t s' stack' rule: tsbig_step_t_induct)
  case (tAssign c x a s stack)
  then show ?case 
    using iAssign tag_tscom.simps(5) by presburger
next
  case (tCall C s z t c r stack)
  then show ?case 
    using iCall tag_tscom.simps(6) by presburger
next
  case (tsPush c x s stack)
  then show ?case 
    using iPush tag_tscom.simps(7) by presburger
next
  case (tsPop stack x v vx c s)
  then show ?case 
    using iPop tag_tscom.simps(8) by presburger
qed auto

lemma lri_correct: "c' \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack') \<equiv> #\<lbrakk>c'\<rbrakk> \<turnstile>Rec\<rightharpoonup>i (#\<lbrakk>c\<rbrakk>,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',None)"
  by (smt (verit, del_insts) lri_complete lri_sound tscom_tag_correct)

fun isem_equiv :: "tscom_tagged \<Rightarrow> tscom_tagged \<Rightarrow> bool" ("_ \<equiv>\<^sub>\<turnstile>\<^sub>i _") where
  "(ct1 #;; ct2) \<equiv>\<^sub>\<turnstile>\<^sub>i (ct1' #;; ct2') \<longleftrightarrow> ((ct1 \<equiv>\<^sub>\<turnstile>\<^sub>i ct1') \<and> (ct2 \<equiv>\<^sub>\<turnstile>\<^sub>i ct2'))" |
  "((#IF b\<noteq>0 THEN ct1 ELSE ct2) \<equiv>\<^sub>\<turnstile>\<^sub>i (#IF b'\<noteq>0 THEN ct1' ELSE ct2')) \<longleftrightarrow> ((ct1 \<equiv>\<^sub>\<turnstile>\<^sub>i ct1') \<and> (ct2 \<equiv>\<^sub>\<turnstile>\<^sub>i ct2') \<and> b = b')" |
  "(#i\<rightharpoonup> TAIL) \<equiv>\<^sub>\<turnstile>\<^sub>i (#j\<rightharpoonup> TAIL) = True" |
  "c \<equiv>\<^sub>\<turnstile>\<^sub>i c' \<longleftrightarrow> c = c'" 

lemma isem_equiv_sound:
  "d \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',i) \<Longrightarrow>
   c \<equiv>\<^sub>\<turnstile>\<^sub>i c' \<Longrightarrow> 
  \<exists>j. d \<turnstile>Rec\<rightharpoonup>i (c',s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',j)"
  by (induction c c' arbitrary: d s stack t s' stack' i rule: isem_equiv.induct) fastforce+

declare isem_equiv.elims[elim]

lemma isem_equiv_refl: "c \<equiv>\<^sub>\<turnstile>\<^sub>i c"
  by (induction c) fastforce+

lemma isem_equiv_sym: "c \<equiv>\<^sub>\<turnstile>\<^sub>i c' \<longleftrightarrow> c' \<equiv>\<^sub>\<turnstile>\<^sub>i c"
  by (induction c c' rule: isem_equiv.induct) fastforce+

lemma isem_equiv_assoc: "\<lbrakk>c \<equiv>\<^sub>\<turnstile>\<^sub>i c';c' \<equiv>\<^sub>\<turnstile>\<^sub>i c''\<rbrakk> \<Longrightarrow> c \<equiv>\<^sub>\<turnstile>\<^sub>i c''"
  by (induction c c' arbitrary: c'' rule: isem_equiv.induct) auto

lemma isem_equiv_correct:
  "c \<equiv>\<^sub>\<turnstile>\<^sub>i c' \<Longrightarrow> 
  \<exists>i. d \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',i) \<equiv> \<exists>j. d \<turnstile>Rec\<rightharpoonup>i (c',s,stack) \<Rightarrow>\<^bsup>t \<^esup> (s',stack',j)"
  using isem_equiv_sym isem_equiv_sound by (smt (verit, best))

end