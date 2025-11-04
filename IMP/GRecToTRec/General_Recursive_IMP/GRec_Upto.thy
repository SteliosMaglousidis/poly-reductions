theory GRec_Upto
  imports IMP_GRec
begin

text \<open>Returns the state right before the first recursive call and if there is a recursive call to be executed\<close>
inductive
  upto_rec :: "(rcom \<times> state \<times> vname) \<Rightarrow> nat \<Rightarrow> (state \<times> bool) \<Rightarrow> bool" ("\<turnstile>UPTO\<lparr> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "\<turnstile>UPTO\<lparr> (rSKIP,s,ret) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,False)" |
Assign: "\<turnstile>UPTO\<lparr> (x ::= a,s,ret) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),False)" |
Seq1: "\<lbrakk>\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup>x \<^esup> (s2,True)\<rbrakk> \<Longrightarrow> \<turnstile>UPTO\<lparr> (c1;;c2,s1,ret) \<Rightarrow>\<^bsup>x\<^esup> (s2,True)" |
Seq2: "\<lbrakk>\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup>x \<^esup> (s2,False); \<turnstile>UPTO\<lparr> (c2,s2,ret) \<Rightarrow>\<^bsup>y \<^esup> (s3,CONT); z=x+y\<rbrakk> \<Longrightarrow> \<turnstile>UPTO\<lparr> (c1;;c2,s1,ret) \<Rightarrow>\<^bsup>z\<^esup> (s3,CONT)" |
IfTrue: "\<lbrakk> s b \<noteq> 0; \<turnstile>UPTO\<lparr> (c1,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1 \<rbrakk> \<Longrightarrow> \<turnstile>UPTO\<lparr> (IF b \<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
IfFalse: "\<lbrakk> s b = 0; \<turnstile>UPTO\<lparr> (c2,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1  \<rbrakk> \<Longrightarrow> \<turnstile>UPTO\<lparr> (IF b \<noteq>0 THEN c1 ELSE c2, s,ret) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> \<turnstile>UPTO\<lparr> (CALL C RETURN r,s,ret) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),False)" |
Rec: "\<turnstile>UPTO\<lparr> (RECURSE,s,ret) \<Rightarrow>\<^bsup>5 \<^esup> (s,True)"

code_pred upto_rec .

declare upto_rec.intros[intro]

lemmas upto_rec_induct = upto_rec.induct[split_format(complete)]

inductive_cases uptoSkip_tE[elim!]: "\<turnstile>UPTO\<lparr> (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"
inductive_cases uptoAssign_tE[elim!]: "\<turnstile>UPTO\<lparr> (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases uptoSeq_tE[elim!]: "\<turnstile>UPTO\<lparr> (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases uptoIf_tE[elim!]: "\<turnstile>UPTO\<lparr> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT)"
inductive_cases uptoCall_tE[elim!]: "\<turnstile>UPTO\<lparr> (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> (t,ret)"
inductive_cases uptoRec_tE[elim]: "\<turnstile>UPTO\<lparr> (RECURSE,s) \<Rightarrow>\<^bsup>x \<^esup> (t,ret)"

lemma upto_rec_noninterference:
  "\<lbrakk>\<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); set (vars c) \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> \<turnstile>UPTO\<lparr> (c,s(v:=y),ret) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),CONT)"
proof (induction c s ret x t CONT rule: upto_rec_induct)
  case (Skip s ret)
  then show ?case 
    by blast
next
  case (Assign x a s ret)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using upto_rec.Assign[of  x a "s(v:=y)" ret] by argo
next
  case (Call C s z t r ret)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from rCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using upto_rec.Call[OF Call, of  r] state by metis
next
  case (Rec s ret1)
  then show ?case by blast
qed auto

lemma upto_rec_deterministic:
  "\<turnstile>UPTO\<lparr>  (c,s,ret) \<Rightarrow>\<^bsup> z \<^esup> (t,b) \<Longrightarrow> \<turnstile>UPTO\<lparr>  (c,s,ret) \<Rightarrow>\<^bsup> z' \<^esup> (t',b') \<Longrightarrow> z = z' \<and> t = t' \<and> b = b'"
proof (induction c s ret z t b arbitrary: t' z' b' rule: upto_rec_induct)
  case (IfTrue s b c1 ret x t CONT y c2)
  then show ?case
    by fastforce
next
  case (IfFalse s b c2 ret x t CONT y c1)
  from \<open>s b = 0\<close> \<open>\<turnstile>UPTO\<lparr> (rIf b c1 c2, s, ret) \<Rightarrow>\<^bsup>z'\<^esup>  (t',b')\<close> obtain x' where
     \<open>\<turnstile>UPTO\<lparr> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (t',b')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t' \<and> CONT = b'\<close>
    using IfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> IfFalse.hyps(3))
next
  case (Call C s z t r ret)
  then show ?case using bigstep_det by blast
qed blast+

lemma upto_no_rec: "\<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (r,b) \<Longrightarrow> \<not>b \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> x \<^esup> r"
  by (induction c s ret x r b rule: upto_rec_induct) auto

lemma upto_false_no_rec: "\<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> (t,b) \<Longrightarrow> \<not>has_rec c \<Longrightarrow> \<not>b"
  by (induction c s ret z t b rule: upto_rec_induct) auto

lemma upto_no_rec_complete': "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> x \<^esup> s' \<Longrightarrow> \<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> y \<^esup> (t,False)\<Longrightarrow> s' = t \<and> x = y"
  apply (induction c' c s ret x s' arbitrary: y t rule: rbig_step_t_induct) 
  apply auto
  using bigstep_det by blast+

lemma upto_no_rec_sound: "\<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',b) \<Longrightarrow> \<not>has_rec c \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  by (meson upto_false_no_rec upto_no_rec)

lemma upto_no_rec_complete: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<not>has_rec c \<Longrightarrow> \<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',False)"
  by (induction c' c s ret t s' rule: rbig_step_t_induct) auto

lemma upto_no_rec_correct:
  assumes \<open> \<not>has_rec c\<close>
  shows "\<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',False) \<equiv> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  by (smt (verit, del_insts) assms upto_no_rec upto_no_rec_complete)

lemma upto_has_rec: "\<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (r,b) \<Longrightarrow> b \<Longrightarrow> has_rec c"
  using upto_false_no_rec by blast

lemma upto_rec_Ex: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<exists>s'' b t'. \<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> t' \<^esup> (s'',b)"
proof (induction c' c s ret t s' rule: rbig_step_t_induct)
  case (rSeq c c1 s1 ret x s2 c2 y s3 z)
  obtain t1 s1' b1 where \<open>\<turnstile>UPTO\<lparr> (c1, s1, ret) \<Rightarrow>\<^bsup>t1\<^esup>  (s1', b1)\<close>
    using rSeq.IH(1) by auto
  then show ?case proof (cases b1)
    case True
    then show ?thesis 
      using \<open>\<turnstile>UPTO\<lparr> (c1, s1, ret) \<Rightarrow>\<^bsup>t1\<^esup> (s1', b1)\<close> by force
  next
    case False
    have \<open>c \<turnstile>\<^sub>R (c1, s1, ret) \<Rightarrow>\<^bsup>t1\<^esup>  s1'\<close> 
      using False \<open>\<turnstile>UPTO\<lparr> (c1, s1, ret) \<Rightarrow>\<^bsup>t1\<^esup> (s1', b1)\<close> upto_no_rec by auto
    hence \<open>t1 = x \<and> s1' = s2\<close>
      using rSeq.hyps(1) rdeterministic by auto
    then show ?thesis 
      using False \<open>\<turnstile>UPTO\<lparr> (c1, s1, ret) \<Rightarrow>\<^bsup>t1\<^esup> (s1', b1)\<close> rSeq.IH(2) by fastforce
  qed
next
  case (rCall C s z t c r ret)
  then show ?case by blast
qed auto


(*
text \<open>Closure of tails\<close>
inductive
 rec_steps :: "rcom \<Rightarrow> rcom \<times> state \<times> vname  \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile>\<^sub>R''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55) for d
where
rFalse: "\<turnstile>\<^sub>R(c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> (t,False) \<Longrightarrow> d \<turnstile>\<^sub>R' (c,s,ret)\<Rightarrow>\<^bsup> z \<^esup> t" |
rTrue: "\<turnstile>\<^sub>R(c,s1,ret) \<Rightarrow>\<^bsup>x \<^esup> (s2,True) \<Longrightarrow> d \<turnstile>\<^sub>R' (d,s2,ret)\<Rightarrow>\<^bsup> y \<^esup> s3 \<Longrightarrow> d \<turnstile>\<^sub>R'(c,s1,ret1)\<Rightarrow>\<^bsup>x+y \<^esup> s3"

code_pred rec_steps .

declare rec_steps.intros[intro]
declare rec_steps.cases[elim]

lemmas rec_steps_induct = rec_steps.induct[split_format(complete)]
*)

(* Executing everything up to the first recursive call and returning the rest to be executed*)
inductive
  upto_with_rec :: "rcom \<Rightarrow> rcom \<times> state \<times> vname \<Rightarrow> nat \<Rightarrow> state \<times> rcom option \<Rightarrow> bool" ("_ \<turnstile>UPTO\<lbrakk> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
upto_withSkip: "c \<turnstile>UPTO\<lbrakk> (rSKIP,s,ret) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,None)" |
upto_withAssign: "c \<turnstile>UPTO\<lbrakk> (x ::= a,s,ret) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),None)" |
upto_withSeqGRec: "\<lbrakk>\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> t1 \<^esup> (s2',True) ; c \<turnstile>UPTO\<lbrakk> (c1,s1,ret) \<Rightarrow>\<^bsup>t\<^esup> (s2,Some rc) ; rc' = Some (rc;;c2)\<rbrakk> 
                    \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2,s1,ret) \<Rightarrow>\<^bsup>t\<^esup> (s2, rc')" |
upto_withSeqTRec: "\<lbrakk>\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> t1 \<^esup> (s2',True) ; c \<turnstile>UPTO\<lbrakk> (c1,s1,ret) \<Rightarrow>\<^bsup>t\<^esup> (s2,None)\<rbrakk> 
                    \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2,s1,ret) \<Rightarrow>\<^bsup>t\<^esup> (s2, Some c2)" |
upto_withSeqNoRec: "\<lbrakk>\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> x \<^esup> (s2,False) ; c \<turnstile>UPTO\<lbrakk> (c2,s2,ret) \<Rightarrow>\<^bsup>y\<^esup> s3 ; z=x+y\<rbrakk> \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z\<^esup> s3" |
upto_withIfTrue: "\<lbrakk>s b \<noteq> 0; c \<turnstile>UPTO\<lbrakk> (c1,s,ret) \<Rightarrow>\<^bsup>x \<^esup> s'; y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (IF b \<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>y \<^esup> s'" |
upto_withIfFalse: "\<lbrakk>s b = 0; c \<turnstile>UPTO\<lbrakk> (c2,s,ret) \<Rightarrow>\<^bsup>x \<^esup> s'; y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (IF b \<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>y \<^esup> s'" |
upto_withCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (CALL C RETURN r,s,ret) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),None)" |
upto_withRec: "c \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> z \<^esup> r \<Longrightarrow>  c \<turnstile>UPTO\<lbrakk> (RECURSE ,s,ret) \<Rightarrow>\<^bsup>5 + z \<^esup> (s(ret:=r ret),None)"
bundle upto_with_rec
begin
notation upto_with_rec ("_ \<turnstile>UPTO\<lbrakk> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

code_pred upto_with_rec .

declare upto_with_rec.intros[intro]

lemmas upto_with_rec_induct = upto_with_rec.induct[split_format(complete)]

inductive_cases upto_withSkip_tE[elim!]: "c \<turnstile>UPTO\<lbrakk> (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases upto_withAssign_tE[elim!]: "c \<turnstile>UPTO\<lbrakk> (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases upto_withSeq_tE[elim!]: "c \<turnstile>UPTO\<lbrakk> (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases upto_withIf_tE[elim!]: "c \<turnstile>UPTO\<lbrakk> (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases upto_withCall_tE[elim!]: "c \<turnstile>UPTO\<lbrakk> (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases upto_withRec_tE[elim]: "c \<turnstile>UPTO\<lbrakk> (RECURSE ,s) \<Rightarrow>\<^bsup>z \<^esup> t"

lemma upto_with_Seq_None_E: "c \<turnstile>UPTO\<lbrakk> (c1,s1,ret) \<Rightarrow>\<^bsup>t1\<^esup> (s2,r) \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2,s1,ret) \<Rightarrow>\<^bsup>t\<^esup> (s3, None) \<Longrightarrow> r = None"
  apply (induction c c1 s1 ret t1 s2 r arbitrary: c2 t s3 rule: upto_with_rec_induct) apply auto
  using upto_rec_deterministic by blast+

lemma upto_with_Seq_Some_E: "\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> t1 \<^esup> (s2,b) \<Longrightarrow> b \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2,s1,ret) \<Rightarrow>\<^bsup>t\<^esup> (s3, r) \<Longrightarrow>\<exists>rc. r = Some rc"
  apply (induction c1 s1 ret t1 s2 b arbitrary: c2 t s3 r rule: upto_rec_induct) apply auto
  using upto_rec_deterministic by blast+

lemma upto_rec_no_with: " \<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',b) \<Longrightarrow> \<not>b \<Longrightarrow> c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',None)"
  apply(induction c s ret t s' b arbitrary: c' rule: upto_rec_induct)
         apply auto
  by fastforce+

lemma uptoSeqGRec_tE'[elim!]: "\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> x \<^esup> (s2,b) \<Longrightarrow> b \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z\<^esup> (s3,Some (rc;;c2)) 
                                \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1,s1,ret) \<Rightarrow>\<^bsup>z\<^esup> (s3,Some rc)"
  apply(induction c1 s1 ret x s2 b arbitrary: c2 c z s3 rule: upto_rec_induct)
         apply auto
  by (metis upto_rec_deterministic)+

lemma uptoSeqTRec_tE'[elim!]: "\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> x \<^esup> (s2,b) \<Longrightarrow> b \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z\<^esup> (s3,Some c2) 
                                \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1,s1,ret) \<Rightarrow>\<^bsup>z\<^esup> (s3,None)"
  apply(induction c1 s1 ret x s2 b arbitrary: c2 c z s3 rule: upto_rec_induct)
         apply auto
  by (metis upto_rec_deterministic)+

lemma uptoSeqRec_Rest_Cases_tE'[elim!]: "\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> x \<^esup> (s2,b) \<Longrightarrow> b \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z\<^esup> (s3,Some r) 
                                \<Longrightarrow> r = c2 \<or> (\<exists>rc. r = rc ;; c2)"
  apply(induction c1 s1 ret x s2 b arbitrary: c2 c z s3 rule: upto_rec_induct)
         apply auto
  by (metis upto_rec_deterministic)+

lemma upto_with_SeqNoRec_E'[elim!]: "\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> x \<^esup> (s2,b) \<Longrightarrow> \<not>b \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z\<^esup> s3  
                                  \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c2,s2,ret) \<Rightarrow>\<^bsup>z - x\<^esup> s3"
  apply(induction c1 s1 ret x s2 b arbitrary: c2 c z s3 rule: upto_rec_induct)
         apply auto
  apply blast  apply blast
  apply (metis upto_rec_deterministic)
  apply (metis upto_rec_deterministic)
  apply (metis upto_rec_deterministic)
  apply (metis upto_rec_deterministic)
  apply (metis upto_rec_deterministic)
          apply (metis upto_rec_deterministic)
  apply (metis add_diff_cancel_left' upto_rec_deterministic)  
  apply (metis  upto_rec_deterministic)
  apply (metis  upto_rec_deterministic)
  apply (metis add_diff_cancel_left' upto_rec_deterministic)
  apply (metis  upto_rec_deterministic)
  apply (metis  upto_rec_deterministic)
   apply (metis add_diff_cancel_left' upto_rec_deterministic)
  by (metis big_step_t_determ2 diff_add_inverse)          

lemma upto_with_SeqNoRec_progress: "\<turnstile>UPTO\<lparr> (c1,s1,ret) \<Rightarrow>\<^bsup> x \<^esup> (s2,b) \<Longrightarrow> \<not>b \<Longrightarrow> c \<turnstile>UPTO\<lbrakk> (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z\<^esup> s3  
                                  \<Longrightarrow> x \<le> z"
  using le_add1 upto_rec_deterministic by blast

lemma upto_with_rec_noninterference:
  "\<lbrakk>c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (t,r); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c' \<turnstile>UPTO\<lbrakk> (c,s(v:=y),ret) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),r)"
proof (induction c s ret x t r rule: upto_with_rec_induct)
  case (upto_withSkip s ret)
  then show ?case 
    by blast
next
  case (upto_withAssign c x a s ret)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using upto_with_rec.upto_withAssign[of c x a "s(v:=y)" ret] by argo
next
  case (upto_withSeqGRec c1 s1 ret t1 s2' c t s2 rc rc' c2)
  hence \<open>\<turnstile>UPTO\<lparr> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>t1\<^esup>  (s2'(v := y), True)\<close> using upto_rec_noninterference by auto
  then show ?case
    using \<open>\<turnstile>UPTO\<lparr> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>t1\<^esup> (s2'(v := y), True)\<close> upto_withSeqGRec.hyps(3)
    by (smt (verit, ccfv_threshold) Un_iff fun_upd_same fun_upd_triv fun_upd_twist fun_upd_upd set_append subset_eq upto_withSeqGRec.IH upto_withSeqGRec.prems(1,2,3)
        upto_with_rec.upto_withSeqGRec vars_rcom.simps(2))
next
  case (upto_withSeqTRec c1 s1 ret t1 s2' c t s2 c2)
  hence \<open>\<turnstile>UPTO\<lparr> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>t1\<^esup>  (s2'(v := y), True)\<close> using upto_rec_noninterference by auto
  have \<open>c \<turnstile>UPTO\<lbrakk> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>t\<^esup>  (s2(v := y), None)\<close> 
    by (metis Un_iff set_append subset_code(1) upto_withSeqTRec.IH upto_withSeqTRec.prems(1,2,3) vars_rcom.simps(2))
  then show ?case 
    using \<open>\<turnstile>UPTO\<lparr> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>t1\<^esup> (s2'(v := y), True)\<close>  
          \<open>c \<turnstile>UPTO\<lbrakk> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>t\<^esup>  (s2(v := y), None)\<close>  upto_withSeqTRec.hyps(2) 
    by (smt (verit, ccfv_threshold) fun_upd_other fun_upd_same fun_upd_twist fun_upd_upd upto_with_rec.upto_withSeqTRec)
next
  case (upto_withSeqNoRec c1 s1 ret x s2 c c2 yt s3 z)
  hence \<open>\<turnstile>UPTO\<lparr> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>x\<^esup>  (s2(v := y), False)\<close> using upto_rec_noninterference by auto
  have \<open>set (vars c2) \<subseteq> S\<close> 
    using upto_withSeqNoRec.prems(1) by auto
  then show ?case 
    using \<open>\<turnstile>UPTO\<lparr> (c1, s1(v := y), ret) \<Rightarrow>\<^bsup>x\<^esup> (s2(v := y), False)\<close> upto_withSeqNoRec.IH upto_withSeqNoRec.hyps(3)
      upto_withSeqNoRec.prems(2,3) by blast
next
  case (upto_withCall C s z t c r ret)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from upto_withCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using upto_rec.Call[OF Call, of  r] state 
    by (metis local.Call upto_with_rec.upto_withCall)
next
  case (upto_withRec c s ret z r)
  hence \<open>c \<turnstile>\<^sub>R (RECURSE, s(v := y), ret) \<Rightarrow>\<^bsup>5 + z\<^esup>  s(ret := r ret, v := y)\<close> 
    by (simp add: rRec rnoninterference)
  then show ?case 
    by (metis rRec_tE upto_with_rec.upto_withRec)
qed auto

lemma upto_with_rec_deterministic:
  "c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> z \<^esup> (s',r) \<Longrightarrow> c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> z' \<^esup> (s'',r') \<Longrightarrow> z = z' \<and> s' = s'' \<and> r = r'"
proof (induction c' c s ret z s' r arbitrary: s'' z' r' rule: upto_with_rec_induct)
   case (upto_withSeqGRec c1 s1 ret t1 s2' c t s2 rc rc' c2)
  then show ?case proof(cases r')
    case None
    then show ?thesis 
      by (metis option.distinct(1) upto_with_Seq_None_E upto_withSeqGRec.hyps(2) upto_withSeqGRec.prems)
  next
    case (Some a)
    have \<open>a = c2 \<or> (\<exists>rc' . a = rc';;c2)\<close> 
      using Some uptoSeqRec_Rest_Cases_tE' upto_withSeqGRec.hyps(1) upto_withSeqGRec.prems by auto
    hence \<open>\<exists>rc' . a = rc';;c2\<close> 
      by (metis Some option.discI uptoSeqTRec_tE' upto_withSeqGRec.IH upto_withSeqGRec.hyps(1)
          upto_withSeqGRec.prems)
    obtain rc'' where \<open> a = rc'';;c2\<close> 
      using \<open>\<exists>rc'. a = rc';; c2\<close> by auto
    have \<open>c \<turnstile>UPTO\<lbrakk> (c1, s1, ret) \<Rightarrow>\<^bsup>z'\<^esup>  (s'', Some rc'')\<close>
      using Some \<open>a = rc'';; c2\<close> uptoSeqGRec_tE' upto_withSeqGRec.hyps(1) upto_withSeqGRec.prems by presburger
    then show ?thesis 
      using Some \<open>a = rc'';; c2\<close> upto_withSeqGRec.IH upto_withSeqGRec.hyps(3) by auto
  qed
next
  case (upto_withSeqTRec c1 s1 ret t1 s2' c t s2 c2)
  obtain rc' where "r' = Some rc'" 
    using upto_with_Seq_Some_E upto_withSeqTRec.hyps(1) upto_withSeqTRec.prems by presburger
  hence \<open>rc' = c2 \<or> (\<exists>rc'' . rc' = rc'';;c2)\<close> 
    using uptoSeqRec_Rest_Cases_tE' upto_withSeqTRec.hyps(1) upto_withSeqTRec.prems by auto
  hence \<open>rc' = c2\<close> 
    by (metis \<open>r' = Some rc'\<close> not_Some_eq uptoSeqGRec_tE' upto_withSeqTRec.IH upto_withSeqTRec.hyps(1)
        upto_withSeqTRec.prems)
  then show ?case 
    by (metis \<open>r' = Some rc'\<close> uptoSeqTRec_tE' upto_withSeqTRec.IH upto_withSeqTRec.hyps(1)
        upto_withSeqTRec.prems)
next
  case (upto_withSeqNoRec c1 s1 ret x s2 c c2 y a b z)
  have \<open>c \<turnstile>UPTO\<lbrakk> (c2, s2, ret) \<Rightarrow>\<^bsup>z' - x\<^esup>  (s'', r')\<close> 
    by (metis upto_with_SeqNoRec_E' upto_withSeqNoRec.hyps(1) upto_withSeqNoRec.prems) 
  hence \<open>y = z' - x \<and> a = s'' \<and> b = r'\<close> 
    by (simp add: upto_withSeqNoRec.IH)
  hence \<open>y = z' - x\<close> by blast
  hence \<open>z' = y + x\<close> using upto_with_SeqNoRec_progress[of c1 s1 ret x s2 "False" c c2 z' "(s'',r')"]
    \<open>\<turnstile>UPTO\<lparr> (c1, s1, ret) \<Rightarrow>\<^bsup>x\<^esup>  (s2, False)\<close> \<open>c \<turnstile>UPTO\<lbrakk> (c1;; c2, s1, ret) \<Rightarrow>\<^bsup>z'\<^esup>  (s'', r')\<close> by simp
  then show ?case 
    by (simp add: \<open>y = z' - x \<and> a = s'' \<and> b = r'\<close> upto_withSeqNoRec.hyps(3))
next
  case (upto_withIfTrue s b c1 ret x t CONT y c2)
  then show ?case by fastforce
next
  case (upto_withIfFalse s b c c2 ret x t2 r2 y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>UPTO\<lbrakk> (rIf b c1 c2, s, ret) \<Rightarrow>\<^bsup>z'\<^esup>  (s'', r')\<close> obtain x' where
     \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', r')\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t2 = s'' \<and> r2 = r'\<close>
    using upto_withIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> upto_withIfFalse.hyps(3))
next
  case (upto_withCall C s z t c r ret)
  then show ?case using bigstep_det by blast
next
  case (upto_withRec c s ret z r)
  then show ?case 
    using rdeterministic by fastforce
qed blast+

lemma upto_with_no_rec: "c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',r) \<Longrightarrow> \<not>has_rec c \<Longrightarrow> \<turnstile>UPTO\<lparr> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',False)"
  apply (induction c' c s ret t s' r rule: upto_with_rec_induct) apply auto
  using upto_false_no_rec by blast+

lemma upto_with_rec_state: "\<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t\<^esup>  (s', b) \<Longrightarrow> b = True \<Longrightarrow> c' \<turnstile>\<^sub>R (c', s', ret) \<Rightarrow>\<^bsup>rect\<^esup>  r \<Longrightarrow> t' = t + rect 
                        \<Longrightarrow>  c' \<turnstile>UPTO\<lbrakk> (c, s, ret) \<Rightarrow>\<^bsup>t'\<^esup>  (s'', rest) \<Longrightarrow> s'' = s'(ret := r ret)"
  apply (induction c s ret t s' b arbitrary: c' rect r t' s'' rest rule: upto_rec_induct)
         apply auto
      apply (metis upto_rec_deterministic)
     apply (metis upto_rec_deterministic)
    apply (metis upto_rec_deterministic)  
  using upto_rec_deterministic apply fastforce
  using rdeterministic by fastforce

lemma upto_with_sound: "c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',r) \<Longrightarrow> invar c \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  apply (induction c' c s ret t s' r rule: upto_with_rec_induct) apply auto 
  using upto_false_no_rec apply blast
  using upto_has_rec apply force
  using rSeq upto_no_rec_correct by presburger

lemma upto_with_complete: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> invar c \<Longrightarrow> c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',None)"
  apply (induction c' c s ret t s' rule: rbig_step_t_induct) apply auto 
  using upto_with_no_rec by fastforce+

lemma upto_with_trec_sound: "c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',r) \<Longrightarrow> r = None \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  apply (induction c' c s ret t s' r rule: upto_with_rec_induct) apply auto 
  by (metis rSeq upto_no_rec)

text \<open>Executing a tail-recursive program upto and including a recursive call is equivalent to executing the whole program\<close>
theorem upto_with_correct: 
  assumes "invar c"
  shows "c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> (s',None) \<equiv> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  using assms upto_with_sound upto_with_complete by (smt (verit))

lemma upto_with_trec_Ex: "\<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t\<^esup>  (s', b) \<Longrightarrow> b = True \<Longrightarrow> c' \<turnstile>UPTO\<lbrakk> (c, s, ret) \<Rightarrow>\<^bsup>t'\<^esup>  (s'', r)
                      \<Longrightarrow> t'' = t' - t \<Longrightarrow> \<exists>sr . c' \<turnstile>\<^sub>R (c',s',ret) \<Rightarrow>\<^bsup> t'' \<^esup> sr"
  apply (induction c s ret t s' b arbitrary: c' t' s'' r  t'' rule: upto_rec_induct)
         apply auto
     apply (metis upto_rec_deterministic)
     apply (metis upto_rec_deterministic)
    apply (metis upto_rec_deterministic) 
  by fastforce+

lemma upto_with_trec_state: "\<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t\<^esup>  (s', b) \<Longrightarrow> b = True \<Longrightarrow> c' \<turnstile>UPTO\<lbrakk> (c, s, ret) \<Rightarrow>\<^bsup>t'\<^esup>  (s'', r)
                      \<Longrightarrow> t'' = t' - t \<Longrightarrow> c' \<turnstile>\<^sub>R (c',s',ret) \<Rightarrow>\<^bsup> t'' \<^esup> sr \<Longrightarrow> s'' = s'(ret:=sr ret)"
  apply (induction c s ret t s' b arbitrary: sr c' t' s'' r  t'' rule: upto_rec_induct)
         apply auto
  apply (metis upto_rec_deterministic)
  apply (metis upto_rec_deterministic)
    apply (metis upto_rec_deterministic)
   apply fastforce
  by (meson upto_withRec upto_with_rec_deterministic)

lemma upto_with_rec_after: "\<lbrakk> c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> x \<^esup> (s', r) ; r = Some rc ; c' \<turnstile>\<^sub>R (rc,s',ret) \<Rightarrow>\<^bsup> y \<^esup> s'' ; z = x + y\<rbrakk> 
                             \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> z \<^esup> s''"
proof (induction c' c s ret x s' r arbitrary: y s'' z rc rule: upto_with_rec_induct)
  case (upto_withSeqTRec c1 s1 ret t1 s2' c t s2 c2)
  from upto_with_trec_sound[OF \<open>c \<turnstile>UPTO\<lbrakk> (c1, s1, ret) \<Rightarrow>\<^bsup>t\<^esup>  (s2, None)\<close>] have
        \<open>c \<turnstile>\<^sub>R (c1, s1, ret) \<Rightarrow>\<^bsup>t\<^esup>  s2\<close>  by blast
  from \<open>Some c2 = Some rc\<close> \<open>c \<turnstile>\<^sub>R (rc, s2, ret) \<Rightarrow>\<^bsup>y\<^esup>  s''\<close> have \<open>c \<turnstile>\<^sub>R (c2, s2, ret) \<Rightarrow>\<^bsup>y\<^esup>  s''\<close>
    by auto
  then show ?case 
    using \<open>c \<turnstile>\<^sub>R (c1, s1, ret) \<Rightarrow>\<^bsup>t\<^esup> s2\<close> upto_withSeqTRec.prems(3) by blast
next
  case (upto_withSeqNoRec c1 s1 ret x s2 c c2 y a b z)
  then show ?case 
    using upto_no_rec by fastforce
qed fastforce+

lemma upto_with_rec_vars: " c' \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup> x \<^esup> (s', r) \<Longrightarrow> r = Some rc \<Longrightarrow> set (vars rc) \<subseteq> set (vars c)"
  by (induction c' c s ret x s' r arbitrary: rc rule: upto_with_rec_induct) auto


text \<open>Step-wise execution of a program in tail-recursive steps\<close>
inductive
  tail_rec_steps :: "rcom \<Rightarrow> rcom \<times> state \<times> vname \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile>\<^sub>R''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55) for d
where
trsFalse: "d \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup>t\<^esup> (s',None) \<Longrightarrow> d \<turnstile>\<^sub>R'(c,s,ret)\<Rightarrow>\<^bsup>t\<^esup> s'" |
trsTrue: "d \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup>x\<^esup> (s',Some r) \<Longrightarrow> d \<turnstile>\<^sub>R'(r,s',ret)\<Rightarrow>\<^bsup>y\<^esup> s'' \<Longrightarrow> d \<turnstile>\<^sub>R'(c,s,ret)\<Rightarrow>\<^bsup>x + y\<^esup> s''"

code_pred tail_rec_steps .

declare tail_rec_steps.intros[intro]
declare tail_rec_steps.cases[elim]

lemmas tail_rec_steps_induct = tail_rec_steps.induct[split_format(complete)]

lemma tail_rec_step_E[elim]: "d \<turnstile>\<^sub>R'(c,s,ret)\<Rightarrow>\<^bsup>t\<^esup> s'' \<Longrightarrow> d \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup>x\<^esup> (s',Some r) \<Longrightarrow> d \<turnstile>\<^sub>R'(r,s',ret)\<Rightarrow>\<^bsup>t - x\<^esup> s''"
  apply (induction c s ret t s'' arbitrary: x s' r rule: tail_rec_steps_induct)
   apply (meson option.discI upto_with_rec_deterministic)
  by (metis diff_add_inverse option.inject upto_with_rec_deterministic)

lemma tail_rec_steps_progress: "d \<turnstile>\<^sub>R'(c,s,ret)\<Rightarrow>\<^bsup>t\<^esup> s'' \<Longrightarrow> d \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup>x\<^esup> (s',Some r) \<Longrightarrow> t \<ge> x"
  apply (induction c s ret t s'' arbitrary: x s' r rule: tail_rec_steps_induct)
   apply (meson option.distinct(1) upto_with_rec_deterministic)
  by (metis le_add1 upto_with_rec_deterministic)

lemma tail_rec_steps_noninterference: 
  "\<lbrakk>d \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup>x \<^esup> s'; set (vars c) \<subseteq> S; set (vars d) \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> d \<turnstile>\<^sub>R' (c,s(v:=y),ret) \<Rightarrow>\<^bsup>x \<^esup> s'(v:=y)"
  apply (induction c s ret x s' rule: tail_rec_steps_induct)
   apply auto
   apply (simp add: trsFalse upto_with_rec_noninterference)
  by (meson order.trans trsTrue upto_with_rec_noninterference upto_with_rec_vars)

lemma tail_rec_steps_deterministic:
  "d \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> d \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup> t' \<^esup> s'' \<Longrightarrow> t = t' \<and> s' = s''" 
proof (induction c s ret t s' arbitrary: t' s'' rule: tail_rec_steps_induct)
  case (trsFalse c s ret t s')
  then show ?case 
    by (smt (verit, best) option.distinct(1) tail_rec_steps.simps
      upto_with_rec_deterministic)
next
  case (trsTrue c s ret x s' r y s''a)
  from tail_rec_step_E[OF \<open>d \<turnstile>\<^sub>R'(c, s, ret) \<Rightarrow>\<^bsup>t'\<^esup>  s''\<close> \<open>d \<turnstile>UPTO\<lbrakk> (c, s, ret) \<Rightarrow>\<^bsup>x\<^esup>  (s', Some r)\<close>]
  have \<open>y = t' - x \<and> s''a = s''\<close> 
    using trsTrue.IH by force
  hence \<open>x + y = t'\<close> using tail_rec_steps_progress 
    using le_add_diff_inverse trsTrue.hyps(1) trsTrue.prems by blast
  then show ?case 
    using \<open>y = t' - x \<and> s''a = s''\<close> by argo
qed

lemma tail_rec_steps_sound: "c' \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  apply (induction c s ret t s' rule: tail_rec_steps_induct)
  apply (simp add: upto_with_trec_sound)
  by (simp add: upto_with_rec_after)

lemma upto_with_rec_Ex: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<exists>x s'' r. c' \<turnstile>UPTO\<lbrakk> (c, s, ret) \<Rightarrow>\<^bsup>x\<^esup>  (s'', r)"
  apply (induction c' c s ret t s' rule: rbig_step_t_induct)
        apply auto
  subgoal
proof -
  fix ca :: rcom and c1 :: rcom and s1 :: "char list \<Rightarrow> nat" and reta :: "char list" and x :: nat and s2 :: "char list \<Rightarrow> nat" and c2 :: rcom and y :: nat and s3 :: "char list \<Rightarrow> nat" and xa :: nat and xb :: nat and s'' :: "char list \<Rightarrow> nat" and s''a :: "char list \<Rightarrow> nat" and r :: "rcom option" and ra :: "rcom option"
  assume a1: "ca \<turnstile>\<^sub>R (c1, s1, reta) \<Rightarrow>\<^bsup>x\<^esup> s2"
  assume a2: "ca \<turnstile>UPTO\<lbrakk> (c1, s1, reta) \<Rightarrow>\<^bsup>xa\<^esup> (s'', r)"
  assume a3: "ca \<turnstile>UPTO\<lbrakk> (c2, s2, reta) \<Rightarrow>\<^bsup>xb\<^esup> (s''a, ra)"
  have "\<forall>z. (None = z \<or> (\<exists>r. Some (r::rcom) = z)) \<and> ((\<forall>r. Some r \<noteq> z) \<or> None \<noteq> z)"
    by (metis (no_types) not_Some_eq)
  then show "\<exists>n f z. ca \<turnstile>UPTO\<lbrakk> (c1;; c2, s1, reta) \<Rightarrow>\<^bsup>n\<^esup> (f, z)"
    using a3 a2 a1 by (metis (full_types) upto_rec_Ex upto_no_rec_complete' upto_withSeqGRec upto_withSeqNoRec upto_withSeqTRec)
qed
      subgoal by blast
      subgoal by blast
      done

lemma upto_with_rec_steps_Ex: "c' \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> \<exists>x s'' r. c' \<turnstile>UPTO\<lbrakk> (c, s, ret) \<Rightarrow>\<^bsup>x\<^esup>  (s'', r)"
  by blast (*? ? ?*)

lemma upto_with_after_rec: " d \<turnstile>UPTO\<lbrakk> (c,s,ret) \<Rightarrow>\<^bsup>x\<^esup> (s',r) \<Longrightarrow> r = Some rc \<Longrightarrow> d \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'' 
                            \<Longrightarrow> d \<turnstile>\<^sub>R (rc,s',ret) \<Rightarrow>\<^bsup> t - x \<^esup> s''"
  apply (induction d c s ret x s' r arbitrary: rc s'' t rule: upto_with_rec_induct)
          apply auto
  apply (metis le_add1 ordered_cancel_comm_monoid_diff_class.diff_add_assoc2 rSeq rdeterministic
      upto_with_rec_after)
   apply (metis add_diff_cancel_left' rdeterministic upto_with_trec_sound)
  by (metis add_diff_cancel_left upto_no_rec_complete')

lemma tail_rec_steps_Seq: "d \<turnstile>\<^sub>R'(c1,s1,ret)\<Rightarrow>\<^bsup>t1\<^esup> s2 \<Longrightarrow> d \<turnstile>\<^sub>R'(c2,s2,ret)\<Rightarrow>\<^bsup>t2\<^esup> s3 \<Longrightarrow> t3 = t1 + t2 
                         \<Longrightarrow> d \<turnstile>\<^sub>R'(c1;;c2,s1,ret)\<Rightarrow>\<^bsup>t3\<^esup> s3"
proof (induction c1 s1 ret t1 s2 arbitrary: c2 t2 t3 s3 rule: tail_rec_steps_induct)
  case (trsFalse c s ret t s')
  obtain t1' s1' b where \<open> \<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t1'\<^esup>  (s1',b)\<close> 
    by (meson trsFalse.hyps upto_rec_Ex upto_with_trec_sound)
  obtain t2' s2' r2 where \<open> d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup>  (s2',r2)\<close>
    using upto_with_rec_steps_Ex[OF \<open>d \<turnstile>\<^sub>R'(c2, s', ret) \<Rightarrow>\<^bsup>t2\<^esup>  s3\<close>] by auto
  then show ?case proof(cases b)
    case True
    have \<open>d \<turnstile>UPTO\<lbrakk> (c;;c2, s, ret) \<Rightarrow>\<^bsup>t\<^esup>  (s',Some c2)\<close> 
      using True \<open>\<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t1'\<^esup> (s1', b)\<close> trsFalse.hyps by auto
    then show ?thesis 
      by (simp add: trsFalse.prems(1,2) trsTrue)
  next
    case False
    have \<open>d \<turnstile>UPTO\<lbrakk> (c;;c2, s, ret) \<Rightarrow>\<^bsup>t + t2'\<^esup>  (s2',r2)\<close> 
      by (metis (full_types) False \<open>\<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t1'\<^esup> (s1', b)\<close> \<open>d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup> (s2', r2)\<close> trsFalse.hyps
          upto_no_rec_complete' upto_withSeqNoRec upto_with_trec_sound)
    then show ?thesis proof(cases r2)
      case None
      then show ?thesis 
        by (metis \<open>d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup> (s2', r2)\<close> \<open>d \<turnstile>UPTO\<lbrakk> (c;; c2, s, ret) \<Rightarrow>\<^bsup>t + t2'\<^esup> (s2', r2)\<close> tail_rec_steps.trsFalse
            tail_rec_steps_deterministic trsFalse.prems(1,2))
    next
      case (Some a)
      hence \<open>d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup> (s2', Some a)\<close> 
        using \<open>d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup> (s2', r2)\<close> by auto
      hence \<open>d \<turnstile>\<^sub>R'(a, s2', ret) \<Rightarrow>\<^bsup>t2 - t2'\<^esup>  s3\<close> 
        using tail_rec_step_E[OF \<open>d \<turnstile>\<^sub>R'(c2, s', ret) \<Rightarrow>\<^bsup>t2\<^esup>  s3\<close> \<open>d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup> (s2', Some a)\<close> ]
        by argo
      then show ?thesis
        by (smt (verit, best) Some \<open>d \<turnstile>UPTO\<lbrakk> (c2, s', ret) \<Rightarrow>\<^bsup>t2'\<^esup> (s2', Some a)\<close> \<open>d \<turnstile>UPTO\<lbrakk> (c;; c2, s, ret) \<Rightarrow>\<^bsup>t + t2'\<^esup> (s2', r2)\<close>
            add.assoc le_add_diff_inverse tail_rec_steps_progress trsFalse.prems(1,2) trsTrue)
    qed
  qed
next
  case (trsTrue c s ret x s' r y s'')
  obtain t1' s1'  where \<open> \<turnstile>UPTO\<lparr> (c, s, ret) \<Rightarrow>\<^bsup>t1'\<^esup>  (s1',True)\<close> 
    by (metis (full_types) option.distinct(1) tail_rec_steps.trsTrue tail_rec_steps_sound trsTrue.hyps(1,2) upto_rec_Ex
        upto_rec_no_with upto_with_rec_deterministic)
  hence \<open>d \<turnstile>UPTO\<lbrakk> (c;;c2, s, ret) \<Rightarrow>\<^bsup>x\<^esup>  (s',Some (r;;c2))\<close> 
    using trsTrue.hyps(1) by blast
  from trsTrue.IH[OF \<open>d \<turnstile>\<^sub>R'(c2, s'', ret) \<Rightarrow>\<^bsup>t2\<^esup>  s3\<close>] have \<open>d \<turnstile>\<^sub>R'(r;; c2, s', ret) \<Rightarrow>\<^bsup>y + t2\<^esup>  s3\<close> by simp
  then show ?case 
    by (metis (no_types, lifting) \<open>d \<turnstile>UPTO\<lbrakk> (c;; c2, s, ret) \<Rightarrow>\<^bsup>x\<^esup> (s', Some (r;; c2))\<close> add.assoc tail_rec_steps.trsTrue
        trsTrue.prems(2))
qed

lemma tail_rec_steps_complete: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<Longrightarrow> c' \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
proof (induction c' c s ret t s' rule: rbig_step_t_induct)
  case (rAssign c x a s ret)
  have \<open>c \<turnstile>UPTO\<lbrakk> (x ::= a, s, ret) \<Rightarrow>\<^bsup>Suc (Suc 0)\<^esup>  (s(x := aval a s),None)\<close> by blast
  then show ?case by blast
next
  case (rSeq c c1 s1 ret x s2 c2 y s3 z)
  then show ?case 
     using tail_rec_steps_Seq[OF \<open>c \<turnstile>\<^sub>R'(c1, s1, ret) \<Rightarrow>\<^bsup>x\<^esup>  s2\<close> \<open>c \<turnstile>\<^sub>R'(c2, s2, ret) \<Rightarrow>\<^bsup>y\<^esup>  s3\<close> \<open>z = x + y\<close>] by argo
next
  case (rIfTrue s b c c1 ret x s' y c2)
  obtain x' s'' r where \<open>c \<turnstile>UPTO\<lbrakk> (c1, s, ret) \<Rightarrow>\<^bsup>x'\<^esup>  (s'',r)\<close> 
    using rIfTrue.IH by blast
  hence \<open>c \<turnstile>UPTO\<lbrakk>(IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup>  (s'',r)\<close> 
    by (simp add: rIfTrue.hyps(1) upto_withIfTrue)
  then show ?case proof(cases r)
    case None
    then show ?thesis 
      by (metis \<open>c \<turnstile>UPTO\<lbrakk> (IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup> (s'', r)\<close> \<open>c \<turnstile>UPTO\<lbrakk> (c1, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', r)\<close>
          rIfTrue.IH rIfTrue.hyps(3) tail_rec_steps_deterministic trsFalse)
  next
    case (Some a)
    hence \<open>c \<turnstile>UPTO\<lbrakk> (c1, s, ret) \<Rightarrow>\<^bsup>x'\<^esup>  (s'',Some a)\<close> 
      using \<open>c \<turnstile>UPTO\<lbrakk> (c1, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', r)\<close> by auto
    from tail_rec_step_E[OF \<open>c \<turnstile>\<^sub>R'(c1, s, ret) \<Rightarrow>\<^bsup>x\<^esup>  s'\<close> \<open>c \<turnstile>UPTO\<lbrakk> (c1, s, ret) \<Rightarrow>\<^bsup>x'\<^esup>  (s'',Some a)\<close>]
    have \<open>c \<turnstile>\<^sub>R'(a, s'', ret) \<Rightarrow>\<^bsup>x - x'\<^esup>  s'\<close> by argo
    have \<open>c \<turnstile>UPTO\<lbrakk>(IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup>  (s'',Some a)\<close> 
      using Some \<open>c \<turnstile>UPTO\<lbrakk> (IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup> (s'', r)\<close> by auto
    hence \<open>c \<turnstile>\<^sub>R'(IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x - x' + (x' + 1)\<^esup> s'\<close> 
      by (metis \<open>c \<turnstile>\<^sub>R'(a, s'', ret) \<Rightarrow>\<^bsup>x - x'\<^esup> s'\<close> add.commute trsTrue)
    then show ?thesis 
      using \<open>c \<turnstile>UPTO\<lbrakk> (c1, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', Some a)\<close> rIfTrue.IH rIfTrue.hyps(3) tail_rec_steps_progress by auto
  qed
next
  case (rIfFalse s b c c2 ret x s' y c1)
  obtain x' s'' r where \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup>  (s'',r)\<close> 
    using rIfFalse.IH by blast
  hence \<open>c \<turnstile>UPTO\<lbrakk>(IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup>  (s'',r)\<close> 
    by (simp add: rIfFalse.hyps(1) upto_withIfFalse)
  then show ?case proof(cases r)
    case None
    then show ?thesis 
      by (metis \<open>c \<turnstile>UPTO\<lbrakk> (IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup> (s'', r)\<close> \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', r)\<close>
          rIfFalse.IH rIfFalse.hyps(3) tail_rec_steps_deterministic trsFalse)
  next
    case (Some a)
    hence \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup>  (s'',Some a)\<close> 
      using \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', r)\<close> by auto
    from tail_rec_step_E[OF \<open>c \<turnstile>\<^sub>R'(c2, s, ret) \<Rightarrow>\<^bsup>x\<^esup>  s'\<close> \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup>  (s'',Some a)\<close>]
    have \<open>c \<turnstile>\<^sub>R'(a, s'', ret) \<Rightarrow>\<^bsup>x - x'\<^esup>  s'\<close> by argo
    have \<open>c \<turnstile>UPTO\<lbrakk>(IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup>  (s'',Some a)\<close> 
      using Some \<open>c \<turnstile>UPTO\<lbrakk> (IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x' + 1\<^esup> (s'', r)\<close> by auto
    hence \<open>c \<turnstile>\<^sub>R'(IF b\<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>x - x' + (x' + 1)\<^esup> s'\<close> 
      by (metis \<open>c \<turnstile>\<^sub>R'(a, s'', ret) \<Rightarrow>\<^bsup>x - x'\<^esup> s'\<close> add.commute trsTrue)
    then show ?thesis 
      using \<open>c \<turnstile>UPTO\<lbrakk> (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> (s'', Some a)\<close> rIfFalse.IH rIfFalse.hyps(3) tail_rec_steps_progress by auto
  qed
qed blast+
    
theorem tail_rec_steps_correct: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s' \<equiv> c' \<turnstile>\<^sub>R' (c,s,ret) \<Rightarrow>\<^bsup> t \<^esup> s'"
  by (smt (verit, best) tail_rec_steps_complete tail_rec_steps_sound)
  
end