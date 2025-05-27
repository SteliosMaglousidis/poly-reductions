theory Last_Rec_Call
  imports IMP_GRec "HOL-Library.Tree"
begin
unbundle no com_syntax and com'_syntax
unbundle rcom_syntax

inductive
  rlast_call :: "rcom \<Rightarrow> rcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<times> vname option \<Rightarrow> bool" ("_ \<turnstile>\<^sub>L\<^sub>C _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
rlcSkip: "c \<turnstile>\<^sub>L\<^sub>C (rSKIP,s) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,None)" |
rlcAssign: "c \<turnstile>\<^sub>L\<^sub>C (x ::= a,s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),None)" |
rlcSeq1: "\<lbrakk>c \<turnstile>\<^sub>L\<^sub>C (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2,r) ; c \<turnstile>\<^sub>L\<^sub>C (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> (s3,None) ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> (s3,r)" |
rlcSeq2: "\<lbrakk>c \<turnstile>\<^sub>L\<^sub>C (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2,r) ; c \<turnstile>\<^sub>L\<^sub>C (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> (s3,Some r') ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> (s3,Some r')" |
rlcIfTrue: "\<lbrakk> s b \<noteq> 0;  c \<turnstile>\<^sub>L\<^sub>C (c1,s) \<Rightarrow>\<^bsup>x \<^esup> (t,r); y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,r)" |
rlcIfFalse: "\<lbrakk> s b = 0; c \<turnstile>\<^sub>L\<^sub>C (c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,r); y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,r)" |
rlcCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r), Some r)" |
\<comment> \<open>New rule\<close>
rlcRec: "c \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,r) \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C (RECURSE,s) \<Rightarrow>\<^bsup>5 + z \<^esup> (t,r)"

code_pred rlast_call .

declare rlast_call.intros[intro]

lemmas rlast_call_induct = rlast_call.induct[split_format(complete)]

inductive_cases rlcSkip_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases rlcAssign_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases rlcSeq_tE1[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (t,None)"
inductive_cases rlcSeq_tE2[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (t,Some r)"
inductive_cases rlcSeq_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases rlcIf_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases rlcCall_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> t"

inductive_cases rlcRec_tE[elim]: "c \<turnstile>\<^sub>L\<^sub>C (RECURSE,s) \<Rightarrow>\<^bsup>x \<^esup> t"

fun call_count :: "rcom \<Rightarrow> nat" where
"call_count ((IF b\<noteq>0 THEN c1 ELSE c2)) = call_count c1 + call_count c2" |
"call_count (c1 ;; c2) =  call_count c1 + call_count c2" |
"call_count (CALL C RETURN r') = 1" |
"call_count _ = 0"

fun call_vars :: "rcom \<Rightarrow> vname list" where
"call_vars ((IF b\<noteq>0 THEN c1 ELSE c2)) = call_vars c1 @ call_vars c2" |
"call_vars (c1 ;; c2) =  call_vars c1 @ call_vars c2" |
"call_vars (CALL C RETURN r) = [r]" |
"call_vars _ = []"

fun call_vars_set :: "rcom \<Rightarrow> vname set" where
"call_vars_set ((IF b\<noteq>0 THEN c1 ELSE c2)) = call_vars_set c1 \<union> call_vars_set c2" |
"call_vars_set (c1 ;; c2) =  call_vars_set c1 \<union> call_vars_set c2" |
"call_vars_set (CALL C RETURN r) = {r}" |
"call_vars_set _ = {}"

lemma call_vars_set: "call_vars_set c = set (call_vars c)"
  by (induction c) auto

lemma call_vars_count: "length (call_vars c) \<le> call_count c"
  by (induction c) auto

lemma last_call_vars: "d \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup>z\<^esup> (t,r) \<Longrightarrow> the r \<in> set (call_vars c) \<union> set (call_vars d) \<or> r = None"
  by (induction d c s z t r rule: rlast_call_induct) auto

lemma last_call_sound: "d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> \<exists> r. d \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,r)"
  apply (induction d c s z t rule: rbig_step_t_induct) try
        apply blast
       apply blast 
      apply (metis not_Some_eq rlcSeq1 rlcSeq2)
  by blast+

lemma last_call_complete: "d \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,r)
  \<Longrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction d c s z t r rule: rlast_call_induct) fastforce+

lemma lc_deterministic: "c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,r) \<Longrightarrow> c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z' \<^esup> (t,r') \<Longrightarrow> z = z' \<and> r = r'"
proof (induction c' c s z t r arbitrary: r' z' rule: rlast_call_induct)
  case (rlcSeq1 c c1 s1 x s2 r c2 y s3 z)
  then show ?case proof (cases r')
    case None
     then show ?thesis proof(cases r)
       case None
       then show ?thesis using \<open>r = None\<close> \<open>r' = None\<close> 
         by (metis last_call_complete rdeterministic rlast_call.rlcSeq1 rlcSeq1.hyps(1,2,3)
             rlcSeq1.prems)
     next
       case (Some a)  
       have \<open>c \<turnstile>\<^sub>L\<^sub>C (c1;; c2, s1) \<Rightarrow>\<^bsup>z\<^esup>  (s3, None)\<close>
         using None rlcSeq1.prems 
         by (metis last_call_complete rSeq rdeterministic rlcSeq1.hyps(1,2,3))
       hence \<open>r = None\<close> using rlcSeq_tE1
         by (metis last_call_complete rdeterministic rlcSeq1.IH(1) rlcSeq1.hyps(1))
       then show ?thesis 
         by (simp add: Some)
     qed
  next
    case (Some a)
    then show ?thesis
      by (smt (verit, ccfv_threshold) Pair_inject last_call_complete option.distinct(1) rdeterministic
          rlcSeq1.IH(1,2) rlcSeq1.hyps(1,3) rlcSeq1.prems rlcSeq_tE)
  qed
next
  case (rlcSeq2 c c1 s1 x s2 r c2 y s3 v'a z)
  then show ?case proof (cases r')
    case None
     then show ?thesis proof(cases r)
       case None
       then show ?thesis using \<open>r = None\<close> \<open>r' = None\<close> 
         by (metis last_call_complete rdeterministic rlcSeq2.IH(2) rlcSeq2.hyps(1,3) rlcSeq2.prems
             rlcSeq_tE1)
     next
       case (Some a)  
       have \<open>c \<turnstile>\<^sub>L\<^sub>C (c1;; c2, s1) \<Rightarrow>\<^bsup>z\<^esup>  (s3, None)\<close>
         using None rlcSeq2.prems 
         by (metis last_call_complete rdeterministic rlast_call.rlcSeq2 rlcSeq2.hyps(1,2,3))
       hence \<open>r = None\<close> using rlcSeq_tE1 
         by (metis last_call_complete rdeterministic rlcSeq2.IH(1) rlcSeq2.hyps(1))
       then show ?thesis 
         by (simp add: Some)
     qed
  next
    case (Some a)
    then show ?thesis 
      by (smt (verit, del_insts) last_call_complete option.distinct(1) rdeterministic rlcSeq2.IH(2)
          rlcSeq2.hyps(1,3) rlcSeq2.prems rlcSeq_tE2)
  qed
next
  case (rlcIfTrue s b c c1 x t v y c2)
  then show ?case 
    by fastforce
next
  case (rlcIfFalse s b c c2 x t v y c1)
  then show ?case
    by (metis Suc_eq_plus1 less_numeral_extra(3) rlcIf_tE)
next
  case (rlcCall C s z t c r)
  then show ?case 
    using bigstep_det by blast
qed blast+


inductive
  rlast_call_val :: "rcom \<Rightarrow> rcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<times> val option \<Rightarrow> bool" ("_ \<turnstile>\<^sub>L\<^sub>C\<^sub>V _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
rlcvSkip: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (rSKIP,s) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,None)" |
rlcvAssign: "c\<turnstile>\<^sub>L\<^sub>C\<^sub>V (x ::= a,s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),None)" |
rlcvSeq1: "\<lbrakk>c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2,v) ; c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> (s3,None) ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> (s3,v)" |
rlcvSeq2: "\<lbrakk>c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2,v) ; c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> (s3,Some v') ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> (s3,Some v')" |
rlcvIfTrue: "\<lbrakk> s b \<noteq> 0;  c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1,s) \<Rightarrow>\<^bsup>x \<^esup> (t,v); y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,v)" |
rlcvIfFalse: "\<lbrakk> s b = 0; c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,v); y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,v)" |
rlcvCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r), Some (t r))" |
\<comment> \<open>New rule\<close>
rRec: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,v) \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (RECURSE,s) \<Rightarrow>\<^bsup>5 + z \<^esup> (t,v)"

code_pred rlast_call_val .

declare rlast_call_val.intros[intro]

lemmas rlast_call_val_induct = rlast_call_val.induct[split_format(complete)]

inductive_cases rlcvSkip_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases rlcvAssign_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases rlcvSeq_tE1[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (t,None)"
inductive_cases rlcvSeq_tE2[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (t,Some v)"
inductive_cases rlcvSeq_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases rlcvIf_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases rlcvCall_tE[elim!]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases rlcvRec_tE[elim]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (RECURSE,s) \<Rightarrow>\<^bsup>x \<^esup> t"


lemma lcv_seq_None[simp]: "c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1, s1) \<Rightarrow>\<^bsup>x\<^esup>  (s2, None) \<Longrightarrow> c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c2, s2) \<Rightarrow>\<^bsup>y\<^esup>  (s3, v)
  \<Longrightarrow>  c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;; c2, s1) \<Rightarrow>\<^bsup>x + y\<^esup>  (s3, v)"
  by (cases v) auto


lemma lcv_sound: "c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,v) \<Longrightarrow> c' \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c' c s z t v rule: rlast_call_val_induct) blast+

lemma lcv_complete: "c' \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> \<exists>v. c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,v)"
  apply (induction c' c s z t rule: rbig_step_t_induct)
  apply blast
       apply blast
      apply (metis not_Some_eq rlcvSeq1 rlcvSeq2)
  by blast+

lemma lcv_no_call: "c' \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> call_count c = 0 \<Longrightarrow> call_count c' = 0 \<Longrightarrow> c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,None)"
  by (induction c' c s z t  rule: rbig_step_t_induct) auto+


lemma lcv_deterministic: "c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,v) \<Longrightarrow> c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z' \<^esup> (t,v') \<Longrightarrow> z = z' \<and> v = v'"
proof (induction c' c s z t v arbitrary: v' z' rule: rlast_call_val_induct)
  case (rlcvSeq1 c c1 s1 x s2 v c2 y s3 z)
  then show ?case proof (cases v')
    case None
     then show ?thesis proof(cases v)
       case None
       then show ?thesis using \<open>v = None\<close> \<open>v' = None\<close> 
         by (metis lcv_sound rdeterministic rlast_call_val.rlcvSeq1 rlcvSeq1.hyps(1,2,3) rlcvSeq1.prems)
     next
       case (Some a)  
       have \<open>c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;; c2, s1) \<Rightarrow>\<^bsup>z\<^esup>  (s3, None)\<close>
         using None rlcvSeq1.prems 
         by (metis lcv_sound rbig_step_t.rSeq rdeterministic rlcvSeq1.hyps(1,2,3))
       hence \<open>v = None\<close> using rlcvSeq_tE1 
         by (metis lcv_sound rdeterministic rlcvSeq1.IH(1) rlcvSeq1.hyps(1))
       then show ?thesis 
         by (simp add: Some)
     qed
  next
    case (Some a)
    then show ?thesis 
      by (smt (verit) lcv_sound option.distinct(1) rdeterministic rlcvSeq1.IH(1,2) rlcvSeq1.hyps(1,3)
          rlcvSeq1.prems rlcvSeq_tE2)
  qed
next
  case (rlcvSeq2 c c1 s1 x s2 v c2 y s3 v'a z)
  then show ?case proof (cases v')
    case None
     then show ?thesis proof(cases v)
       case None
       then show ?thesis using \<open>v = None\<close> \<open>v' = None\<close>     
         by (metis lcv_sound option.simps(3) rdeterministic rlcvSeq2.IH(2) rlcvSeq2.hyps(1) rlcvSeq2.prems
             rlcvSeq_tE1)
     next
       case (Some a)  
       have \<open>c \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c1;; c2, s1) \<Rightarrow>\<^bsup>z\<^esup>  (s3, None)\<close>
         using None rlcvSeq2.prems 
         by (metis lcv_sound rbig_step_t.rSeq rdeterministic rlcvSeq2.hyps(1,2,3))
       hence \<open>v = None\<close> using rlcvSeq_tE1 
         by (metis lcv_sound rdeterministic rlcvSeq2.IH(1) rlcvSeq2.hyps(1))
       then show ?thesis 
         by (simp add: Some)
     qed
  next
    case (Some a)
    then show ?thesis 
      by (smt (verit) lcv_sound option.distinct(1) rdeterministic rlcvSeq2.IH(1,2) rlcvSeq2.hyps(1,3)
          rlcvSeq2.prems rlcvSeq_tE2)
  qed
next
  case (rlcvIfTrue s b c c1 x t v y c2)
  then show ?case 
    by fastforce
next
  case (rlcvIfFalse s b c c2 x t v y c1)
  then show ?case (*sledgehammer beats try*)
    by (metis Suc_eq_plus1 less_numeral_extra(3) rlcvIf_tE)
next
  case (rlcvCall C s z t c r)
  then show ?case 
    using bigstep_det by blast
qed blast+

lemma no_last_call_value1: "c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t, v) \<Longrightarrow> v = None \<Longrightarrow> c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,None)"
  by (induction c' c s z t v rule: rlast_call_val_induct) blast+

lemma no_last_call_value2: "c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t, r) \<Longrightarrow> r = None \<Longrightarrow> c'\<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,None)"
  by (induction c' c s z t r rule: rlast_call_induct) blast+

lemma no_last_call_value: "c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t, None) \<equiv> c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t, None)"
  using no_last_call_value1 no_last_call_value2  by (smt (verit))

lemma last_call_value1: "c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t, v) \<Longrightarrow> v = Some val \<Longrightarrow> \<exists>r. c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,Some r)"
  apply (induction c' c s z t v arbitrary: val rule: rlast_call_val_induct)
  apply simp 
        apply simp
  using no_last_call_value1 apply blast
      apply (meson last_call_sound lcv_sound rlast_call.rlcSeq2)
  by blast+

lemma last_call_value2: "c' \<turnstile>\<^sub>L\<^sub>C (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t, r) \<Longrightarrow> r = Some var \<Longrightarrow> \<exists>v. c' \<turnstile>\<^sub>L\<^sub>C\<^sub>V (c,s) \<Rightarrow>\<^bsup> z \<^esup> (t,Some v)"
  apply (induction c' c s z t r arbitrary: var rule: rlast_call_induct)
  apply simp 
        apply simp
  apply (metis no_last_call_value rlast_call_val.rlcvSeq1)
      apply (meson last_call_sound lcv_sound rlast_call.rlcSeq2)
      apply (meson last_call_complete lcv_complete rlast_call_val.rlcvSeq2)
  by blast+

end