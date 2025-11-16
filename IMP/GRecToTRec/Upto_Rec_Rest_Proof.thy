theory Upto_Rec_Rest_Proof
  imports IMP_TCS_to_Tail_Recursive "General_Recursive_IMP/GRec_Upto" 
begin

unbundle tscom_tagged_syntax and no com'_syntax

(*The return point of an annotated program part*)

lemma upto_syn_correct_no_rest: "(*GRec\<lbrakk>\<diamondop>GRec\<lbrakk> #\<lbrakk>NORM c \<rbrakk>\<rbrakk>\<rbrakk> \<Zsurj> n) = (cn, rn) \<Longrightarrow>
                         #\<lbrakk>NORM c'\<rbrakk> \<turnstile>Rec\<rightharpoonup>i (cn,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',i) \<Longrightarrow>
                       c' \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack')"
proof (induction c arbitrary: c' s stack x s' stack' n cn rn)
  case tsSKIP
  then show ?case by auto
next
  case (tsPush x)
  then show ?case by auto
next
  case (tsPop x)
  then show ?case by auto
next
  case (tsAssign x1 x2a)
  then show ?case by auto
next
  case (tsSeq c1 c2)
  then show ?case sorry
next
  case (tsIf x1 c1 c2)
  then show ?case sorry
next
  case (tsCall x1 x2a)
  then show ?case by auto
next
  case tsTAIL
  then show ?case sorry
qed

lemma upto_syn_full_correct_no_rest: "c' \<turnstile>Rec\<rightharpoonup>i (c \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',None,b)
                      \<Longrightarrow> #\<^sub>r\<lbrakk>c'\<rbrakk>\<inverse> \<turnstile>\<^sub>R (#\<^sub>r\<lbrakk>c\<rbrakk>\<inverse>,s,ret) \<Rightarrow>\<^bsup> x + y \<^esup> s''"
  sorry

lemma upto_syn_invar: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) \<Longrightarrow> tagged_invar ut"
  sorry


end