theory Upto_Rec_Rest_Proof
  imports GRecToTRec "General_Recursive_IMP/GRec_Upto" 
begin

unbundle tscom_tagged_syntax and no com'_syntax and no tscom_syntax

(*The return point of an annotated program part*)
inductive
  return_point :: "tscom_tagged \<Rightarrow> tscom_tagged \<times> state \<times> fstack \<Rightarrow> nat \<Rightarrow> state \<times> fstack \<times> nat option \<Rightarrow> bool" ("_ \<turnstile>Rec\<rightharpoonup>i _ \<Rightarrow>\<^bsup> _ \<^esup> _" 55)
  where
rpSkip: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup> SKIP,s,stack) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,stack,n)" |
rpAssign: "c \<turnstile>Rec\<rightharpoonup>i (#n \<rightharpoonup> x ::= a,s,stack) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),stack,n)" |
rpSeq2: "\<lbrakk>c \<turnstile>Rec\<rightharpoonup>i (c1,s1,stack1) \<Rightarrow>\<^bsup>x\<^esup> (s2,stack2,n) ; c \<turnstile>Rec\<rightharpoonup>i (c2,s2,stack2) \<Rightarrow>\<^bsup>y\<^esup> (s3,stack3,r) ; z=x+y\<rbrakk> \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (c1 #;; c2, s1,stack1) \<Rightarrow>\<^bsup>z\<^esup> (s3,stack3,r)" |
rpIfTrue: "\<lbrakk>s b \<noteq> 0; c \<turnstile>Rec\<rightharpoonup>i (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> s'; y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>y \<^esup> s'" |
rpIfFalse: "\<lbrakk>s b = 0; c \<turnstile>Rec\<rightharpoonup>i (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> s'; y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#IF b \<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup>y \<^esup> s'" |
rpCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup> CALL C RETURN r,s,stack) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),stack,n)" |
rpRec: "c \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> z \<^esup> (s',stack',i) \<Longrightarrow>  c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>TAIL,s,stack) \<Rightarrow>\<^bsup>5 + z \<^esup> (s',stack',n)"|
rpPush: "c \<turnstile>Rec\<rightharpoonup>i  (#n\<rightharpoonup> PUSH x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s, stack(x := s x # stack x),n)"|
rpPop: "stack x = Cons v vx \<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>POP x,s,stack) \<Rightarrow>\<^bsup>Suc 0 \<^esup> (s(x := v), stack(x := vx),n)"
\<comment> \<open>New rule\<close>
bundle return_point
begin
notation return_point ("_ \<turnstile>Rec\<rightharpoonup>i _ \<Rightarrow> _" 55)
end

code_pred return_point .

declare return_point.intros[intro]

lemmas return_point_induct = return_point.induct[split_format(complete)]

inductive_cases rpSkip_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup> SKIP,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpAssign_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#n \<rightharpoonup> x ::= a,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpSeq_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (c1#;;c2,s1) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpIf_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpCall_tE[elim!]: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup> CALL C RETURN ret,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpRec_tE[elim]: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>TAIL,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpPush_tE[elim]: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>PUSH x,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"
inductive_cases rpPop_tE[elim]: "c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup>POP x,s) \<Rightarrow>\<^bsup>t\<^esup> (s',r)"

lemma enum_first_call: "c' \<turnstile>Rec\<rightharpoonup>i (c \<diamondop>Ret n,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',Some i) \<Longrightarrow> i \<ge> n"
  apply (induction c n arbitrary: c' s stack t s' stack' i rule: enum_ret_points_n.induct)
  apply auto by fastforce

lemma enum_last_call_count: "c' \<turnstile>Rec\<rightharpoonup>i (c \<diamondop>Ret n,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',Some i) \<Longrightarrow> i < n + ret_point_count c"
  apply (induction c n arbitrary: c' s stack t s' stack' i rule: enum_ret_points_n.induct)
  apply auto by fastforce+

lemma rp_Seq_None_E[elim]: "\<lbrakk>c \<turnstile>Rec\<rightharpoonup>i (c1,s1,stack1) \<Rightarrow>\<^bsup>t1\<^esup> (s2,stack2,r) ; r = None ; c \<turnstile>Rec\<rightharpoonup>i (c1#;;c2,s1,stack1) \<Rightarrow>\<^bsup>t\<^esup> (s3,stack3,r')\<rbrakk> 
\<Longrightarrow> c \<turnstile>Rec\<rightharpoonup>i (c2,s2,stack2) \<Rightarrow>\<^bsup>t - t1\<^esup> (s3,stack3,r')"
  oops

lemma rp_noninterference: 
  "\<lbrakk>c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (s',stack',r); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (c,s(v:=y),stack) \<Rightarrow>\<^bsup>x \<^esup> (s'(v:=y),stack',r)"
proof (induction c' c s stack x s' stack' r rule: return_point_induct)
  case (rpAssign c n x a s stack)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using return_point.rpAssign[of c n x a "s(v:=y)" stack] by argo
next
  case (rpCall C s z t c n r stack)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from rpCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using return_point.rpCall[OF Call, of c n r] state 
    by metis
next
  case (rpRec c s ret z r n)
  then show ?case 
    by blast
next
  case (rpPush c n x s stack)
  have \<open>v \<noteq> x\<close> using \<open>set (vars #n\<rightharpoonup> PUSH x) \<subseteq> S\<close> \<open>v \<notin> S\<close> by auto
  hence \<open>(s(v := y)) x = s x\<close> by simp
  then show ?case 
    by (metis return_point.rpPush)
next
  case (rpPop stack x va vx c n s)
  have \<open>v \<noteq> x\<close> using \<open>set (vars #n\<rightharpoonup> POP x) \<subseteq> S\<close> \<open>v \<notin> S\<close> by auto
  hence \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by auto
  have \<open>c \<turnstile>Rec\<rightharpoonup>i (#n\<rightharpoonup> POP x, s(v := y), stack) \<Rightarrow>\<^bsup>Suc 0\<^esup>  (s(v := y,x := va), stack(x := vx),n)\<close>
    using \<open>stack x = va # vx\<close> by blast
  then show ?case using \<open>(s(v := y, x := va)) = (s(x := va, v := y))\<close> by argo
qed auto

lemma fcdeterministic:
  "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',r) \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> t' \<^esup> (s'',stack'',r') \<Longrightarrow> t = t' \<and> s' = s'' \<and> stack' = stack'' \<and> r = r'"
proof (induction c' c s stack t s' stack' r arbitrary: t' s'' stack'' r' rule: return_point_induct)
  case (rpIfTrue s b c c1 stack x a a b y c2)
  then show ?case by fastforce
next
  case (rpIfFalse s b c c2 stack x s' stack' r y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN c1 ELSE c2, s, stack) \<Rightarrow>\<^bsup> t' \<^esup> (s'',stack'', r')\<close> obtain x' where
     \<open>c \<turnstile>Rec\<rightharpoonup>i (c2, s, stack) \<Rightarrow>\<^bsup>x'\<^esup> (s'',stack'',r')\<close> and \<open>t' = x' + 1\<close>
    by auto
  hence \<open> x' = x \<and> s' = s'' \<and> stack' = stack'' \<and> r = r'\<close>
    using rpIfFalse.IH by simp
  then show ?case 
    by (simp add: \<open>t' = x' + 1\<close> rpIfFalse.hyps(3))
next
  case (rpCall C s z t c r ret)
  then show ?case 
    using bigstep_det by blast
next
  case (rpPop stack x v vx c n s)
  then show ?case by auto
qed blast+

lemma rp_sound: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',r) \<Longrightarrow> #\<lbrakk> c' \<rbrakk>\<inverse> \<turnstile> (#\<lbrakk> c \<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack')"
proof (induction c' c s stack t s' stack' r rule: return_point_induct)
  case (rpAssign c n x a s stack)
  then show ?case  
    using tAssign untag_tscom.simps(5) by presburger
next
  case (rpCall C s z t c n r stack)
  then show ?case 
    using tCall untag_tscom.simps(6) by presburger
next
  case (rpPush c n x s stack)
  then show ?case 
    using tsPush untag_tscom.simps(7) by presburger
next
  case (rpPop stack x v vx c n s)
  then show ?case 
    using tsPop untag_tscom.simps(8) by presburger
qed auto

lemma rp_complete: "c' \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack') \<Longrightarrow> #\<lbrakk>c'\<rbrakk> \<turnstile>Rec\<rightharpoonup>i (#\<lbrakk>c\<rbrakk>,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',None)"
proof (induction c' c s stack t s' stack' rule: tsbig_step_t_induct)
  case (tAssign c x a s stack)
  then show ?case 
    using rpAssign tag_tscom.simps(5) by presburger
next
  case (tCall C s z t c r stack)
  then show ?case 
    using rpCall tag_tscom.simps(6) by presburger
next
  case (tsPush c x s stack)
  then show ?case 
    using rpPush tag_tscom.simps(7) by presburger
next
  case (tsPop stack x v vx c s)
  then show ?case 
    using rpPop tag_tscom.simps(8) by presburger
qed auto

lemma rp_correct: "c' \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack') \<equiv> #\<lbrakk>c'\<rbrakk> \<turnstile>Rec\<rightharpoonup>i (#\<lbrakk>c\<rbrakk>,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack',None)"
  by (smt (verit, del_insts) rp_complete rp_sound tscom_tag_correct)


lemma upto_syn_correct_no_rest: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> B) = (ut,rest) \<Longrightarrow> B = False \<Longrightarrow>
                        c' \<turnstile>Rec\<rightharpoonup>i (ut,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',None) \<Longrightarrow> no_rp c \<Longrightarrow>
                       c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',None)"
proof (induction c n B arbitrary: c' ut s stack x s' stack' rest rule: upto_rec_and_rest_syn.induct)
  case (1 b c1 c2 n B)
  obtain ut1 rest1 ut2 rest2 where \<open>UPTO\<lbrakk> c1 \<rbrakk> n \<Zsurj> B = (ut1, rest1)\<close> \<open>UPTO\<lbrakk> c2 \<rbrakk> length rest1 + n \<Zsurj> B = (ut2, rest2)\<close>
    by fastforce
  hence \<open>UPTO\<lbrakk> #IF b\<noteq>0 THEN c1 ELSE c2 \<rbrakk> n \<Zsurj> B = (#IF b\<noteq>0 THEN ut1 ELSE ut2, rest1@rest2)\<close> by auto
  hence \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN ut1 ELSE ut2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> 
    using "1.prems"(1,3) by auto
  then show ?case proof(cases "s b = 0")
    case True
    hence \<open>c' \<turnstile>Rec\<rightharpoonup>i (ut2, s, stack) \<Rightarrow>\<^bsup> x - 1\<^esup> (s', stack', None)\<close> 
      using \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN ut1 ELSE ut2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> 
      by auto
    moreover have \<open>no_rp c2\<close> 
      using "1.prems"(4) by auto
    ultimately have \<open>c' \<turnstile>Rec\<rightharpoonup>i (c2, s, stack) \<Rightarrow>\<^bsup> x - 1 \<^esup> (s', stack', None)\<close> 
      using "1.IH"(2) "1.prems"(3) \<open>UPTO\<lbrakk> c2 \<rbrakk> length rest1 + n \<Zsurj> B = (ut2, rest2)\<close> 
      using "1.prems"(2) \<open>UPTO\<lbrakk> c1 \<rbrakk> n \<Zsurj> B = (ut1, rest1)\<close> by auto
    then show ?thesis 
      using True \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN ut1 ELSE ut2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> by fastforce
  next
    case False
    hence \<open>c' \<turnstile>Rec\<rightharpoonup>i (ut1, s, stack) \<Rightarrow>\<^bsup> x - 1\<^esup> (s', stack', None)\<close> 
      using \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN ut1 ELSE ut2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> 
      by auto
    moreover have \<open>no_rp c1\<close> 
      using "1.prems"(4) by auto
    ultimately have \<open>c' \<turnstile>Rec\<rightharpoonup>i (c1, s, stack) \<Rightarrow>\<^bsup> x - 1 \<^esup> (s', stack', None)\<close> 
      using "1.IH"(1) "1.prems"(2) \<open>UPTO\<lbrakk> c1 \<rbrakk> n \<Zsurj> B = (ut1, rest1)\<close> by blast
    then show ?thesis 
      using False \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN ut1 ELSE ut2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> by fastforce
  qed
next
  case (2 c1 c2 n B)
  then show ?case sorry
next
  case (3 i n B)
  then show ?case sorry
next
  case (4 i x a n B)
  then show ?case sorry
next
  case (5 i c r n B)
  then show ?case sorry
next
  case (6 i n B)
  then show ?case sorry
next
  case (7 i v n B)
  then show ?case sorry
next
  case (8 i v n B)
  then show ?case sorry
qed


lemma upto_syn_full_correct_rest: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> B) = (ut,rest) \<Longrightarrow> B = False \<Longrightarrow>
                        c' \<turnstile>Rec\<rightharpoonup>i (ut,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',Some i) \<Longrightarrow> 
                       c' \<turnstile>Rec\<rightharpoonup>i (ut,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',Some i) \<Longrightarrow>
                       c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',None)"
  sorry

lemma upto_syn_full_correct_no_rest: "c' \<turnstile>Rec\<rightharpoonup>i (c \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',None,b)
                      \<Longrightarrow> #\<^sub>r\<lbrakk>c'\<rbrakk>\<inverse> \<turnstile>\<^sub>R (#\<^sub>r\<lbrakk>c\<rbrakk>\<inverse>,s,ret) \<Rightarrow>\<^bsup> x + y \<^esup> s''"
  sorry

lemma upto_syn_invar: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) \<Longrightarrow> tagged_invar ut"
  sorry


end