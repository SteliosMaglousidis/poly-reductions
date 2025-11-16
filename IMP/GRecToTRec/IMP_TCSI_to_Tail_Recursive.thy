theory IMP_TCSI_to_Tail_Recursive
  imports IMP_TCS_to_IMP_TCSI
begin

fun TCIS_to_trec1 :: "tscom_tagged \<Rightarrow> tscom_tagged * tscom_tagged list" ("\<lbrakk> _ \<rbrakk>\<rightarrow>TREC" 55) where
   "\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2\<rbrakk>\<rightarrow>TREC =
    (let (ut1,r1) = \<lbrakk>c1\<rbrakk>\<rightarrow>TREC in 
      (let (ut2,r2) = \<lbrakk>c2\<rbrakk>\<rightarrow>TREC in 
        (#IF b\<noteq>0 THEN ut1 ELSE ut2,r1@r2)))"
  |"\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC = 
     (if stails_tagged c1 then 
       (let (ut1,r1) = \<lbrakk>c1\<rbrakk>\<rightarrow>TREC in (ut1, if r1 = [] then [c2] else map (\<lambda>x. x #;; c2) r1)) 
      else 
       (let (ut2,r2) = \<lbrakk>c2\<rbrakk>\<rightarrow>TREC in
         (c1 #;; ut2, r2)))"
  |"\<lbrakk>c\<rbrakk>\<rightarrow>TREC = (c,[])" 

declare TCIS_to_trec1.elims[elim]

lemmas TCIS_to_trec1.elims

lemma TCIS_to_trec1_Skip_fst[simp]: "fst (\<lbrakk>#SKIP\<rbrakk>\<rightarrow>TREC) = #SKIP"
  by auto
lemma TCIS_to_trec1_Assign_fst[simp]: "fst (\<lbrakk>#x ::= a\<rbrakk>\<rightarrow>TREC) = #x ::= a"
  by auto
lemma TCIS_to_trec1_Call_fst[simp]: "fst (\<lbrakk>#CALL c RETURN r\<rbrakk>\<rightarrow>TREC) = #CALL c RETURN r"
  by auto
lemma TCIS_to_trec1_Tail_fst[simp]: "fst (\<lbrakk>#i\<rightharpoonup> TAIL\<rbrakk>\<rightarrow>TREC) = #i\<rightharpoonup> TAIL"
  by auto
lemma TCIS_to_trec1_Push_fst[simp]: "fst (\<lbrakk>#PUSH x\<rbrakk>\<rightarrow>TREC) = #PUSH x"
  by auto
lemma TCIS_to_trec1_Pop_fst[simp]: "fst (\<lbrakk>#POP x\<rbrakk>\<rightarrow>TREC) = #POP x"
  by auto

lemma TCIS_to_trec1_If_fst[simp]: 
    "fst (\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2\<rbrakk>\<rightarrow>TREC) 
      = #IF b\<noteq>0 THEN (fst (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)) ELSE (fst (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC))"
  by (auto simp add: case_prod_beta)

lemma TCIS_to_trec1_Seq_fst[simp]:
    "stails_tagged c1 \<Longrightarrow> fst (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = fst (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)"
  apply auto by (metis (no_types, lifting) case_prod_conv fst_conv surj_pair)

lemma TCIS_to_trec1_Seq_fst'[simp]:
    "\<not>stails_tagged c1 \<Longrightarrow> fst (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = c1#;;fst (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC)"
  apply auto by (metis (no_types, lifting) case_prod_conv fst_conv surj_pair)

lemma TCIS_to_trec1_Skip_snd[simp]: "snd (\<lbrakk>#SKIP\<rbrakk>\<rightarrow>TREC) = []"
  by auto
lemma TCIS_to_trec1_Assign_snd[simp]: "snd (\<lbrakk>#x ::= a\<rbrakk>\<rightarrow>TREC) = []"
  by auto
lemma TCIS_to_trec1_Call_snd[simp]: "snd (\<lbrakk>#CALL c RETURN r\<rbrakk>\<rightarrow>TREC) = []"
  by auto
lemma TCIS_to_trec1_Tail_snd[simp]: "snd (\<lbrakk>#i\<rightharpoonup> TAIL\<rbrakk>\<rightarrow>TREC) = []"
  by auto
lemma TCIS_to_trec1_Push_snd[simp]: "snd (\<lbrakk>#PUSH x\<rbrakk>\<rightarrow>TREC) = []"
  by auto
lemma TCIS_to_trec1_Pop_snd[simp]: "snd (\<lbrakk>#POP x\<rbrakk>\<rightarrow>TREC) = []"
  by auto

lemma TCIS_to_trec1_If_snd[simp]: 
    "snd (\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2\<rbrakk>\<rightarrow>TREC) 
      = (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)) @ (snd (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC))"
  by (auto simp add: case_prod_beta)

lemma TCIS_to_trec1_Seq_snd[simp]:
    "stails_tagged c1 \<Longrightarrow> snd (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = (if (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)) = [] then [c2] else map (\<lambda>x. x #;; c2) (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)))"
  by (auto simp add: case_prod_beta) 

lemma TCIS_to_trec1_Seq_snd'[simp]:
    "\<not>stails_tagged c1 \<Longrightarrow> snd (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = (snd (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC))"
  by (auto simp add: case_prod_beta)

lemma TCIS_to_trec1_no_rest_invar: "\<lbrakk>c\<rbrakk>\<rightarrow>TREC = (sb,rest) \<Longrightarrow> rest = [] \<Longrightarrow> sinvar_tagged c"
apply (induction c arbitrary: sb rest rule: TCIS_to_trec1.induct)
         apply auto
     apply (metis (mono_tags, lifting) Nil_is_append_conv case_prod_conv eq_snd_iff)
    apply (metis (mono_tags, lifting) Nil_is_append_conv case_prod_conv eq_snd_iff)
  apply (metis (lifting) TCIS_to_trec1.simps(2) TCIS_to_trec1_Seq_snd case_prod_conv list.map_disc_iff not_Cons_self2
      snd_def)
  by (smt (verit, ccfv_threshold) Nil_is_map_conv list.distinct(1) old.prod.case snd_conv surj_pair)

lemma TCIS_to_trec1_no_rest: "\<lbrakk>c\<rbrakk>\<rightarrow>TREC = (sb,rest) \<Longrightarrow> rest = [] \<Longrightarrow> c = sb"
proof (induction c arbitrary: sb rest rule: TCIS_to_trec1.induct)
  case (1 b c1 c2)
  obtain sb1 rest1 sb2 rest2 
    where "\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)" "\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (sb2, rest2)"
    by fastforce
  have "rest = rest1@rest2" using \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC  = (sb1, rest1)\<close> \<open>\<lbrakk>c2\<rbrakk>\<rightarrow>TREC  = (sb2, rest2)\<close>
      \<open>\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2\<rbrakk>\<rightarrow>TREC  = (sb, rest)\<close> by simp
  hence \<open>rest1 = []\<close> \<open>rest2 = []\<close> by (simp add: "1.prems"(2))+
  then show ?case 
    using "1.IH"(1,2) "1.prems"(1) \<open>\<lbrakk> c1 \<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> \<open>\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC = (sb2, rest2)\<close> by auto
next
  case (2 c1 c2)
  obtain sb1 rest1 sb2 rest2 
    where "\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)" "\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (sb2, rest2)"
    by fastforce
  then show ?case apply (cases "stails_tagged c1")
    using "2.prems"(1,2) TCIS_to_trec1_no_rest_invar sinvar_tagged.simps(1) apply blast
    using "2.IH"(2) "2.prems"(1,2) by auto
qed auto

lemma TCIS_to_trec1_no_rest': "snd (\<lbrakk>c\<rbrakk>\<rightarrow>TREC) = [] \<Longrightarrow> c = fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC)"
  using TCIS_to_trec1_no_rest prod.exhaust_sel by blast

lemma rest_size : "\<lbrakk>c\<rbrakk>\<rightarrow>TREC = (sb,rest) \<Longrightarrow> rc \<in> set rest \<Longrightarrow> size rc < size c"
proof (induction c arbitrary: sb rest rc rule: TCIS_to_trec1.induct)
  case (1 b c1 c2)
  obtain sb1 rest1 sb2 rest2 
    where "\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)" "\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (sb2, rest2)"
    by fastforce
  have "rest = rest1@rest2" using \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC  = (sb1, rest1)\<close> \<open>\<lbrakk>c2\<rbrakk>\<rightarrow>TREC  = (sb2, rest2)\<close>
      \<open>\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2\<rbrakk>\<rightarrow>TREC  = (sb, rest)\<close> by simp
  hence \<open>rc \<in> set rest1 \<or> rc \<in> set rest2\<close> 
    using "1.prems"(2) by force
  then show ?case apply (cases "rc \<in> set rest1")
    apply auto 
    using "1.IH"(1) \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> apply force
    by (simp add: "1.IH"(2) \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> \<open>\<lbrakk>c2\<rbrakk>\<rightarrow>TREC  = (sb2, rest2)\<close> less_Suc_eq
        trans_less_add2)
next
  case (2 c1 c2) 
  then show ?case proof(cases \<open>stails_tagged c1\<close>)
    case True
    obtain sb1 rest1 
    where "\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)" 
    by fastforce
    then show ?thesis proof(cases \<open>rest1 = []\<close>)
      case True
      have \<open>\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC = (sb1, [c2])\<close>  
        using \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> \<open>stails_tagged c1\<close> \<open>rest1 = []\<close> 
        by simp
      hence \<open>sb = sb1\<close> \<open>rest = [c2]\<close>  
        using "2.prems"(1) apply fastforce
        using "2.prems"(1) \<open>\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC = (sb1, [c2])\<close> by fastforce
        hence \<open>rc = c2\<close> 
          using "2.prems"(2) by fastforce
      then show ?thesis 
        by auto
    next
      case False
      have \<open>\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC = (sb1, map (\<lambda>x. x #;; c2) rest1)\<close>
        using \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> \<open>stails_tagged c1\<close> \<open>rest1 \<noteq> []\<close>
        by simp
      hence \<open>sb = sb1\<close> \<open>rest = map (\<lambda>x. x #;; c2) rest1\<close>  
        using "2.prems"(1) apply fastforce
        using "2.prems"(1) \<open>\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC = (sb1, map (\<lambda>x. x #;; c2) rest1)\<close>
        by force
      hence \<open>rc \<in> set (map (\<lambda>x. x #;; c2) rest1)\<close>
        using "2.prems"(2) by fastforce
      have \<open>\<forall>x. x \<in> set rest1 \<longrightarrow> size x \<le> size c1\<close>
        by (simp add: "2.IH"(1) True \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> order_le_less)
      hence \<open>\<forall>x. x \<in> set (map (\<lambda>x. x #;; c2) rest1) \<longrightarrow> size x \<le> size (c1 #;; c2)\<close>
        by auto
      then show ?thesis using \<open>rc \<in> set (map (\<lambda>x. x #;; c2) rest1)\<close> \<open>\<forall>x. x \<in> set (map (\<lambda>x. x #;; c2) rest1) \<longrightarrow> size x \<le> size (c1 #;; c2)\<close>
        using "2.IH"(1) True \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (sb1, rest1)\<close> by force
    qed
  next
    case False
    obtain sb2 rest2 
      where "\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (sb2, rest2)"
    by fastforce
    have \<open>\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC = (c1 #;; sb2, rest2)\<close>
      using False \<open>\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (sb2, rest2)\<close> by auto
    hence \<open>rest = rest2\<close>
      using "2.prems"(1) by auto
    hence \<open>rc \<in> set rest2\<close> using \<open>rc \<in> set rest\<close> by simp
    then show ?thesis 
      using "2.IH"(2) False \<open>\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (sb2, rest2)\<close>
      by fastforce
  qed
qed auto

lemma TCIS_to_trec1_no_branches: "\<not>branches c \<Longrightarrow> \<not>branches (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC))"
  by (induction c rule: TCIS_to_trec1.induct) (auto simp add: case_prod_beta)

lemma TCIS_to_trec1_norm: "\<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow> \<turnstile>\<^bsub>NORM\<^esub> (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC))"
  apply (induction c rule: TCIS_to_trec1.induct) 
         apply (auto simp add: case_prod_beta)
  using prod.collapse apply blast
  using no_branches_norm by blast

lemma TCIS_to_trec1_None: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',i) \<Longrightarrow>
                        i = None \<Longrightarrow>
                        \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
                        \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
                       c' \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC),s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',None)"
proof(induction c' c s stack t s' stack' i  rule: first_rec_index_induct)
  case (iAssign c x a s stack)
  then show ?case 
    using TCIS_to_trec1_Assign_fst first_rec_index.iAssign by presburger
next
  case (iSeqNone c c1 s1 stack1 x s2 stack2 c2 y s3 stack3 i2 z)
  then show ?case 
    using TCIS_to_trec1_Seq_fst' non_branching_no_rec' by auto
next
  case (iSeqSome c c1 s1 stack1 x s2 stack2 i c2 y s3 stack3 j z)
  then show ?case by blast
next
  case (iIfTrue s b c c1 stack x a a b y c2)
  then show ?case
    using TCIS_to_trec1_If_fst by auto
next
  case (iIfFalse s b c c2 stack x a a b y c1)
  then show ?case 
    using TCIS_to_trec1_If_fst by auto
next
  case (iCall C s z t c r stack)
  then show ?case 
    using TCIS_to_trec1_Call_fst first_rec_index.iCall by presburger
next
  case (iPush c x s stack)
  then show ?case 
    using TCIS_to_trec1_Push_fst first_rec_index.iPush by presburger
next
  case (iPop stack x v vx c s)
  then show ?case
    using TCIS_to_trec1_Pop_fst first_rec_index.iPop by presburger
qed auto

lemma TCIS_to_trec1_None': "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',None) \<Longrightarrow>
                        \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
                        \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
                       c' \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC),s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',None)"
  by (simp add: TCIS_to_trec1_None)

lemma TCIS_to_trec1_Some_fst: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',i) \<Longrightarrow>
                        i = Some j\<Longrightarrow>
                        \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
                        \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
                       \<exists>s'' stack'' t'. c' \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC),s,stack) \<Rightarrow>\<^bsup>t'\<^esup> (s'',stack'',Some j) \<and> t \<ge> t'"
proof(induction c' c s stack t s' stack' i arbitrary: j rule: first_rec_index_induct)
  case (iSeqNone c c1 s1 stack1 x s2 stack2 c2 y s3 stack3 i2 z)
  then show ?case 
    using TCIS_to_trec1_Seq_fst' non_branching_no_rec' 
    by fastforce
next
  case (iSeqSome c c1 s1 stack1 x s2 stack2 i c2 y s3 stack3 ja z)
  then show ?case using TCIS_to_trec1_Seq_fst non_branching_rec' no_branches_norm rec_grec_identified 
    by fastforce
next
  case (iIfTrue s b c c1 stack x a a b y c2)
  then show ?case 
    using TCIS_to_trec1_If_fst 
    by fastforce
next
  case (iIfFalse s b c c2 stack x a a b y c1)
  then show ?case 
    using TCIS_to_trec1_If_fst 
    by fastforce
next
  case (iRec c s stack z s' stack' i n)
  then show ?case by force
qed blast+

lemma TCIS_to_trec1_Some': "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',Some i) \<Longrightarrow>
                        \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
                        \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
                       \<exists>s'' stack'' t'. c' \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC),s,stack) \<Rightarrow>\<^bsup>t'\<^esup> (s'',stack'',Some i) \<and> t \<ge> t'"
  by (simp add: TCIS_to_trec1_Some_fst)


lemma TCIS_to_trec1_Some_no_rest: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',i) \<Longrightarrow>
                        snd (\<lbrakk>c\<rbrakk>\<rightarrow>TREC) = [] \<Longrightarrow>
                        c' \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC),s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',i)"
  using TCIS_to_trec1_no_rest' by simp


lemma arec_call_enumerated_index: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',ai) \<Longrightarrow>
       ai = Some i \<Longrightarrow>
       \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
       \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
       \<turnstile>\<^bsub>*$Rec\<^esub> c \<Zsurj> n = (True,rn) \<Longrightarrow> 
       rn \<ge> i - n"
proof(induction c' c s stack t s' stack' ai arbitrary: i  n rn rule: first_rec_index_induct)
  case (iSeqNone c c1 s1 stack1 x s2 stack2 c2 y s3 stack3 i2 z)
  from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 #;; c2 \<Zsurj> n = (True, rn)\<close> obtain
      rn1 rn2 where \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>rn = rn1 + rn2\<close>
      apply auto using arec_call_enumerated_Seq_fst arec_call_enumerated_Seq_snd 
    by (smt (verit, del_insts) fst_conv iSeqNone.prems(4) snd_conv surjective_pairing)
  have \<open>\<not>stails_tagged c1\<close> using non_branching_no_rec' 
    using iSeqNone.hyps(1) iSeqNone.prems(2,3) by auto
  hence \<open>rn1 = 0\<close> using \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> no_rec_enumerated_count' 
    by (metis sndI)
  have \<open>\<turnstile>\<^bsub>NORM\<^esub> c2\<close> 
    using iSeqNone.prems(2) no_branches_norm by auto
  have \<open>\<turnstile>\<^bsub>$GRec\<^esub> c2\<close>
    using grec_annotated.simps(1) iSeqNone.prems(3) rec_grec_identified by auto
  have \<open>i - (n + rn1) \<le> rn2\<close> using iSeqNone.IH(2)[OF \<open>i2 = Some i\<close> \<open>\<turnstile>\<^bsub>NORM\<^esub> c2\<close> \<open>\<turnstile>\<^bsub>$GRec\<^esub> c2\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close>]
    by blast
  hence \<open>i - n \<le> rn2\<close> using \<open>rn1 = 0\<close> by simp
    then show ?case using \<open>rn = rn1 + rn2\<close> trans_le_add2 by blast
next
  case (iSeqSome c c1 s1 stack1 x s2 stack2 i' c2 y s3 stack3 j z)
    have \<open>\<turnstile>\<^bsub>NORM\<^esub> c1\<close> 
      using iSeqSome.prems(2) no_branches_norm by auto
    have \<open>\<turnstile>\<^bsub>$GRec\<^esub> c1\<close>
      using grec_annotated.simps(1) iSeqSome.prems(3) rec_grec_identified by auto
    from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 #;; c2 \<Zsurj> n = (True, rn)\<close> obtain
      rn1 rn2 where \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>rn = rn1 + rn2\<close>
      apply auto using arec_call_enumerated_Seq_fst arec_call_enumerated_Seq_snd 
      by (smt (verit, del_insts) fst_conv iSeqSome.prems(4) snd_conv surjective_pairing)
    have \<open>i - n \<le> rn1\<close> using iSeqSome.IH(1)[OF \<open>Some i' = Some i\<close> \<open>\<turnstile>\<^bsub>NORM\<^esub> c1\<close> \<open>\<turnstile>\<^bsub>$GRec\<^esub> c1\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close>]
      by simp
  then show ?case 
    using \<open>rn = rn1 + rn2\<close> trans_le_add1 by blast
next
  case (iIfTrue s b c c1 stack x a a i' y c2)
    from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> #IF b\<noteq>0 THEN c1 ELSE c2 \<Zsurj> n = (True, rn)\<close> obtain
      rn1 rn2 where \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>rn = rn1 + rn2\<close>
      apply auto using arec_call_enumerated_If_fst arec_call_enumerated_If_snd 
    by (smt (verit, del_insts) fst_conv iIfTrue.prems(4) snd_conv surjective_pairing)
    have \<open>\<turnstile>\<^bsub>NORM\<^esub> c1\<close> 
      using iIfTrue.prems(2) no_branches_norm by auto
    have \<open>\<turnstile>\<^bsub>$GRec\<^esub> c1\<close>
      using grec_annotated.simps(1) iIfTrue.prems(3) rec_grec_identified by auto
    from iIfTrue.IH[OF \<open>i' = Some i\<close> \<open>\<turnstile>\<^bsub>NORM\<^esub> c1\<close> \<open>\<turnstile>\<^bsub>$GRec\<^esub> c1\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close>]
    have \<open>i - n \<le> rn1\<close> by simp
  then show ?case 
    using \<open>rn = rn1 + rn2\<close> trans_le_add1 by blast
next
  case (iIfFalse s b c c2 stack x a a i' y c1)
    from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> #IF b\<noteq>0 THEN c1 ELSE c2 \<Zsurj> n = (True, rn)\<close> obtain
      rn1 rn2 where \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>rn = rn1 + rn2\<close>
      apply auto using arec_call_enumerated_If_fst arec_call_enumerated_If_snd 
    by (smt (verit, del_insts) fst_conv iIfFalse.prems(4) snd_conv surjective_pairing)
    have \<open>\<turnstile>\<^bsub>NORM\<^esub> c2\<close> 
      using iIfFalse.prems(2) no_branches_norm by auto
    have \<open>\<turnstile>\<^bsub>$GRec\<^esub> c2\<close>
      using grec_annotated.simps(1) iIfFalse.prems(3) rec_grec_identified by auto
    from iIfFalse.IH[OF \<open>i' = Some i\<close> \<open>\<turnstile>\<^bsub>NORM\<^esub> c2\<close> \<open>\<turnstile>\<^bsub>$GRec\<^esub> c2\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close>]
    have \<open>i - (n + rn1) \<le> rn2\<close> by simp
  then show ?case 
    using \<open>rn = rn1 + rn2\<close> by simp
qed auto

lemma arec_call_enumerated_index': "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',Some i) \<Longrightarrow>
       \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
       \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
       \<turnstile>\<^bsub>*$Rec\<^esub> c \<Zsurj> n = (True,rn) \<Longrightarrow> 
       rn \<ge> i - n"
  using arec_call_enumerated_index by auto

lemma arec_call_enumerated_rest_len: "\<lbrakk>c\<rbrakk>\<rightarrow>TREC = (sb,rest) \<Longrightarrow>
                                      \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>           
                                      rest \<noteq> [] \<Longrightarrow>
                                      \<turnstile>\<^bsub>*$Rec\<^esub> c \<Zsurj> n = (True,rn) \<Longrightarrow> 
                                      length rest = rn"
proof (induction c arbitrary: sb rest n rn rule: TCIS_to_trec1.induct)
  case (1 b c1 c2)
  then show ?case 
next
  case (2 c1 c2)
  then show ?case sorry
qed auto

lemma TCIS_to_trec1_Some_snd: "c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',ai) \<Longrightarrow>
                        ai = Some i \<Longrightarrow>
                        \<turnstile>\<^bsub>NORM\<^esub> c \<Longrightarrow>
                        \<turnstile>\<^bsub>$GRec\<^esub> c \<Longrightarrow>
                        snd (\<lbrakk>c\<rbrakk>\<rightarrow>TREC) \<noteq> [] \<Longrightarrow>
                        \<turnstile>\<^bsub>*$Rec\<^esub> c \<Zsurj> n = (True,rn) \<Longrightarrow>
                        c' \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c\<rbrakk>\<rightarrow>TREC),s,stack) \<Rightarrow>\<^bsup>t'\<^esup> (s'',stack'',Some i) \<Longrightarrow>
                        \<exists>j . c' \<turnstile>Rec\<rightharpoonup>i (snd (\<lbrakk>c\<rbrakk>\<rightarrow>TREC) ! (i-n),s'',stack'') \<Rightarrow>\<^bsup>t - t'\<^esup> (s',stack',j) "
proof(induction c' c s stack t s' stack' ai arbitrary: i s'' stack'' t' n rn rule: first_rec_index_induct)
  case (iSeqNone c c1 s1 stack1 x s2 stack2 c2 y s3 stack3 i2 z)
  have \<open>fst (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = c1#;;fst (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC)\<close> 
      using TCIS_to_trec1_Seq_fst' grec_annotated.simps(1) iSeqNone.hyps(1) iSeqNone.prems(2,3) non_branching_no_rec
        normalized.simps(1) grecs_only_grecs_annotated by blast
    from \<open>c \<turnstile>Rec\<rightharpoonup>i (c1, s1, stack1) \<Rightarrow>\<^bsup> x \<^esup> (s2, stack2, None)\<close> this
         \<open>c \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk> c1 #;; c2 \<rbrakk>\<rightarrow>TREC), s1, stack1) \<Rightarrow>\<^bsup> t' \<^esup> (s'', stack'', Some i)\<close>
    have \<open>c \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC), s2, stack2) \<Rightarrow>\<^bsup> t' - x \<^esup> (s'', stack'', Some i)\<close> 
      by (smt (verit, best) add_diff_cancel_left' iSeq_tE lri_deterministic option.discI)
    from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 #;; c2 \<Zsurj> n = (True, rn)\<close> obtain
      rn1 rn2 where \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>rn = rn1 + rn2\<close>
      apply auto using arec_call_enumerated_Seq_fst arec_call_enumerated_Seq_snd 
      by (smt (verit, del_insts) fst_conv iSeqNone.prems(5) snd_conv surjective_pairing)
    have \<open>\<not>stails_tagged c1\<close> 
      using iSeqNone.hyps(1) iSeqNone.prems(2,3) non_branching_no_rec' by auto
    from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<not>stails_tagged c1\<close> 
          no_rec_enumerated_count' have \<open>rn1 = 0\<close> by (metis sndI) 
    then show ?case proof (cases "snd (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC) \<noteq> []")
      case True
    obtain j where \<open>c \<turnstile>Rec\<rightharpoonup>i (snd (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC) ! (i - (n + rn1)), s'', stack'') \<Rightarrow>\<^bsup> y - (t' - x) \<^esup> (s3, stack3, j)\<close>
      using \<open>i2 = Some i\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>c \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC), s2, stack2) \<Rightarrow>\<^bsup> t' - x \<^esup> (s'', stack'', Some i)\<close>
      using grec_annotated.simps(1) iSeqNone.IH(2) iSeqNone.prems(2,3) normalized.simps(1) 
      using True by blast
    hence \<open>c \<turnstile>Rec\<rightharpoonup>i (snd (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC) ! (i - n), s'', stack'') \<Rightarrow>\<^bsup> y - (t' - x) \<^esup> (s3, stack3, j)\<close>
      using \<open>rn1 = 0\<close> by auto
    have \<open>snd (\<lbrakk> c1 #;; c2 \<rbrakk>\<rightarrow>TREC) = snd (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC)\<close> using \<open>\<not>stails_tagged c1\<close> 
      using TCIS_to_trec1_Seq_snd' by auto
    hence \<open>(snd (\<lbrakk> c1 #;; c2 \<rbrakk>\<rightarrow>TREC)) ! (i - n) = (snd (\<lbrakk>c2\<rbrakk>\<rightarrow>TREC))! (i - n)\<close> by simp 
      then show ?thesis using \<open>c \<turnstile>Rec\<rightharpoonup>i (snd (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC) ! (i - n), s'', stack'') \<Rightarrow>\<^bsup> y - (t' - x)\<^esup> (s3, stack3, j)\<close>
        by (metis (no_types, opaque_lifting) \<open>c \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC), s2, stack2) \<Rightarrow>\<^bsup> t' - x \<^esup> (s'', stack'', Some i)\<close>
            \<open>fst (\<lbrakk> c1 #;; c2 \<rbrakk>\<rightarrow>TREC) = c1 #;; fst (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC)\<close> add_diff_cancel_left iSeqNone.hyps(1,3) iSeqNone.prems(6)
            iSeq_annot_Ex lri_deterministic)
    next
      case False
      have \<open>fst (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC) = c2\<close>
        using False TCIS_to_trec1_no_rest' by auto
      then show ?thesis 
        using False TCIS_to_trec1_Seq_snd' \<open>\<not> stails_tagged c1\<close> iSeqNone.prems(4) by auto
    qed
next
  case (iSeqSome c c1 s1 stack1 x s2 stack2 i' c2 y s3 stack3 j z)
    from \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 #;; c2 \<Zsurj> n = (True, rn)\<close> obtain
      rn1 rn2 where \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close> \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c2 \<Zsurj> (n + rn1) = (True, rn2)\<close> \<open>rn = rn1 + rn2\<close>
      apply auto using arec_call_enumerated_Seq_fst arec_call_enumerated_Seq_snd 
      by (smt (verit, del_insts) fst_conv iSeqSome.prems(5) snd_conv surjective_pairing)
    have \<open>stails_tagged c1\<close>
      using iSeqSome.hyps(1) iSeqSome.prems(2,3) non_branching_rec' by auto 
    hence \<open>fst (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = fst (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)\<close> 
          \<open>snd (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = (if (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)) = [] then [c2] else map (\<lambda>x. x #;; c2) (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)))\<close>
      using TCIS_to_trec1_Seq_fst TCIS_to_trec1_Seq_snd by auto
    hence \<open>c \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC), s1, stack1) \<Rightarrow>\<^bsup> t' \<^esup> (s'', stack'', Some i)\<close> 
      using iSeqSome.prems(6) by auto
    have \<open>\<turnstile>\<^bsub>NORM\<^esub> c1\<close> 
      using iSeqSome.prems(2) no_branches_norm by auto
    have \<open>\<turnstile>\<^bsub>$GRec\<^esub> c1\<close>
      using grec_annotated.simps(1) iSeqSome.prems(3) rec_grec_identified by auto
    have \<open>\<turnstile>\<^bsub>NORM\<^esub> c2\<close> 
      using iSeqSome.prems(2) no_branches_norm by auto
    have \<open>\<turnstile>\<^bsub>$GRec\<^esub> c2\<close>
      using grec_annotated.simps(1) iSeqSome.prems(3) rec_grec_identified by auto
    then show ?case proof(cases \<open>snd (\<lbrakk> c1 \<rbrakk>\<rightarrow>TREC) \<noteq> []\<close>)
      case True
      have \<open>snd (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = (map (\<lambda>x. x #;; c2) (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)))\<close>
        using True \<open>snd (\<lbrakk>c1 #;; c2\<rbrakk>\<rightarrow>TREC) = (if (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)) = [] then [c2] else map (\<lambda>x. x #;; c2) (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC)))\<close>
        by simp
      hence \<open>(map (\<lambda>x. x #;; c2) (snd (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC))) ! (i - n) = (snd (\<lbrakk> c1 \<rbrakk>\<rightarrow>TREC) ! (i - n)) #;; c2 \<close> 
      obtain j where \<open>c \<turnstile>Rec\<rightharpoonup>i (snd (\<lbrakk> c1 \<rbrakk>\<rightarrow>TREC) ! (i - n), s'', stack'') \<Rightarrow>\<^bsup> x - t' \<^esup> (s2, stack2, j)\<close>
        using iSeqSome.IH(1)[OF \<open>Some i' = Some i\<close> \<open>\<turnstile>\<^bsub>NORM\<^esub> c1\<close> \<open>\<turnstile>\<^bsub>$GRec\<^esub> c1\<close> True \<open>\<turnstile>\<^bsub>*$Rec\<^esub> c1 \<Zsurj> n = (True, rn1)\<close>
          \<open>c \<turnstile>Rec\<rightharpoonup>i (fst (\<lbrakk>c1\<rbrakk>\<rightarrow>TREC), s1, stack1) \<Rightarrow>\<^bsup> t' \<^esup> (s'', stack'', Some i)\<close>] by blast
      then show ?thesis proof(cases \<open>snd (\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC) \<noteq> []\<close>)
        case True
        then show ?thesis proof(cases \<open>j = None\<close>)
          case True
          then show ?thesis sorry
        next
          case False
          then show ?thesis sorry
        qed
      next
        case False
        then show ?thesis sorry
      qed
    next
      case False
      then show ?thesis sorry
    qed
next
  case (iIfTrue s b c c1 stack x a a b y c2)
  then show ?case sorry
next
  case (iIfFalse s b c c2 stack x a a b y c1)
  then show ?case sorry
qed auto


lemma TCIS_to_trec1_no_branch_no_rest: "\<not>branches c \<Longrightarrow> \<turnstile>\<^bsub>\<diamondop>Rec\<^esub> c \<Longrightarrow> 

lemma upto_syn_correct_no_rest: " \<turnstile>\<^bsub>\<diamondop>GRec\<^esub> c \<Longrightarrow>
                        \<lbrakk>c\<rbrakk>\<rightarrow>TREC = (tc,rest) \<Longrightarrow> 
                        c' \<turnstile>Rec\<rightharpoonup>i (tc,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',None) \<Longrightarrow>
                       c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',None)"
proof (induction c arbitrary: tc rest s stack x s' stack' rule: TCIS_to_trec1.induct)
  case (1 b c1 c2)
  obtain tc1 rest1 tc2 rest2 
    where \<open>\<lbrakk>c1\<rbrakk>\<rightarrow>TREC = (tc1, rest1)\<close> \<open>\<lbrakk>c2\<rbrakk>\<rightarrow>TREC = (tc2, rest2)\<close>
    by fastforce
  hence \<open>\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2 \<rbrakk>\<rightarrow>TREC = (#IF b\<noteq>0 THEN tc1 ELSE tc2, rest1@rest2)\<close>
    by auto
  hence \<open>tc = #IF b\<noteq>0 THEN tc1 ELSE tc2\<close> 
    using "1.prems"(2) by auto
  hence \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN tc1 ELSE tc2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close>
    using "1.prems"(3) by auto
  then show ?case proof(cases "s b \<noteq> 0")
    case True
    from \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN tc1 ELSE tc2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> 
    have \<open>c' \<turnstile>Rec\<rightharpoonup>i (tc1, s, stack) \<Rightarrow>\<^bsup> x - 1 \<^esup> (s', stack', None)\<close>
      using True by force
    hence \<open>c' \<turnstile>Rec\<rightharpoonup>i (c1, s, stack) \<Rightarrow>\<^bsup> x - 1\<^esup> (s', stack', None)\<close>
      using "1.IH"(1) "1.prems"(1) \<open>\<lbrakk> c1 \<rbrakk>\<rightarrow>TREC = (tc1, rest1)\<close> grec_indentified.simps(2)
      by blast
    then show ?thesis 
      by (metis True
          \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN tc1 ELSE tc2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close>
          \<open>c' \<turnstile>Rec\<rightharpoonup>i (tc1, s, stack) \<Rightarrow>\<^bsup> x - 1 \<^esup> (s', stack', None)\<close> iIfTrue
          lri_deterministic)
  next
    case False
    from \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN tc1 ELSE tc2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close> 
    have \<open>c' \<turnstile>Rec\<rightharpoonup>i (tc2, s, stack) \<Rightarrow>\<^bsup> x - 1 \<^esup> (s', stack', None)\<close>
      using False by force
    hence \<open>c' \<turnstile>Rec\<rightharpoonup>i (c2, s, stack) \<Rightarrow>\<^bsup> x - 1\<^esup> (s', stack', None)\<close>
      using "1.IH"(2) "1.prems"(1) \<open>\<lbrakk> c1 \<rbrakk>\<rightarrow>TREC = (tc1, rest1)\<close>
        \<open>\<lbrakk> c2 \<rbrakk>\<rightarrow>TREC = (tc2, rest2)\<close> by auto
    then show ?thesis 
      by (metis False
          \<open>c' \<turnstile>Rec\<rightharpoonup>i (#IF b\<noteq>0 THEN tc1 ELSE tc2, s, stack) \<Rightarrow>\<^bsup> x \<^esup> (s', stack', None)\<close>
          \<open>c' \<turnstile>Rec\<rightharpoonup>i (tc2, s, stack) \<Rightarrow>\<^bsup> x - 1 \<^esup> (s', stack', None)\<close> iIfFalse
          lri_deterministic)
  qed
next
  case (2 c1 c2)
  then show ?case sorry
next
  case "3_1"
  then show ?case sorry
next
  case ("3_2" v va)
  then show ?case sorry
next
  case ("3_3" v va)
  then show ?case sorry
next
  case ("3_4" v)
  then show ?case sorry
next
  case ("3_5" v)
  then show ?case sorry
next
  case ("3_6" v)
  then show ?case sorry
qed


lemma upto_syn_correct_rest: "*GRec\<lbrakk>\<diamondop>GRec\<lbrakk> c \<rbrakk>\<rbrakk> \<Zsurj> n = (cn,rn) \<Longrightarrow>
                              \<lbrakk>cn\<rbrakk>\<rightarrow>TREC = (tcn,rest) \<Longrightarrow>
                        c' \<turnstile>Rec\<rightharpoonup>i (tcn,s,stack) \<Rightarrow>\<^bsup>x\<^esup> (s',stack',Some i) \<Longrightarrow> 
                       c' \<turnstile>Rec\<rightharpoonup>i (rest ! i,s',stack') \<Rightarrow>\<^bsup>y\<^esup> (s'',stack'',j) \<Longrightarrow>
                       c' \<turnstile>Rec\<rightharpoonup>i (c,s,stack) \<Rightarrow>\<^bsup>x + y\<^esup> (s'',stack'',None)"
  sorry

(* 2. Recursively cut the return points until there are no return points left and accumulate the subprograms in a list *)
function upto_grec_full :: "tscom_tagged \<Rightarrow>tscom_tagged list" ("\<rightarrow>TREC\<lbrace> _ \<rbrace>" 55)where
 "\<rightarrow>TREC\<lbrace> c \<rbrace>  = (let (csb,rest) = \<rightarrow>TREC\<lbrakk>c\<rbrakk> in 
      (case rest of [] \<Rightarrow> [csb] 
                   | sb#sbs \<Rightarrow> csb #  concat (map  upto_grec_full (rest))))"
  by auto

termination upto_grec_full using rest_size 
  by (metis "termination" in_measure wf_measure)


end