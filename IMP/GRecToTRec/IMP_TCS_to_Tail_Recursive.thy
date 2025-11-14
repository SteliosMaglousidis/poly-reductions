theory IMP_TCS_to_Tail_Recursive
  imports IMP_TCS_Intermediate
begin

unbundle tscom_tagged_syntax and no com'_syntax 

fun upto_rec_and_rest_syn :: "tscom_tagged \<Rightarrow> tscom_tagged * tscom_tagged list" ("UPTO-GREC\<lbrakk> _ \<rbrakk> " 55) where
   "UPTO-GREC\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2\<rbrakk> =
    (let (ut1,r1) = UPTO-GREC\<lbrakk>c1\<rbrakk> in 
      (let (ut2,r2) = UPTO-GREC\<lbrakk>c2\<rbrakk> in 
        (#IF b\<noteq>0 THEN ut1 ELSE ut2,r1@r2)))"
  |"UPTO-GREC\<lbrakk>c1 #;; c2\<rbrakk> = 
     (if stails_tagged c1 then 
       (let (ut1,r1) = UPTO-GREC\<lbrakk>c1\<rbrakk> in (ut1, if r1 = [] then [c2] else map (\<lambda>x. x #;; c2) r1)) 
      else 
       (let (ut2,r2) = UPTO-GREC\<lbrakk>c2\<rbrakk>  in
         (c1 #;; ut2, r2)))" 
  |"UPTO-GREC\<lbrakk>c\<rbrakk>  = (c,[])" 


declare upto_rec_and_rest_syn.elims[elim]

lemmas upto_rec_and_rest_syn.elims

lemma rest_size : "UPTO-GREC\<lbrakk>c\<rbrakk> = (sb,rest) \<Longrightarrow> rc \<in> set rest \<Longrightarrow> size rc < size c"
proof (induction c arbitrary: sb rest rc rule: upto_rec_and_rest_syn.induct)
  case (1 b c1 c2)
  obtain sb1 rest1 sb2 rest2 
    where "UPTO-GREC\<lbrakk>c1\<rbrakk> = (sb1, rest1)" "UPTO-GREC\<lbrakk>c2\<rbrakk> = (sb2, rest2)"
    by fastforce
  have "rest = rest1@rest2" using \<open>UPTO-GREC\<lbrakk>c1\<rbrakk>  = (sb1, rest1)\<close> \<open>UPTO-GREC\<lbrakk>c2\<rbrakk>  = (sb2, rest2)\<close>
      \<open>UPTO-GREC\<lbrakk>#IF b\<noteq>0 THEN c1 ELSE c2 \<rbrakk>  = (sb, rest)\<close> by simp
  hence \<open>rc \<in> set rest1 \<or> rc \<in> set rest2\<close> 
    using "1.prems"(2) by force
  then show ?case apply (cases "rc \<in> set rest1")
    apply auto 
    using "1.IH"(1) \<open>UPTO-GREC\<lbrakk>c1\<rbrakk> = (sb1, rest1)\<close> apply force
    by (simp add: "1.IH"(2) \<open>UPTO-GREC\<lbrakk>c1\<rbrakk> = (sb1, rest1)\<close> \<open>UPTO-GREC\<lbrakk>c2\<rbrakk>  = (sb2, rest2)\<close> less_Suc_eq
        trans_less_add2)
next
  case (2 c1 c2) 
  then show ?case proof(cases \<open>stails_tagged c1\<close>)
    case True
    obtain sb1 rest1 
    where "UPTO-GREC\<lbrakk>c1\<rbrakk>  = (sb1, rest1)" 
    by fastforce
    then show ?thesis proof(cases \<open>rest1 = []\<close>)
      case True
      have \<open>UPTO-GREC\<lbrakk>c1 #;; c2\<rbrakk> = (sb1, [c2])\<close>  
        using \<open>UPTO-GREC\<lbrakk>c1\<rbrakk> = (sb1, rest1)\<close> \<open>stails_tagged c1\<close> \<open>rest1 = []\<close> 
        by simp
      hence \<open>sb = sb1\<close> \<open>rest = [c2]\<close>  
        using "2.prems"(1) apply fastforce
        using "2.prems"(1) \<open>UPTO-GREC\<lbrakk>c1 #;; c2\<rbrakk>= (sb1, [c2])\<close> by fastforce
        hence \<open>rc = c2\<close> 
          using "2.prems"(2) by fastforce
      then show ?thesis 
        by auto
    next
      case False
      have \<open>UPTO-GREC\<lbrakk>c1 #;; c2\<rbrakk> = (sb1, map (\<lambda>x. x #;; c2) rest1)\<close>
        using \<open>UPTO-GREC\<lbrakk>c1\<rbrakk> = (sb1, rest1)\<close> \<open>stails_tagged c1\<close> \<open>rest1 \<noteq> []\<close>
        by simp
      hence \<open>sb = sb1\<close> \<open>rest = map (\<lambda>x. x #;; c2) rest1\<close>  
        using "2.prems"(1) apply fastforce
        using "2.prems"(1) \<open>UPTO-GREC\<lbrakk>c1 #;; c2\<rbrakk> = (sb1, map (\<lambda>x. x #;; c2) rest1)\<close>
        by force
      hence \<open>rc \<in> set (map (\<lambda>x. x #;; c2) rest1)\<close>
        using "2.prems"(2) by fastforce
      have \<open>\<forall>x. x \<in> set rest1 \<longrightarrow> size x \<le> size c1\<close>
        by (simp add: "2.IH"(1) True \<open>UPTO-GREC\<lbrakk> c1 \<rbrakk>= (sb1, rest1)\<close> order_le_less)
      hence \<open>\<forall>x. x \<in> set (map (\<lambda>x. x #;; c2) rest1) \<longrightarrow> size x \<le> size (c1 #;; c2)\<close>
        by auto
      then show ?thesis using \<open>rc \<in> set (map (\<lambda>x. x #;; c2) rest1)\<close> \<open>\<forall>x. x \<in> set (map (\<lambda>x. x #;; c2) rest1) \<longrightarrow> size x \<le> size (c1 #;; c2)\<close>
        using "2.IH"(1) True \<open>UPTO-GREC\<lbrakk> c1 \<rbrakk>  = (sb1, rest1)\<close> by force
    qed
  next
    case False
    obtain sb2 rest2 
      where "UPTO-GREC\<lbrakk>c2\<rbrakk> = (sb2, rest2)"
    by fastforce
    have \<open>UPTO-GREC\<lbrakk>c1 #;; c2\<rbrakk> = (c1 #;; sb2, rest2)\<close>
      using False \<open>UPTO-GREC\<lbrakk>c2\<rbrakk> = (sb2, rest2)\<close> by auto
    hence \<open>rest = rest2\<close>
      using "2.prems"(1) by auto
    hence \<open>rc \<in> set rest2\<close> using \<open>rc \<in> set rest\<close> by simp
    then show ?thesis 
      using "2.IH"(2) False \<open>UPTO-GREC\<lbrakk>c2\<rbrakk>= (sb2, rest2)\<close>
      by fastforce
  qed
qed auto

(* 2. Recursively cut the return points until there are no return points left and accumulate the subprograms in a list *)
function upto_grec_full :: "tscom_tagged \<Rightarrow>tscom_tagged list" ("UPTO-GREC\<lbrace> _ \<rbrace>" 55)where
 "UPTO-GREC\<lbrace> c \<rbrace>  = (let (csb,rest) = UPTO-GREC\<lbrakk>c\<rbrakk> in 
      (case rest of [] \<Rightarrow> [csb] 
                   | sb#sbs \<Rightarrow> csb #  concat (map  upto_grec_full (rest))))"
  by auto

termination upto_grec_full using rest_size 
  by (metis "termination" in_measure wf_measure)

(* 2. Assign a unique return point index its corresponding termination point*)

fun ret_point_count :: "tscom_tagged \<Rightarrow> nat" ("_ #Ret")where
   "(#IF b\<noteq>0 THEN c1 ELSE c2) #Ret = c1 #Ret + c2 #Ret" 
  |"(c1 #;; c2) #Ret = c2 #Ret" 
  |"#Some i\<rightharpoonup> SKIP #Ret = 1" 
  |"(#(Some i)\<rightharpoonup> x ::= a) #Ret = 1" 
  |"#Some i\<rightharpoonup> CALL c RETURN r #Ret = 1"
  |"#Some i\<rightharpoonup> TAIL #Ret = 1"
  |"#Some i\<rightharpoonup> PUSH v #Ret = 1"
  |"#Some i\<rightharpoonup> POP v #Ret = 1"
  |"_ #Ret = 0"

fun enum_ret_points_n :: "tscom_tagged \<Rightarrow> nat \<Rightarrow> tscom_tagged" ("_ \<diamondop>Ret _") where
   "(ct1 #;; ct2) \<diamondop>Ret i = ct1 #;; (ct2 \<diamondop>Ret i)" 
  |"(#IF b\<noteq>0 THEN ct1 ELSE ct2) \<diamondop>Ret i = (#IF b\<noteq>0 THEN (ct1 \<diamondop>Ret i) ELSE (ct2 \<diamondop>Ret (i + ct1 #Ret)))" 
  |"#Some j\<rightharpoonup> SKIP \<diamondop>Ret i = #Some i\<rightharpoonup> SKIP" 
  |"(#(Some j) \<rightharpoonup> x ::= a) \<diamondop>Ret i = #(Some i) \<rightharpoonup> x ::= a" 
  |"#Some j\<rightharpoonup> CALL c RETURN r \<diamondop>Ret i = #Some i\<rightharpoonup> CALL c RETURN r" 
  |"#Some j\<rightharpoonup> TAIL \<diamondop>Ret i = (#Some i\<rightharpoonup> TAIL)" 
  |"#Some j\<rightharpoonup> PUSH v \<diamondop>Ret i = (#Some i\<rightharpoonup> PUSH v)" 
  |"#Some j\<rightharpoonup> POP v \<diamondop>Ret i = (#Some i\<rightharpoonup> POP v)" 
  |"c \<diamondop>Ret i = c"

fun enum_ret_points_list_n :: "tscom_tagged list \<Rightarrow> nat \<Rightarrow> tscom_tagged list" ("_ \<diamondop>Ret* _") where
   "[] \<diamondop>Ret* n = []" 
  |"(c#cs) \<diamondop>Ret* n = (c \<diamondop>Ret n) # (cs \<diamondop>Ret* (n + c #Ret))" 


(* 3. Assign the return point to the program counter after a termination point and 
  push the return point index to the program counter stack in case of a recursive call *)


term "c1 ;; c2 ;; c3"

term "c1 ;; (c2 ;; c3)"

unbundle tscom_tagged_syntax and no com'_syntax and no rcom_tagged_syntax

definition "max_pc_value c \<equiv> (length (UPTO\<lbrace> c \<rbrace> \<diamondop>Ret* 0 ))"

fun add_stack_coms :: "tscom_tagged \<Rightarrow> vname \<Rightarrow> tscom_tagged" ("\<lblot>STACK _ PC _ \<rblot>")where 
 "add_stack_coms (ct1 #;; ct2) pc = (ct1 #;; add_stack_coms ct2 pc)" 
|"add_stack_coms (#IF b\<noteq>0 THEN ct1 ELSE ct2) pc =
  (#IF b\<noteq>0 THEN add_stack_coms ct1 pc ELSE add_stack_coms ct2 pc)" 
(*Recursive call with return point*)
|"add_stack_coms (#Some i\<rightharpoonup> TAIL) pc  = 
                            (#None \<rightharpoonup> pc ::= A (N i)) #;;
                            #None \<rightharpoonup> PUSH pc #;;
                            (#None \<rightharpoonup> pc ::= A (N 1)) #;; 
                            (#None \<rightharpoonup> TAIL)" 
(*Tail recursive call. Returns to a termination point*)
|"add_stack_coms (#None\<rightharpoonup> TAIL) pc = (#None\<rightharpoonup> TAIL)" 
(*Return points*)
|"add_stack_coms (#Some i\<rightharpoonup> SKIP) pc = 
                            (#None\<rightharpoonup> SKIP) #;;
                            (#None \<rightharpoonup> pc ::= A (N i)) #;;
                            (#None \<rightharpoonup> TAIL)"
|"add_stack_coms (#(Some i) \<rightharpoonup> x ::= a) pc = 
                            (#None\<rightharpoonup> x ::= a) #;;
                            (#None \<rightharpoonup> pc ::= A (N i)) #;;
                            (#None \<rightharpoonup> TAIL)"
|"add_stack_coms (#Some i\<rightharpoonup> CALL v RETURN r) pc = 
                            (#None\<rightharpoonup> CALL v RETURN r) #;;
                            (#None \<rightharpoonup> pc ::= A (N i)) #;;
                            (#None \<rightharpoonup> TAIL)"
(*Termination points*)
|"add_stack_coms c pc =   c #;;
                            #None \<rightharpoonup>POP pc #;; 
                            (#None \<rightharpoonup> TAIL)"

(*4. Initialize the program counter stack with the program exit value.
     Initialize program counter with program start value. *)


unbundle tscom_syntax and no com'_syntax and no rcom_syntax

definition "call_start c pc \<equiv> (IF pc = 0 THEN (
                                        (pc ::= A (N (max_pc_value c + 1))) ;;
                                        PUSH pc ;;
                                        (pc ::= A (N 1)) 
                                  )ELSE tsSKIP)"



(*5. Reset pc to 0 *)
definition "reset_pc pc \<equiv> pc ::= A (N 0)"

(* Give more structure and prove some modules that make sense*)
(* Include unique variables in the original program *)

definition "grec_to_trec c pc \<equiv> (
   let return_point_branches = (\<lambda>x. upto_rec_and_rest_syn_bfs #\<lbrakk> x \<rbrakk>) in
    let branches_to_tscom = (\<lambda>x. (map untag_tscom (map (\<lambda>x. add_stack_coms x pc) x))) in
  (call_start #\<lbrakk> c \<rbrakk> pc ) ;;
  (switch_basic pc (branches_to_tscom (return_point_branches (c))) ;;
   reset_pc pc))"

theorem grec_to_tirec_correct_gen:
(* Generalize pc.*)
  assumes "pc \<notin> set (vars c)"
  shows "c \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack') \<Longrightarrow> 
       \<exists>t . ((grec_to_trec c pc) \<turnstile> (grec_to_trec c pc,s,stack) \<Rightarrow>\<^bsup> t \<^esup> (s',stack))"
proof(induction c arbitrary: s stack t s' stack')
  oops
(* do each step seperately, prove its specification *)

end