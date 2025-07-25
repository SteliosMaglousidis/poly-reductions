theory IMP_GRec
  imports IMP.IMP_Calls "HOL-Library.Tree" IMP.Com
begin

unbundle no com_syntax and com'_syntax
declare [[syntax_ambiguity_warning=false]]

datatype
  rcom = rSKIP
      | rAssign vname aexp
      | rSeq    rcom  rcom
      | rIf     vname rcom rcom
      | rCall   com vname
      | rRec  

open_bundle rcom_syntax begin
notation rAssign ("_ ::= _" [1000, 61] 61) and
         rSeq ("_;;/ _"  [60, 61] 60) and
         rIf ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         rCall ("CALL _ RETURN _") and
(* Add return register or add it to the semantics*)
         rRec ("RECURSE") 
end

unbundle no com'_syntax

instantiation rcom :: order_bot
begin

fun less_eq_rcom :: "rcom \<Rightarrow> rcom \<Rightarrow> bool" where
  "less_eq_rcom (rAssign v1 e1) (rAssign v2 e2) \<longleftrightarrow> v1 \<le> v2 \<and> e1 \<le> e2"
| "less_eq_rcom (rSeq c1 c2) (rSeq c3 c4) \<longleftrightarrow> less_eq_rcom c1 c3 \<and> less_eq_rcom c2 c4"
| "less_eq_rcom (rIf v1 c1 c2) (rIf v2 c3 c4) \<longleftrightarrow> v1 \<le> v2 \<and> less_eq_rcom c1 c3 \<and> less_eq_rcom c2 c4"
| "less_eq_rcom (rCall c1 r1) (rCall c2 r2) \<longleftrightarrow> r1 \<le> r2 \<and> c1 \<le> c2"
| "less_eq_rcom (rCall c1 r1) (RECURSE) \<longleftrightarrow> True"
| "less_eq_rcom (RECURSE) (rCall c2 r2) \<longleftrightarrow> False"
| "less_eq_rcom (RECURSE) (RECURSE) \<longleftrightarrow> True"
| "less_eq_rcom rSKIP _ \<longleftrightarrow> True"
| "less_eq_rcom _ rSKIP \<longleftrightarrow> False"
| "less_eq_rcom (rAssign _ _) _ \<longleftrightarrow> True"
| "less_eq_rcom _ (rAssign _ _) \<longleftrightarrow> False"
| "less_eq_rcom (rSeq _ _) _ \<longleftrightarrow> True"
| "less_eq_rcom _ (rSeq _ _) \<longleftrightarrow> False"
| "less_eq_rcom (rIf _ _ _) _ \<longleftrightarrow> True"
| "less_eq_rcom _ (rIf _ _ _) \<longleftrightarrow> False"

definition less_rcom :: "rcom \<Rightarrow> rcom \<Rightarrow> bool" where
  "less_rcom c1 c2 = (c1 \<le> c2 \<and> \<not> c2 \<le> c1)"

definition bot_rcom :: "rcom" where
  "bot_rcom = rSKIP"

instance
proof(standard, goal_cases)
  case 1 show ?case by (simp add: less_rcom_def)
next
  case (2 x) show ?case by(induction x; simp)
next
  case (3 x y z) thus ?case
    by(induction x z arbitrary: y rule: less_eq_rcom.induct; auto; force elim: less_eq_rcom.elims)
next
  case (4 x y) thus ?case
    by(induction x y rule: less_eq_rcom.induct; force elim: less_eq_rcom.elims)
next
  case 5 show ?case
    unfolding bot_rcom_def by simp
qed
end

type_synonym rstate = "val list"

inductive
  rbig_step_t :: "rcom \<Rightarrow> rcom \<times> state \<times> vname \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile>\<^sub>R _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
rSkip: "c \<turnstile>\<^sub>R (rSKIP,s,ret) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> s" |
rAssign: "c \<turnstile>\<^sub>R (x ::= a,s,ret) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> s(x := aval a s)" |
rSeq: "\<lbrakk>c \<turnstile>\<^sub>R (c1,s1,ret) \<Rightarrow>\<^bsup>x \<^esup> s2 ; c \<turnstile>\<^sub>R (c2,s2,ret) \<Rightarrow>\<^bsup>y \<^esup> s3 ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>R (c1;;c2, s1,ret) \<Rightarrow>\<^bsup>z \<^esup> s3" |
rIfTrue: "\<lbrakk> s b \<noteq> 0;  c \<turnstile>\<^sub>R (c1,s,ret) \<Rightarrow>\<^bsup>x \<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>y \<^esup> t" |
rIfFalse: "\<lbrakk> s b = 0; c \<turnstile>\<^sub>R (c2,s,ret) \<Rightarrow>\<^bsup>x \<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s, ret) \<Rightarrow>\<^bsup>y \<^esup> t" |
rCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>R (CALL C RETURN r,s,ret) \<Rightarrow>\<^bsup>z \<^esup> s(r:=t r)" |
\<comment> \<open>New rule\<close>
rRec: "c \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>R (RECURSE,s,ret) \<Rightarrow>\<^bsup>5 + z \<^esup> (s(ret:=t ret))"
bundle rbig_step_syntax
begin
notation rbig_step_t ("_ \<turnstile>\<^sub>R _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

code_pred rbig_step_t .

declare rbig_step_t.intros[intro]

lemmas rbig_step_t_induct = rbig_step_t.induct[split_format(complete)]

inductive_cases rSkip_tE[elim!]: "c \<turnstile>\<^sub>R (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases rAssign_tE[elim!]: "c \<turnstile>\<^sub>R (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> t"
inductive_cases rSeq_tE[elim!]: "c \<turnstile>\<^sub>R (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> s3"
inductive_cases rIf_tE[elim!]: "c \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> t"
inductive_cases rCall_tE[elim!]: "c \<turnstile>\<^sub>R (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> t"
inductive_cases rRec_tE[elim]: "c \<turnstile>\<^sub>R (RECURSE,s) \<Rightarrow>\<^bsup>x \<^esup> t"

instantiation rcom :: vars
begin

fun vars_rcom :: "rcom \<Rightarrow> vname list" where
"vars_rcom (x ::= a)  = x # vars a" |
"vars_rcom (c\<^sub>1;;c\<^sub>2) = vars_rcom c\<^sub>1 @ vars_rcom c\<^sub>2" |
"vars_rcom (IF b\<noteq>0 THEN c1 ELSE c2) = b # vars_rcom c1 @ vars_rcom c2" |
"vars_rcom (CALL c RETURN r) = r#vars c" |
"vars_rcom _ = []"

instance ..

end

fun recs :: "rcom \<Rightarrow> bool" where
  "recs RECURSE \<longleftrightarrow> True" |
  "recs (c1;;c2) \<longleftrightarrow> recs c1 \<or> recs c2" |
  "recs (IF b\<noteq>0 THEN c1 ELSE c2) \<longleftrightarrow> recs c1 \<or> recs c2" |
  "recs _ \<longleftrightarrow> False"

fun invar :: "rcom \<Rightarrow> bool" where
  "invar (c\<^sub>1;;c\<^sub>2) \<longleftrightarrow> \<not>recs c\<^sub>1 \<and> invar c\<^sub>2" |
  "invar (IF b\<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> invar c\<^sub>1 \<and> invar c\<^sub>2" |
  "invar _ \<longleftrightarrow> True"

lemma no_recs_invar[simp]: "\<not>recs c \<Longrightarrow> invar c"
  by (induction c) auto

fun call_count :: "rcom \<Rightarrow> nat" where
"call_count ((IF b\<noteq>0 THEN c1 ELSE c2)) = call_count c1 + call_count c2" |
"call_count (c1 ;; c2) =  call_count c1 + call_count c2" |
"call_count (CALL C RETURN r') = 1" |
"call_count _ = 0"

abbreviation if_equals_var ("(IF _/=_ ON _ THEN _/ ELSE _ )"  [0, 0, 0, 0, 61] 61) where
"if_equals_var x v b c1 c2  \<equiv> ((b ::= Sub (V x) (V v)) ;; IF b\<noteq>0 THEN c1 ELSE c2)"

abbreviation if_equals ("(IF _/=_ ON _ THEN _/ ELSE _ )"  [0, 0, 0, 0, 61] 61) where
"if_equals x v b c1 c2  \<equiv> ((b ::= Sub (V x) (N v)) ;; (IF b\<noteq>0 THEN c1 ELSE c2))"

(* Looks as if there is no need to eliminate tail calls *)
term "ackermann \<equiv> (IF m=0 ON b THEN (ret ::= Plus (V n) (N 1)) ELSE 
                     (IF n=0 ON b THEN 
                                    m ::= Sub (V m) (N 1) ;;
                                    n ::= Plus (V n) (N 1) ;;
                                    RECURSE
                                  ELSE(
                                    n ::= Sub (V n) (N 1) ;;
                                    RECURSE ;;
                                    r1 ::= A (V ret) ;;
                                    m ::= Sub (V m) (N 1) ;;
                                    n ::= A (V r1) ;;
                                    RECURSE)))"

term "ackermann_trec \<equiv> (IF pc=0 ON b THEN (
                            (IF m=0 ON b THEN (
                                    r ::= Plus (V n) (N 1)) ;;
                                    pop_all_vars ;; 
                                    pop_pc ELSE 
                            (IF n=0 ON b THEN ( 
                                    m ::= Sub (V m) (N 1) ;;
                                    n ::= Plus (V n) (N 1) ;;
                            push_all_vars ;;
                            push_pc_1 ;;
                            pc0;;
                            RECURSE)
                            ELSE 
                            (n ::= Sub (V n) (N 1) ;;
                            push_all_vars ;;
                            push_pc_2 ;;
                            pc0;;
                            RECURSE)))) 
                   ELSE (IF pc=1 ON b THEN (
                            pop_all_vars ;; 
                            pop_pc) 
                   ELSE (IF pc=2 ON b THEN (
                            r1 ::= A (V r) ;;
                            m ::= Sub (V m) (N 1) ;;
                            n ::= A (V r1) ;;
                            push_all_vars ;;
                            push_pc_3 ;;
                            pc0 ;;
                            RECURSE)
                   ELSE (
                            pop_all_vars ;; 
                            pop_pc))))"

 
section \<open>Semantics for small-step-ish reasoning (loops)\<close>
text \<open>Big-step semantics that just returns true for Tail\<close>
inductive
  rec_step :: "(rcom \<times> state \<times> vname) \<Rightarrow> nat \<Rightarrow> (state \<times> bool) \<Rightarrow> bool" ("\<turnstile>\<^sub>R_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "\<turnstile>\<^sub>R (rSKIP,s,ret) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,False)" |
Assign: "\<turnstile>\<^sub>R(x ::= a,s,ret) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),False)" |
Seq: "\<lbrakk>\<turnstile>\<^sub>R (c1,s1,ret) \<Rightarrow>\<^bsup>x \<^esup> (s2,CONT1); \<turnstile>\<^sub>R (c2,s2,ret2) \<Rightarrow>\<^bsup>y \<^esup> (s3,CONT2) ; z=x+y \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R (c1;;c2,s1,ret1) \<Rightarrow>\<^bsup>z\<^esup> (s3,CONT1 \<or> CONT2)" |
IfTrue: "\<lbrakk> s b \<noteq> 0; \<turnstile>\<^sub>R (c1,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1 \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s, ret1) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
IfFalse: "\<lbrakk> s b = 0; \<turnstile>\<^sub>R (c2,s,ret) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s,ret1) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> \<turnstile>\<^sub>R (CALL C RETURN r,s,ret) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),False)" |
Rec: "\<turnstile>\<^sub>R (RECURSE,s,ret1) \<Rightarrow>\<^bsup>5 \<^esup> (s,True)"

code_pred rec_step .

declare rec_step.intros[intro]

lemmas rec_step_induct = rec_step.induct[split_format(complete)]

inductive_cases recSkip_tE[elim!]: "\<turnstile>\<^sub>R (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"
inductive_cases recAssign_tE[elim!]: "\<turnstile>\<^sub>R (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases recSeq_tE[elim!]: "\<turnstile>\<^sub>R (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases recIf_tE[elim!]: "\<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT)"
inductive_cases recCall_tE[elim!]: "\<turnstile>\<^sub>R (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> (t,ret)"
inductive_cases recRec_tE[elim]: "\<turnstile>\<^sub>R (RECURSE,s) \<Rightarrow>\<^bsup>x \<^esup> (t,ret)"

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

lemma no_recs_no_step: "\<turnstile>\<^sub>R(c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> (t,b) \<Longrightarrow> \<not>recs c \<Longrightarrow> \<not>b"
  by (induction c s ret z t b rule: rec_step_induct) auto

unbundle no rcom_syntax and com'_syntax

lemma rnoninterference:
  "\<lbrakk>c'\<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup>x \<^esup> t; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>\<^sub>R (c,s(v:=y),ret) \<Rightarrow>\<^bsup>x \<^esup> t(v:=y)"
proof (induction c' c s ret x t rule: rbig_step_t_induct)
  case (rAssign c x a s ret)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using rbig_step_t.rAssign[of c x a "s(v:=y)" ret] by argo
next
  case (rCall C s z t c r ret)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from rCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using rbig_step_t.rCall[OF Call, of c r] state by metis
next 
  case (rRec c s ret z t)
  then show ?case 
    by (smt (verit, ccfv_SIG) fun_upd_other fun_upd_same fun_upd_twist fun_upd_upd rbig_step_t.rRec)
qed auto

lemma rdeterministic:
  "d \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> z \<^esup> t \<Longrightarrow> d \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup> z' \<^esup> t' \<Longrightarrow> z = z' \<and> t = t'"
proof  (induction c s ret z t arbitrary: t' z' rule: rbig_step_t_induct)
  case (rIfTrue s b c c1 ret x t ret' y c2)
  then show ?case
    by fastforce
next
  case (rIfFalse s b c c2 ret x t y c1)
  from \<open>s b = 0\<close> \<open>c \<turnstile>\<^sub>R (rIf b c1 c2, s, ret) \<Rightarrow>\<^bsup>z'\<^esup>  t'\<close> obtain x' where
     \<open>c \<turnstile>\<^sub>R (c2, s, ret) \<Rightarrow>\<^bsup>x'\<^esup> t'\<close> and \<open>z' = x' + 1\<close>
    by auto
  hence \<open> x = x' \<and> t = t'\<close>
    using rIfFalse.IH by blast
  then show ?case 
    by (simp add: \<open>z' = x' + 1\<close> rIfFalse.hyps(3))
next
  case (rCall C s z t c r ret)
  then show ?case 
    using bigstep_det by blast
qed blast+

end