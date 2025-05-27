theory IMP_GRec
  imports IMP_Calls "HOL-Library.Tree"
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
         rRec ("RECURSE")
end
unbundle no com'_syntax

type_synonym rstate = "val list"

inductive
  rbig_step_t :: "rcom \<Rightarrow> rcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile>\<^sub>R _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
rSkip: "c \<turnstile>\<^sub>R (rSKIP,s) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> s" |
rAssign: "c \<turnstile>\<^sub>R (x ::= a,s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> s(x := aval a s)" |
rSeq: "\<lbrakk>c \<turnstile>\<^sub>R (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> s2; c \<turnstile>\<^sub>R (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> s3 ; z=x+y \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>R (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> s3" |
rIfTrue: "\<lbrakk> s b \<noteq> 0;  c \<turnstile>\<^sub>R (c1,s) \<Rightarrow>\<^bsup>x \<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> t" |
rIfFalse: "\<lbrakk> s b = 0; c \<turnstile>\<^sub>R (c2,s) \<Rightarrow>\<^bsup>x \<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> c \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> t" |
rCall: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>R (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r))" |
\<comment> \<open>New rule\<close>
rRec: "c \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> c \<turnstile>\<^sub>R (RECURSE,s) \<Rightarrow>\<^bsup>5 + z \<^esup> t"
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

fun tree_cf :: "rcom \<Rightarrow> rcom" where 
"tree_cf (rSKIP) = rSKIP" |
"tree_cf (x ::= a)  = (x ::= a)" |
"tree_cf ((IF b\<noteq>0 THEN c1 ELSE c2) ;; c3) = (IF b\<noteq>0 THEN tree_cf (c1 ;; c3) ELSE tree_cf (c2 ;; c3))" |
"tree_cf (c1 ;; c2) = tree_cf c1 ;; tree_cf c2" |
"tree_cf (IF b\<noteq>0 THEN c1 ELSE c2)  = (IF b\<noteq>0 THEN tree_cf c1 ELSE tree_cf c2)" |
"tree_cf c = c"

lemma tree_sound: "d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile>\<^sub>R (tree_cf c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s z t rule: tree_cf.induct) fastforce+

lemma tree_complete: "d \<turnstile>\<^sub>R (tree_cf c,s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s z t rule: tree_cf.induct) fastforce+

lemma tree_comp: "d \<turnstile>\<^sub>R (tree_cf c,s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<longleftrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t" using tree_sound tree_complete by metis


abbreviation if_equals_var ("(IF _/=_ ON _ THEN _/ ELSE _ )"  [0, 0, 0, 0, 61] 61) where
"if_equals_var x v b c1 c2  \<equiv> ((b ::= Sub (V x) (V v)) ;; IF b\<noteq>0 THEN c1 ELSE c2)"

abbreviation if_equals ("(IF _/=_ ON _ THEN _/ ELSE _ )"  [0, 0, 0, 0, 61] 61) where
"if_equals x v b c1 c2  \<equiv> ((b ::= Sub (V x) (N v)) ;; (IF b\<noteq>0 THEN c1 ELSE c2))"

abbreviation push_all where
"push_all \<equiv> rSKIP"

abbreviation pop_all where
"pop_all \<equiv> rSKIP;;rSKIP"


term "fibonacci \<equiv> (IF n=0 ON b THEN (r ::= A (N 0)) ELSE 
                     (IF n=1 ON b THEN (r ::= A (N 1)) ELSE 
                          (n ::= Sub (V n) (N 1)) ;;
                            CALL fib RETURN r;;
                            (r1 ::= A (V r));;
                            (n ::= Sub (V n) (N 1)) ;;
                            CALL fib RETURN r;;
                            (r2 ::= A (V r));;
                            (r ::= Plus (V r1) (V r2))))"

term "fibonacci_tail \<equiv> ((IF n=0 ON b THEN r ::= A (N 0) ;; pc ::= Plus (V pc) (N 1) ELSE 
                     (IF n=1 ON b THEN r ::= A (N 1) ;; pc ::= Plus (V pc) (N 1) ELSE 
                          (n ::= Sub (V n) (N 1)) ;;
                            IF pc=1 ON bc THEN 
                            (pop_all ;;
                             r1 ::= A (V r) ;;
                             n ::= Sub (V n) (N 1) ;;
                             IF pc=2 ON bc THEN 
                             (pop_all ;;
                              pc ::= A(N 0);;
                              r2 ::= A (V r);;
                              r ::= Plus (V r1) (V r2)
                              ;; pc ::= Plus (V pc) (N 1)
                             )ELSE push_all ;; CALL fib RETURN r
                            )ELSE push_all ;; CALL fib RETURN r)))"

(* Looks as if there is no need to eliminate tail calls *)
term "ackermann \<equiv> (IF m=0 ON b THEN (r ::= Plus (V n) (N 1)) ELSE 
                     (IF n=0 ON b THEN 
                                    m ::= Sub (V m) (N 1) ;;
                                    n ::= Plus (V n) (N 1) ;;
                                    CALL ACK RETURN r 
                                  ELSE(
                                    n ::= Sub (V n) (N 1) ;;
                                    CALL ACK RETURN r ;;
                                    r1 ::= A (V r) ;;
                                    m ::= Sub (V m) (N 1) ;;
                                    n ::= A (V r1) ;;
                                    CALL ACK RETURN r )))"

term "ackermann_trec \<equiv> (IF m=0 ON b THEN (r ::= Plus (V n) (N 1)) ;; pc ::= Plus (V pc) (N 1) ELSE 
                         (IF n=0 ON b THEN 
                            m ::= Sub (V m) (N 1) ;;
                            n ::= A (N 1) ;;
                            CALL ACK RETURN r 
                          ELSE(
                            n ::= Sub (V n) (N 1) ;;
                            IF pc=1 ON bc THEN 
                              pop_all ;;
                              r1 ::= A (V r) ;;
                              m ::= Sub (V m) (N 1) ;;
                              n ::= A (V r1) ;; 
                              CALL ACK RETURN r
                            ELSE (
                            push_all ;; 
                            CALL ACK RETURN r))))"

 
section \<open>Semantics for small-step-ish reasoning (loops)\<close>
text \<open>Big-step semantics that just returns true for Tail\<close>
inductive
  rec_step :: "(rcom \<times> state) \<Rightarrow> nat \<Rightarrow> (state \<times> bool) \<Rightarrow> bool" ("\<turnstile>\<^sub>R_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
where
Skip: "\<turnstile>\<^sub>R (rSKIP,s) \<Rightarrow>\<^bsup>Suc (0::nat) \<^esup> (s,False)" |
Assign: "\<turnstile>\<^sub>R(x ::= a,s) \<Rightarrow>\<^bsup>Suc (Suc 0) \<^esup> (s(x := aval a s),False)" |
Seq: "\<lbrakk>\<turnstile>\<^sub>R (c1,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2, False); \<turnstile>\<^sub>R (c2,s2) \<Rightarrow>\<^bsup>y \<^esup> (s3,CONT) ; z=x+y \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup> (s3,CONT)" |
IfTrue: "\<lbrakk> s b \<noteq> 0; \<turnstile>\<^sub>R (c1,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1 \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
IfFalse: "\<lbrakk> s b = 0; \<turnstile>\<^sub>R (c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT); y=x+1  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup>y \<^esup> (t,CONT)" |
Call: "(C,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> \<turnstile>\<^sub>R (CALL C RETURN r,s) \<Rightarrow>\<^bsup>z \<^esup> (s(r:=t r),False)" |
Rec: "\<turnstile>\<^sub>R (RECURSE,s) \<Rightarrow>\<^bsup>5 \<^esup> (s,True)"

code_pred rec_step .

declare rec_step.intros[intro]

lemmas rec_step_induct = rec_step.induct[split_format(complete)]

inductive_cases recSkip_tE[elim!]: "\<turnstile>\<^sub>R (rSKIP,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"
inductive_cases recAssign_tE[elim!]: "\<turnstile>\<^sub>R (x ::= a,s) \<Rightarrow>\<^bsup>p \<^esup> (t,b)"
inductive_cases recSeq_tE[elim!]: "\<turnstile>\<^sub>R (c1;;c2,s1) \<Rightarrow>\<^bsup>p \<^esup> (s3,b)"
inductive_cases recIf_tE[elim!]: "\<turnstile>\<^sub>R (IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup>x \<^esup> (t,CONT)"
inductive_cases recCall_tE[elim!]: "\<turnstile>\<^sub>R (CALL C RETURN v,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b)"

inductive_cases recRec_tE[elim]: "\<turnstile>\<^sub>R (RECURSE,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b)"

text \<open>Closure of tails\<close>
inductive
 rec_steps :: "rcom \<Rightarrow> rcom \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" ("_ \<turnstile>\<^sub>R''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55) for d
where
rFalse: "\<turnstile>\<^sub>R(c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,False) \<Longrightarrow> d \<turnstile>\<^sub>R'(c,s)\<Rightarrow>\<^bsup>z \<^esup> t" |
rTrue: "\<turnstile>\<^sub>R(c,s1) \<Rightarrow>\<^bsup>x \<^esup> (s2,True) \<Longrightarrow> d \<turnstile>\<^sub>R'(d,s2)\<Rightarrow>\<^bsup>y \<^esup> s3 \<Longrightarrow> d \<turnstile>\<^sub>R'(c,s1)\<Rightarrow>\<^bsup>x+y \<^esup> s3"

code_pred rec_steps .

declare rec_steps.intros[intro]
declare rec_steps.cases[elim]

lemmas rec_steps_induct = rec_steps.induct[split_format(complete)]

lemma no_recs_no_step: "\<turnstile>\<^sub>R(c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b) \<Longrightarrow> \<not>recs c \<Longrightarrow> \<not>b"
  by (induction c s z t b rule: rec_step_induct) auto

lemma no_recs_sem: "\<turnstile>\<^sub>R(c,s) \<Rightarrow>\<^bsup>z \<^esup> (t,b) \<Longrightarrow> \<not>recs c \<Longrightarrow> d \<turnstile>\<^sub>R (c,s)\<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c s z t b rule: rec_step_induct) auto

lemma small_sound: "d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> invar c \<Longrightarrow> invar d \<Longrightarrow> d \<turnstile>\<^sub>R' (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
proof (induction d c s z t rule: rbig_step_t_induct)
  case (rSeq c c1 s1 x s2 c2 y s3 z)
  hence "c \<turnstile>\<^sub>R'(c1, s1) \<Rightarrow>\<^bsup>x\<^esup>  s2" "c \<turnstile>\<^sub>R'(c2, s2) \<Rightarrow>\<^bsup>y\<^esup>  s3" by auto
  from this rSeq show ?case apply (cases) apply auto
    subgoal
      by (smt (verit) ab_semigroup_add_class.add_ac(1) rec_step.Seq rec_steps.simps)
    subgoal
      by (metis no_recs_no_step)
    done
next
  case (rIfTrue s b c c1 x t y c2)
  hence "c \<turnstile>\<^sub>R'(c1, s) \<Rightarrow>\<^bsup>x\<^esup>  t" by auto
  from this rIfTrue show ?case apply (cases) apply auto apply force
    by (metis Suc_eq_plus1 local.rIfTrue(1) plus_nat.simps(2) rec_step.IfTrue rec_steps.intros(2))
next
  case (rIfFalse s b c c2 x t y c1)
  hence "c \<turnstile>\<^sub>R'(c2, s) \<Rightarrow>\<^bsup>x\<^esup>  t" by auto
  from this rIfFalse show ?case apply (cases) apply auto apply force
    by (metis Suc_eq_plus1 add_Suc rTrue rec_step.IfFalse)
next
  case (rRec c s z t)
  hence " c \<turnstile>\<^sub>R'(c, s) \<Rightarrow>\<^bsup>z\<^esup>  t" by simp
  moreover have "\<turnstile>\<^sub>R(RECURSE,s) \<Rightarrow>\<^bsup>5 \<^esup> (s,True)"
    by (metis Rec)
  ultimately show ?case by auto
qed auto

lemma small_complete: "d \<turnstile>\<^sub>R' (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> invar c \<Longrightarrow> invar d \<Longrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
proof (induction c s z t rule: rec_steps_induct)
  case (rFalse c s z t)
  then show ?case
    by (induction c s z t False rule: rec_step_induct) auto
next
  case (rTrue c s1 x s2 y s3)
  then show ?case
  proof (induction c s1 x s2 True arbitrary:  rule: rec_step_induct)
    case (Seq c1 s1 x s2 c2 y s3 z)
    then show ?case using no_recs_sem apply auto
      using ab_semigroup_add_class.add_ac(1) by blast
  qed auto
qed




unbundle no rcom_syntax and com'_syntax

lemma while'_unrolling:
  assumes "s b \<noteq> 0"
  shows "(c;;WHILE b\<noteq>0 DO c,s)\<Rightarrow>'\<^bsup>z\<^esup> t = (WHILE b\<noteq>0 DO c,s)\<Rightarrow>'\<^bsup>1+z\<^esup> t"
  using assms by auto

lemma rnoninterference:
  "\<lbrakk>c'\<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>x \<^esup> t; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>\<^sub>R (c,s(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> t(v:=y)"
proof (induction c' c s x t rule: rbig_step_t_induct)
  case (rAssign c x a s)
  hence " s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  thus ?case using rbig_step_t.rAssign[of c x a "s(v:=y)"] by argo
next
  case (rCall C s z t c r)
  hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
  from rCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
  show ?case using rbig_step_t.rCall[OF Call, of c r] state by argo
qed (auto | force)+


lemma noninterference':
  "\<lbrakk>\<turnstile>\<^sub>R(c,s) \<Rightarrow>\<^bsup>x \<^esup> (t,b); set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>R(c,s(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> (t(v:=y),b)"
proof (induction c s x t b rule: rec_step_induct)
  case (Assign x a s)
  hence "s(v := y, x := aval a (s(v := y))) = s(x := aval a s, v := y)" by force
  then show ?case using rec_step.Assign[of x a "s(v:=y)"] by argo
next
  case (Call C s z t r)
   hence Call: "(C, s(v := y)) \<Rightarrow>\<^bsup>z \<^esup> t(v := y)" using fresh_var_changed by fastforce
   from rCall have state: " s(v := y, r := (t(v := y)) r) = s(r := t r, v := y)" by auto
   show ?case using rbig_step_t.rCall[OF Call, of c r] state
     by (metis local.Call rec_step.Call)
qed auto

lemma rnoninterference':
  "\<lbrakk>c'\<turnstile>\<^sub>R'(c,s) \<Rightarrow>\<^bsup>x \<^esup> t; set (vars c) \<subseteq> S; set (vars c') \<subseteq> S; v \<notin> S \<rbrakk> \<Longrightarrow> c'\<turnstile>\<^sub>R'(c,s(v:=y)) \<Rightarrow>\<^bsup>x \<^esup> t(v:=y)"
proof (induction c s x t rule: rec_steps_induct)
  case (rFalse c s z t)
  then show ?case
    using noninterference' by blast
next
  case (rTrue c s1 x s2 y s3)
  then show ?case
    by (meson noninterference' rec_steps.rTrue)
qed

lemma rdeterministic:
  "d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t \<Longrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z' \<^esup> t' \<Longrightarrow> z = z' \<and> t = t'"
proof  (induction arbitrary: t' z' rule: rbig_step_t_induct)
  case (rIfTrue s b c c1 x t y c2)
  then show ?case 
    by fastforce
next
  case (rIfFalse s b c c2 x t y c1)
  then show ?case 
    by (metis add.commute less_numeral_extra(3) plus_1_eq_Suc rIf_tE)
next
  case (rCall C s z t c r)
  then show ?case
    using bigstep_det by blast
qed blast+


end