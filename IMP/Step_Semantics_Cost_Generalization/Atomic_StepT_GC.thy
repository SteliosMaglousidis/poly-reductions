
section "Small step semantics of IMP- "

subsection "Small step semantics definition"
theory Atomic_StepT_GC imports Big_StepT_Generalized_Cost_Final Main "../Com" "../Rel_Pow" begin

paragraph "Summary"

text\<open>Naive approach to generalize costs similar to big step. 
     One would probalby want to work with the transitive closure 
     rather than the predicate.\<close>

context BS_Generalized_Cost begin

inductive
  atomic_step_GC :: "com * state * nat \<Rightarrow> com * state * nat \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>G\<^sub>C\<^sub>A _" 55) 
  where

atomic_step: "(c, s, Suc n) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c, s, n)" |

Assign:  "(x ::= a, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (SKIP, s(x := aval a s), aexp_cost a s)" |

Seq1:    "(SKIP;;c\<^sub>2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c\<^sub>2,s, skip_cost s)" |
Seq2:    "(c\<^sub>1,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c\<^sub>1',s',m') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c\<^sub>1';;c\<^sub>2,s',m')" |

IfTrue:  "s b \<noteq> 0 \<Longrightarrow> (IF b \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c\<^sub>1,s,0)" |
IfFalse: "s b = 0 \<Longrightarrow> (IF b \<noteq>0  THEN c\<^sub>1 ELSE c\<^sub>2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c\<^sub>2,s,0)" |
                                                   
WhileTrue:   "s b \<noteq> 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A
            (c ;; WHILE b \<noteq>0 DO c,s,0)" |
WhileFalse:   "s b = 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A
            (SKIP,s,0)"

subsection "Transitive Closure"
abbreviation
  atomic_step_GC_pow :: "com * state * nat \<Rightarrow> nat \<Rightarrow> com * state * nat \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>_\<^esup> _" 55)
  where "x \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> y == (rel_pow atomic_step_GC t) x  y"
end

bundle small_step_GC_atomic_syntax
begin
notation BS_Generalized_Cost.atomic_step_GC (infix "\<rightarrow>" 55) and
         BS_Generalized_Cost.atomic_step_GC_pow ("_ \<rightarrow>\<^bsup>_\<^esup> _" 55)
end

bundle no_small_step_syntax
begin
no_notation BS_Generalized_Cost.atomic_step_GC (infix "\<rightarrow>" 55) and
         BS_Generalized_Cost.atomic_step_GC_pow ("_ \<rightarrow>\<^bsup>_\<^esup> _" 55)
end


context BS_Generalized_Cost begin

subsection\<open>Executability\<close>

(*
code_pred small_step .

experiment begin
values "{(c',map t [''x'',''y'',''z''], n) |c' t n.
   ((''x'' ::= A (V ''z'');; ''y'' ::=A ( V ''x''),
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>\<^bsup>n\<^esup> (c',t))}"
end

*)
subsection\<open>Proof infrastructure\<close>

subsubsection\<open>Induction rules\<close>

text\<open>The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form \<open>a \<rightarrow> b \<Longrightarrow> \<dots>\<close> where \<open>a\<close> and \<open>b\<close> are
not already pairs \<open>(DUMMY,DUMMY)\<close>. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
\<open>\<rightarrow>\<close> into pairs:\<close>
lemmas atomic_step_GC_induct = atomic_step_GC.induct[split_format(complete), OF BS_Generalized_Cost_axioms, consumes 1]


subsubsection\<open>Proof automation\<close>

declare atomic_step_GC.intros[simp,intro]


text\<open>Rule inversion:\<close>

inductive_cases AtomicStepE[elim!]: "(c, s, Suc n) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A ct"
inductive_cases SkipE[elim!]: "(SKIP,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A ct"
inductive_cases AssignE[elim!]: "(x::=a,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A ct"
inductive_cases SeqE[elim]: "(c1;;c2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A ct"
inductive_cases IfE[elim!]: "(IF b\<noteq>0 THEN c1 ELSE c2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A ct"
inductive_cases WhileE[elim]: "(WHILE b\<noteq>0 DO c, s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A ct"

text\<open>A simple property:\<close>

lemma atomic_ex_com: "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs' \<Longrightarrow> (snd (snd cs)) = Suc (snd (snd cs')) \<Longrightarrow> fst cs = fst cs'"
  by (induction rule: atomic_step_GC.induct) auto

lemma atomic_ex_state: "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs' \<Longrightarrow> (snd (snd cs)) = Suc (snd (snd cs')) \<Longrightarrow> fst (snd cs) = fst (snd cs')"
  by (induction rule: atomic_step_GC.induct) auto

lemma atomic_ex_det: "(c,s,Suc n) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c',s',n) \<Longrightarrow> c = c' \<and> s = s'"
  using atomic_ex_com atomic_ex_state by force

lemma atomic_ex_t: "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs' \<Longrightarrow> (snd (snd cs)) = Suc m \<Longrightarrow> (snd (snd cs')) = m"
  by (induction rule: atomic_step_GC.induct) auto

lemma atomic_ex: "(c, s, n) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>n\<^esup> (c, s, 0)"
  by (induction n arbitrary: c s) auto

lemma Assing_ex: "(x ::= a, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>aexp_cost a s + 1\<^esup> (SKIP, s(x := aval a s), 0)"
  using atomic_ex by auto

lemma Skip_ex: "(SKIP;; c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>skip_costs s\<^esup> (c, s, 0)"
    using atomic_ex by auto


lemma deterministic:
  "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m') \<Longrightarrow> (c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'', s'', m'')  \<Longrightarrow> c' = c'' \<and> s' = s'' \<and> m' = m''"
proof(induction c s m c' s' m' arbitrary: c'' s'' m'' rule: atomic_step_GC_induct)
  case (1 c s n)
  then show ?case using atomic_ex_t atomic_ex_det 
    by (metis (mono_tags, opaque_lifting) split_pairs)
next
  case (4 c\<^sub>1 s m c\<^sub>1' s' m' c\<^sub>2)
  then show ?case using 4 proof (cases m')
    case 0
    then show ?thesis using 4 proof(cases m)
      case 0
      then show ?thesis using 4 by blast
    next
      case (Suc nat)
      from 4(1) \<open>m' = 0\<close> have "nat = 0" 
        by (metis "4.IH" Suc atomic_step)
      hence "(c\<^sub>1, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c\<^sub>1, s, 0)"
        by (simp add: Suc)
      hence \<open>c\<^sub>1' = c\<^sub>1 \<and> s' = s\<close> 
        by (simp add: "4.IH")
      then show ?thesis 
        by (smt (verit) "0" "4.IH" "4.prems" AtomicStepE Suc \<open>nat = 0\<close> com.inject(2) prod.inject)
    qed
  next
    case (Suc nat)
    then show ?thesis using 4 proof(cases m)
      case 0
      then show ?thesis 
        by (smt (verit) "4.IH" "4.hyps" "4.prems" Pair_inject less_numeral_extra(3) local.SeqE local.SkipE zero_less_Suc)
    next
      case (Suc nat)
      then show ?thesis 
        by (smt (verit) "4.IH" "4.prems" AtomicStepE Pair_inject atomic_step com.inject(2))
    qed
  qed
qed auto

lemma atomic_step_t_deterministic: "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> cs' \<Longrightarrow> cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction t arbitrary: cs)
  using deterministic apply auto
  using Small_StepT.deterministic by blast

subsection "Progress property"
text "every command costs time"
lemma atomic_step_progress: "(c, s, a) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> p \<^esup> t \<Longrightarrow> t \<noteq> (c, s, a)  \<Longrightarrow> p > 0"
  by (induction p) auto

subsection "Sequence properties"
declare rel_pow_intros[simp,intro]

text "sequence property"
lemma star_seq2': "(c1,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c1',s',m') \<Longrightarrow> (c1;;c2,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (c1';;c2,s',m')"
proof(induction t arbitrary: c1 c1' s s' m m')
  case (Suc t)
  then obtain c1'' s'' m''  where "(c1,s,m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c1'', s'',m'')" 
                         and "(c1'', s'', m'')  \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup>  (c1', s', m')" 
    by auto
  moreover then have "(c1'';;c2, s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (c1';;c2, s', m')" using Suc by simp
  ultimately show ?case 
    by blast
qed auto

lemma star_seq2: "(c1,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c1',s',0) \<Longrightarrow> (c1;;c2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (c1';;c2,s',0)"
  by (simp add: local.star_seq2')

text "sequence time is one plus sum of the sub-commands times"
lemma seq_comp:
  "\<lbrakk> (c1,s1,m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 \<^esup> (SKIP,s2,0); (c2,s2,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t2 \<^esup> (c3,s3,m3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 + t2 + skip_costs s2\<^esup> (c3,s3,m3)"
proof (induction t1 arbitrary: c1 s1 m1  c2 s2 t2 c3 s3 )
  case 0
  have "(c1;; c2, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c2,s2,skip_cost s2)"
    using "0.prems"(1) 
    by blast
  hence "(c1;; c2, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> skip_costs s2\<^esup> (c2,s2,0)"
    using atomic_ex by auto
  then show ?case 
    by (smt (verit) "0.prems"(2) add.commute add_Suc plus_1_eq_Suc plus_nat.add_0 rel_pow_sum)
next
  case (Suc t1)
  then show ?case using Suc by auto
qed


lemma atomic_step_cant_continue_after_reaching_SKIP_0: "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 \<^esup> (SKIP, s2, 0)
  \<Longrightarrow> (c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>  t2 \<^esup> (c3, s3, m3)
  \<Longrightarrow> t2 \<le> t1"
proof(rule ccontr)
  assume "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t1\<^esup> (SKIP, s2, 0)" "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t2\<^esup> (c3, s3, m3)" "\<not> t2 \<le> t1"
  then obtain t3 where "t2 = t1 + t3" "t3 > 0"
    by (metis less_imp_add_positive not_le)
  hence "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 + t3 \<^esup> (c3, s3, m3)" 
    using \<open>(c1, s1, m1)  \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t2 \<^esup> (c3, s3, m3)\<close> 
    by auto
  then obtain c4s4 where "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t1\<^esup> c4s4" "c4s4 \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t3\<^esup> (c3, s3, m3)" 
    using \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t2\<^esup>  (c3, s3, m3)\<close> rel_pow_sum_decomp[OF \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 + t3 \<^esup>  (c3, s3, m3)\<close>]
    by blast
  hence "c4s4 = (SKIP, s2, 0)"
    using atomic_step_t_deterministic \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t1\<^esup> (SKIP, s2, 0)\<close>
    by simp
  hence "t3 = 0" 
    using \<open>c4s4  \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t3\<^esup> (c3, s3, m3)\<close>
    by (cases t3) auto
  thus False using \<open>t3 > 0\<close> by simp
qed


lemma atomic_backtrack1:
"(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m') \<Longrightarrow> m = Suc m' \<or> m = 0"
  by (induction c s m c' s' m' rule: atomic_step_GC_induct) auto

lemma atomic_next1:
"(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m') \<Longrightarrow> (m' = 0 \<or> m = Suc m' \<or> m' = skip_cost s \<or> ( \<exists>a.  m' = aexp_cost a s))"
  by (induction c s m c' s' m'  rule: atomic_step_GC_induct) auto


lemma atomic_backtrack:
  assumes "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m') "
  shows " \<exists>c'' s'' m''. ((c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c'', s'', m'') \<and> (c'', s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m') \<and> (m'' = 0 \<or> m'' = Suc m'))"
proof-
  from \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close> obtain c'' s'' m'' where "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c'', s'', m'')" "(c'', s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m')"
    by (metis rel_pow_Suc_E surj_pair)
  hence "m'' = Suc m' \<or> m'' = 0"
    by (simp add: atomic_backtrack1)
  then show ?thesis 
    using \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c'', s'', m'')\<close> 
    by (metis \<open>(c'', s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c', s', m')\<close>)
qed

lemma atomic_next:
  assumes "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m') "
  shows " \<exists>c'' s'' m''. ((c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'', s'', m'') \<and> (c'', s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', m') \<and> (m'' = 0 \<or> m = Suc m'' \<or> m'' = skip_cost s \<or> ( \<exists>a.  m'' = aexp_cost a s)))"
proof-
  from \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close> obtain c'' s'' m'' where "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'', s'', m'')" "(c'', s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup>  (c', s', m')"
    by auto
  hence "(m'' = 0 \<or> m = Suc m'' \<or> m'' = skip_cost s \<or> ( \<exists>a.  m'' = aexp_cost a s))"
    by (simp add: atomic_next1)
  then show ?thesis 
    by (metis \<open>(c'', s'', m'') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', m')\<close> \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c'', s'', m'')\<close>)
qed

lemma atomic_prev: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', Suc m') \<Longrightarrow>
                    (c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')"
  by (induction t arbitrary:  m c s s' c' m') auto

corollary full_atomic_backtrack: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', m') \<Longrightarrow>
                    (c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t + m'\<^esup> (c', s', 0)"
  apply (induction m' arbitrary: c s m t c' s')
   apply auto
  by (metis add_Suc atomic_prev)

lemma atomic_step1: "(c, s, Suc m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m') \<Longrightarrow>
                    (c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>  t\<^esup> (c', s', m')"
proof (induction t arbitrary: m c s s' c' m')
  case 0
  have \<open>(c, s, Suc m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c, s, m)\<close>
    by simp
  then show ?case 
    by (metis "0" atomic_next local.deterministic)
next
  case (Suc t)
  have \<open>(c, s, Suc m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c, s, m)\<close>
    by simp
  hence \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close>
    by (metis Suc.prems atomic_next local.deterministic)
  then show ?case proof(cases m)
    case 0
    then show ?thesis 
      using \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close> by auto
  next
    case (Suc nat)
    have \<open>(c, s, Suc nat) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close>
      using Suc \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close> by auto
    hence \<open>(c, s, nat) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', m')\<close> 
      by (simp add: Suc.IH)
    then show ?thesis 
      by (simp add: \<open>(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s', m')\<close>)
  qed
qed

corollary atomic_lens: "(c, s, Suc m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', Suc m') \<Longrightarrow> 
                        (c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>  t\<^esup> (c', s', m')"
  by (meson atomic_prev local.atomic_step1)

lemma atomic_residual1: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> m \<ge> m' \<Longrightarrow> (c, s, m - m') \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', 0)"
  apply (induction m' arbitrary: c s m t c' s')
  apply auto
  by (smt (verit) Suc_le_D atomic_prev diff_Suc_Suc local.atomic_step1 not_less_eq_eq)

corollary atomic_simp: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m) \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', 0)"
  by (metis atomic_residual1 cancel_comm_monoid_add_class.diff_cancel nat_le_linear)

lemma deatomization1': "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> m \<ge> m'  \<Longrightarrow> t \<ge> m - m' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t - (m - m')\<^esup> (c', s', 0)"
proof (induction m arbitrary: c s t c' s' m')
  case 0
  then show ?case 
    by (auto simp add: atomic_simp)
next
  case (Suc m)
  then show ?case proof (cases "m' =Suc m")
    case True
    then show ?thesis using Suc by (auto simp add: atomic_simp)
  next
    case False
    have \<open>m' \<le> m\<close> 
      using False Suc.prems(2) by auto
    have \<open>m - m' \<le> t - 1\<close> 
      using Suc.prems(3) by auto
    have \<open>(c, s,  m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t - 1\<^esup> (c', s', m')\<close>
      by (metis BS_Generalized_Cost.atomic_step1 BS_Generalized_Cost.atomic_step_progress BS_Generalized_Cost_axioms False Pair_inject Suc.prems(1) Suc_pred')
    then show ?thesis 
      by (metis (full_types) Nat.add_diff_assoc Suc.IH \<open>m - m' \<le> t - 1\<close> \<open>m' \<le> m\<close> diff_diff_left plus_1_eq_Suc)
  qed
qed

lemma deatomization1'': "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> m \<ge> m' \<Longrightarrow> t \<le> m - m' \<Longrightarrow> (c, s, (m - m') - t) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> 0\<^esup> (c', s', 0)"
proof (induction t arbitrary: c s  c' s' m m')
  case 0
  then show ?case 
    by (auto simp add: atomic_simp)
next
  case (Suc t)
  then show ?case proof (cases "m' =Suc m")
    case True
    then show ?thesis using Suc by (auto simp add: atomic_simp)
  next
    case False
    have \<open>m' \<le> m\<close> 
      using False Suc.prems(2) by auto
    have \<open>t \<le> (m - 1)- m'\<close> 
      using Suc.prems(3) by auto
    have \<open>(c, s,  m - 1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', m')\<close>
      by (metis (no_types, lifting) BS_Generalized_Cost.atomic_step1 BS_Generalized_Cost_axioms Nat.le_diff_conv2 Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc_diff_le add_leE diff_Suc_1 plus_1_eq_Suc)
    then show ?thesis 
      by (smt (z3) Suc.IH Suc.prems(1) Suc.prems(2) Suc.prems(3) deatomization1' diff_commute diff_diff_left diff_is_0_eq nat_le_linear plus_1_eq_Suc)
  qed
qed

corollary detomization1: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> m \<ge> m'  \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t - (m - m')\<^esup> (c', s', 0)"
  by (metis Pair_inject canonically_ordered_monoid_add_class.lessE deatomization1' deatomization1'' diff_add_inverse linorder_le_cases linorder_not_less reflE)

corollary atomic_residual2: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> m \<le> m' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m' - m)"
  apply (induction m arbitrary: c s t c' s' m')
   apply auto
  by (smt (verit, ccfv_SIG) Suc_le_mono Suc_pred atomic_lens diff_Suc_Suc diff_is_0_eq' diff_zero not_gr_zero)

lemma deatomization2: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> m \<le> m' \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t + (m' - m) \<^esup> (c', s', 0)"
  by (meson atomic_residual2 full_atomic_backtrack)

theorem deatomization: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t\<^esup> (c', s', m') \<Longrightarrow> (c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t + (m' - m) - (m - m')\<^esup> (c', s', 0)"
  using detomization1 deatomization2 
  by (metis add.right_neutral diff_is_0_eq' diff_zero nat_le_linear)

lemma split_steps:  "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s, 0) \<Longrightarrow> cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> cs'' \<Longrightarrow> cs'' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t - t'\<^esup> (SKIP, s, 0)"
proof (induction t arbitrary: t' cs s cs'')
  case 0
  then show ?case apply auto 
    using rel_pow.cases by fastforce
next
  case (Suc t)
  from \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (SKIP, s, 0)\<close> obtain cs' where \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'\<close> \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s, 0)\<close>
    by blast
  then show ?case proof (cases t')
    case 0
    have \<open>cs'' = cs\<close> 
      using "0" Suc.prems(2) by auto
    then show ?thesis 
      by (simp add: "0" Suc.prems(1))
  next
    case (Suc nat)
    from \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> cs''\<close> obtain cs''' where \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'''\<close> \<open>cs''' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close>
      using Suc by auto
    from \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'\<close> \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'''\<close> have \<open>cs' = cs'''\<close> 
      using atomic_step_t_deterministic by blast
    hence \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close> 
      by (simp add: \<open>cs''' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close>)
    from Suc.IH[OF \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s, 0)\<close> \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close>] have
      \<open>cs'' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t - nat\<^esup> (SKIP, s, 0)\<close> by auto
    then show ?thesis 
      by (simp add: Suc)
  qed
qed

lemma split_steps':  "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s, 0) \<Longrightarrow> cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> cs'' \<Longrightarrow>  t \<ge> t' \<Longrightarrow>cs'' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t - t'\<^esup> (c', s, 0)"
proof (induction t arbitrary: t' cs s cs'' c')
  case 0
  then show ?case by auto
next
  case (Suc t)
  from \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>Suc t\<^esup> (c', s, 0)\<close> obtain cs' where \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'\<close> \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s, 0)\<close>
    by blast
  then show ?case proof (cases t')
    case 0
    have \<open>cs'' = cs\<close> 
      using "0" Suc.prems(2) by auto
    then show ?thesis 
      by (simp add: "0" Suc.prems(1))
  next
    case (Suc nat)
    from \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t'\<^esup> cs''\<close> obtain cs''' where \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'''\<close> \<open>cs''' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close>
      using Suc by auto
    from \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'\<close> \<open>cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'''\<close> have \<open>cs' = cs'''\<close> 
      using atomic_step_t_deterministic by blast
    hence \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close> 
      by (simp add: \<open>cs''' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close>)
    from Suc.IH[OF \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s, 0)\<close> \<open>cs' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>nat\<^esup> cs''\<close>] have
      \<open>cs'' \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t - nat\<^esup> (c', s, 0)\<close> 
      using Suc Suc.prems(3) by blast
    then show ?thesis 
      by (simp add: Suc)
  qed
qed

lemma split_sequence_SKIP: 
  assumes "(SKIP;; c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s', 0)"
  shows "(c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t - skip_costs s\<^esup> (SKIP, s', 0)"
proof-
  have \<open>(SKIP;; c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>skip_costs s\<^esup> (c, s, 0)\<close> using Skip_ex by simp
  then show ?thesis using \<open>(SKIP;; c, s, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (SKIP, s', 0)\<close> 
    by (simp add: split_steps)
qed

end
end