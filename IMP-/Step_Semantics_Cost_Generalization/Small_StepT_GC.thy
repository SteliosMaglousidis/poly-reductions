
section "Small step semantics of IMP- "

subsection "Small step semantics definition"
theory Small_StepT_GC  imports Big_StepT_Generalized_Cost_Final Main "../Com" "../Rel_Pow" begin

paragraph "Summary"

text\<open>Naive approach to generalize costs similar to big step. 
     One would probalby want to work with the transitive closure 
     rather than the predicate.\<close>

context BS_Generalized_Cost begin

inductive
  small_step_GC :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>G\<^sub>C\<^bsup> _ \<^esup> _" 55) 
where
Assign:  "(x ::= a, s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> assign_costs a s \<^esup> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> skip_costs s \<^esup> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> t \<^esup> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> t \<^esup> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "s b \<noteq> 0 \<Longrightarrow> (IF b \<noteq>0 THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> Suc 0 \<^esup> (c\<^sub>1,s)" |
IfFalse: "s b = 0 \<Longrightarrow> (IF b \<noteq>0  THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> Suc 0 \<^esup> (c\<^sub>2,s)" |
                                                   
WhileTrue:   "s b \<noteq> 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> Suc 0 \<^esup>
            (c ;; WHILE b \<noteq>0 DO c,s)" |
WhileFalse:   "s b = 0 \<Longrightarrow> (WHILE b\<noteq>0 DO c,s) \<rightarrow>\<^sub>G\<^sub>C\<^bsup> while_exit_costs s \<^esup>
            (SKIP,s)"

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
lemmas small_step_GC_atomic_induct = atomic_step_GC.induct[split_format(complete), OF BS_Generalized_Cost_axioms]


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

lemma atomic_ex_gen: "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c', s', m') \<Longrightarrow> \<exists>t' . t = m + t'"
proof-
  have "(c, s, m) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>m\<^esup> (c, s, 0)" using atomic_ex by auto


lemma deterministic:
  "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs' \<Longrightarrow> cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A cs'' \<Longrightarrow> cs'' = cs'"
proof(induction arbitrary: cs'' rule: atomic_step_GC.induct)
  case (atomic_step c s n)
  then show ?case using atomic_ex_t atomic_ex_det 
    by (metis (mono_tags, opaque_lifting) split_pairs)
next
  case (Assign x a s)
  then show ?case by auto
next
  case (Seq1 c\<^sub>2 s)
  then show ?case by auto
next
  case (Seq2 c\<^sub>1 s m c\<^sub>1' s' m' c\<^sub>2)
  then show ?case apply (cases m) subgoal apply simp 
      apply (cases m') apply simp 
       apply blast
      by blast
    apply (cases m') apply simp 
     apply (smt (verit, best) BS_Generalized_Cost.AtomicStepE BS_Generalized_Cost.atomic_step BS_Generalized_Cost_axioms Pair_inject com.inject(2))
    apply simp 

next
  case (IfTrue s b c\<^sub>1 c\<^sub>2)
  then show ?case sorry
next
  case (IfFalse s b c\<^sub>1 c\<^sub>2)
  then show ?case by auto
next
  case (WhileTrue s b c)
  then show ?case by auto
next
  case (WhileFalse s b c)
  then show ?case by auto
qed

lemma small_step_t_deterministic: "cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> cs' \<Longrightarrow> cs \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> cs'' \<Longrightarrow> cs'' = cs'"
  apply(induction t arbitrary: cs)
  using deterministic apply auto
  using Small_StepT.deterministic by blast

subsection "Progress property"
text "every command costs time"
lemma small_step_progress: "(c, s, a) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> p \<^esup> t \<Longrightarrow> t \<noteq> (c, s, a)  \<Longrightarrow> p > 0"
  apply(induction p) by auto

subsection "Sequence properties"
declare rel_pow_intros[simp,intro]

text "sequence property"
lemma star_seq2: "(c1,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t\<^esup> (c1',s',0) \<Longrightarrow> (c1;;c2,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (c1';;c2,s',0)"
proof(induction t arbitrary: c1 c1' s s' )
  case (Suc t)
  then obtain c1'' s''  where "(c1,s,0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A (c1'', s'',0)" 
                         and "(c1'', s'', 0)  \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup>  (c1', s', 0)" sorry
  moreover then have "(c1'';;c2, s'', 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t \<^esup> (c1';;c2, s', 0)" using Suc by simp
  ultimately show ?case 
    by blast
qed auto

text "sequence time is one plus sum of the sub-commands times"
lemma seq_comp:
  "\<lbrakk> (c1,s1,m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 \<^esup> (SKIP,s2,m2); (c2,s2,m2) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t2 \<^esup> (c3,s3,m3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> t1 + t2 + skip_costs s1 + 1\<^esup> (c3,s3,m3)"
proof (induction t1 arbitrary: c1 s1)
  case 0
  have "c1 = SKIP" using \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>0\<^esup> (SKIP, s2, m2)\<close> by auto
  have "m1 = m2" using \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>0\<^esup> (SKIP, s2, m2)\<close> by auto
  have "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>m1\<^esup> (c1, s1, 0)" using atomic_ex by auto
  hence "(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>m1\<^esup> (c1, s2, 0)" using \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>0\<^esup> (SKIP, s2, m2)\<close> by auto
  have "(c1;; c2, s1, 0) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A  (c2,s1,skip_costs s1)"
    using \<open>c1 = SKIP\<close> by simp
  hence "(c2,s1,skip_costs s1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup> skip_costs s1 \<^esup> (c2,s1,0)"
    using atomic_ex by auto
  then show ?case 
    using \<open>m1 = m2\<close> \<open>(c1, s1, m1) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>0\<^esup> (SKIP, s2, m2)\<close> \<open>(c2, s2, m2) \<rightarrow>\<^sub>G\<^sub>C\<^sub>A\<^bsup>t2\<^esup> (c3, s3, m3)\<close> 
    proof(induction m1 arbitrary: m2)
    case 0
    then show ?case apply auto 
      by (smt (verit, ccfv_SIG) add.commute atomic_step_GC.Seq1 rel_pow.step rel_pow_sum)
  next
    case (Suc nat)
    then show ?case apply auto 
  qed 
next
  case (Suc t1)
  then obtain c1' s1' where *: "(c1, s1) \<rightarrow> (c1',s1')" and "(c1',s1') \<rightarrow>\<^bsup> t1 \<^esup> (SKIP,s2)"
    using relpowp_Suc_E2 by auto
  then have "(c1';;c2, s1') \<rightarrow>\<^bsup> t1 + t2 + 1 \<^esup> (c3, s3)" using Suc sorry
  then show ?case using Suc by auto
qed

lemma small_step_cant_continue_after_reaching_SKIP: "(c1, s1) \<rightarrow>\<^bsup> t1 \<^esup> (SKIP, s2)
  \<Longrightarrow> (c1, s1) \<rightarrow>\<^bsup> t2 \<^esup> (c3, s3)
  \<Longrightarrow> t2 \<le> t1"
proof(rule ccontr)
  assume "(c1, s1) \<rightarrow>\<^bsup>t1\<^esup> (SKIP, s2)" "(c1, s1) \<rightarrow>\<^bsup>t2\<^esup> (c3, s3)" "\<not> t2 \<le> t1"
  then obtain t3 where "t2 = t1 + t3" "t3 > 0"
    by (metis less_imp_add_positive not_le)
  hence "(c1, s1) \<rightarrow>\<^bsup> t1 + t3 \<^esup> (c3, s3)" 
    using \<open>(c1, s1) \<rightarrow>\<^bsup> t2 \<^esup> (c3, s3)\<close> 
    by auto
  then obtain c4s4 where "(c1, s1) \<rightarrow>\<^bsup>t1\<^esup> c4s4" "c4s4 \<rightarrow>\<^bsup>t3\<^esup> (c3, s3)" 
    using \<open>(c1, s1) \<rightarrow>\<^bsup>t2\<^esup> (c3, s3)\<close> rel_pow_sum_decomp[OF \<open>(c1, s1) \<rightarrow>\<^bsup> t1 + t3 \<^esup> (c3, s3)\<close>]
    by blast
  hence "c4s4 = (SKIP, s2)"
    using small_step_t_deterministic \<open>(c1, s1) \<rightarrow>\<^bsup>t1\<^esup> (SKIP, s2)\<close>
    by simp
  hence "t3 = 0" 
    using \<open>c4s4 \<rightarrow>\<^bsup>t3\<^esup> (c3, s3)\<close>
    by (cases t3) auto
  thus False using \<open>t3 > 0\<close> by simp
qed

end