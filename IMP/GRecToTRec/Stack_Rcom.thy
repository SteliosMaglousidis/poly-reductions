theory Stack_Rcom
  imports GRecToTRec "Tail_Recursive_IMP_Stack/Stack_Memory"
begin

unbundle rcom_syntax'
                
fun stack_rcom :: "rcom \<Rightarrow> vname list \<Rightarrow> tscom" ("\<lblot>_ STACK _\<rblot>") where 
  "\<lblot>(IF\<^sub>R b\<noteq>0 THEN c1 ELSE c2) STACK vs\<rblot> = (IF b\<noteq>0 THEN \<lblot>c1 STACK vs\<rblot> ELSE \<lblot>c2 STACK vs\<rblot>)"
| "\<lblot>c1 ;;\<^sub>R c2 STACK vs\<rblot> = (\<lblot>c1 STACK vs\<rblot> ;; \<lblot>c2 STACK vs\<rblot>)"
| "\<lblot>RECURSE STACK vs\<rblot> = (PUSHMANY vs ;; TAIL ;; POPMANY vs)"
| "\<lblot>rSKIP STACK vs\<rblot> = SKIP"
| "\<lblot>CALL\<^sub>R c RETURN r STACK vs\<rblot> = CALL c RETURN r"
| "\<lblot>x ::=\<^sub>R a STACK vs\<rblot> = x ::= a"

abbreviation grec_context :: "rcom \<Rightarrow> vname \<Rightarrow> vname list"  ("\<Gamma>[_]\<rightarrow>_") where
"grec_context c ret \<equiv> removeAll ret (vars c)"

lemma grec_context_set: "set (\<Gamma>[c]\<rightarrow>ret) = set (vars c) - {ret}"
  by simp

lemma stacked_rcom_vars: "set (vars \<lblot>c STACK vs\<rblot>) \<subseteq> (set (vars c) \<union> set vs)"
  by (induction c vs rule: stack_rcom.induct) (auto simp add: push_many_vars pop_many_vars)

lemma stacked_rcom_vars': "set (vars \<lblot>c STACK vs\<rblot>) \<supseteq> set (vars c)"
  by (induction c vs rule: stack_rcom.induct) (auto simp add: push_many_vars pop_many_vars)

corollary stacked_rcom_context_vars: "set (vars \<lblot>c STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot>) = set (vars c)"
  using stacked_rcom_vars[of c "(\<Gamma>[c]\<rightarrow>ret)"] stacked_rcom_vars'[of c "(\<Gamma>[c]\<rightarrow>ret)"] by auto

lemma override_on_except: "t = override_on s t S \<Longrightarrow> override_on t s (S - {v}) = s(v := t v)"
  unfolding override_on_def fun_upd_def apply auto by metis


theorem stack_memory_comp: "c' \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> 
        \<exists>t'. \<lblot>c' STACK (\<Gamma>[c']\<rightarrow>ret)\<rblot> 
          \<turnstile> (\<lblot>c STACK (\<Gamma>[c']\<rightarrow>ret)\<rblot>,s,stack) \<Rightarrow>\<^bsup>t'\<^esup> (s',stack) \<and> t' \<le> t + (t * (2 * Suc (length (\<Gamma>[c']\<rightarrow>ret))))"
proof(induction c' c s ret t s' arbitrary: stack  rule: rbig_step_t_induct)
  case (rAssign c x a s ret)
  then show ?case
    using stack_rcom.simps(6) tAssign by (metis le_add1)
next
  case (rSeq c c1 s1 ret x s2 c2 y s3 z)
  obtain tx where \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (\<lblot>c1 STACK \<Gamma>[c]\<rightarrow>ret\<rblot>, s1, stack) \<Rightarrow>\<^bsup>tx\<^esup>  (s2, stack)\<close> 
                  \<open>tx \<le> x + x * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close>
    using rSeq.IH(1) by blast
  obtain ty where \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (\<lblot>c2 STACK \<Gamma>[c]\<rightarrow>ret\<rblot>, s2, stack) \<Rightarrow>\<^bsup>ty\<^esup>  (s3, stack)\<close> 
                  \<open>ty \<le> y + y * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close>
    using rSeq.IH(2) by blast
  hence \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (\<lblot>c1;;\<^sub>R c2 STACK \<Gamma>[c]\<rightarrow>ret\<rblot>, s1, stack) \<Rightarrow>\<^bsup>tx + ty\<^esup>  (s3, stack)\<close>
    using \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (\<lblot>c1 STACK \<Gamma>[c]\<rightarrow>ret\<rblot>, s1, stack) \<Rightarrow>\<^bsup>tx\<^esup> (s2, stack)\<close> stack_rcom.simps(2) tSeq
    by presburger
  have \<open>tx + ty \<le>x + y + x * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)) + y * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close> 
    using \<open>tx \<le> x + x * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close> \<open>ty \<le> y + y * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close>
    by linarith 
  hence \<open>tx + ty \<le>x + y + (x + y) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close> 
    using add_mult_distrib by presburger
  hence \<open>tx + ty \<le>z + z * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close> 
    using rSeq.hyps(3) by blast
  then show ?case 
    using \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (\<lblot>c1;;\<^sub>R c2 STACK \<Gamma>[c]\<rightarrow>ret\<rblot>, s1, stack) \<Rightarrow>\<^bsup>tx + ty\<^esup> (s3, stack)\<close>
    by blast
next
  case (rCall C s z t c r ret)
  then show ?case 
    using stack_rcom.simps(5) tCall by (metis le_add1)
next
  case (rRec c s ret z t)
  have \<open>\<lblot>RECURSE STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot> = (PUSHMANY (\<Gamma>[c]\<rightarrow>ret) ;; TAIL ;; POPMANY (\<Gamma>[c]\<rightarrow>ret))\<close>
    by simp
  have \<open>\<lblot>c STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot> \<turnstile> 
       (PUSHMANY (\<Gamma>[c]\<rightarrow>ret), s, stack) \<Rightarrow>\<^bsup>Suc (length (\<Gamma>[c]\<rightarrow>ret))\<^esup>  (s, push_many_stack stack s (\<Gamma>[c]\<rightarrow>ret))\<close>
    using push_many_sem by blast
  obtain t' where \<open>\<lblot>c STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot> \<turnstile> (\<lblot>c STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot>, s, push_many_stack stack s (\<Gamma>[c]\<rightarrow>ret)) 
                    \<Rightarrow>\<^bsup>t'\<^esup>  (t, push_many_stack stack s (\<Gamma>[c]\<rightarrow>ret))\<close>
                  \<open>t' \<le> z + z * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close>
    using rRec.IH by blast
  hence \<open>\<lblot>c STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot> \<turnstile> (PUSHMANY (\<Gamma>[c]\<rightarrow>ret) ;; TAIL, s, stack) \<Rightarrow>\<^bsup>Suc (length (\<Gamma>[c]\<rightarrow>ret)) + 5 + t'\<^esup>  (t, push_many_stack stack s (\<Gamma>[c]\<rightarrow>ret))\<close>
    using \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (PUSHMANY \<Gamma>[c]\<rightarrow>ret , s, stack) \<Rightarrow>\<^bsup>Suc (length \<Gamma>[c]\<rightarrow>ret)\<^esup> (s, push_many_stack stack s \<Gamma>[c]\<rightarrow>ret)\<close>
      ab_semigroup_add_class.add_ac(1) by blast
  have \<open>t = override_on s t (set (vars c))\<close> 
    by (metis
        \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot>, s, push_many_stack stack s \<Gamma>[c]\<rightarrow>ret) \<Rightarrow>\<^bsup>t'\<^esup> (t, push_many_stack stack s \<Gamma>[c]\<rightarrow>ret)\<close>
        stacked_rcom_context_vars stacked_rcom_vars' tsnoninterference_override_on)
  have \<open>override_on t s (set (\<Gamma>[c]\<rightarrow>ret)) = s(ret := t ret)\<close> using override_on_except[OF \<open>t = override_on s t (set (vars c))\<close> , of ret]
    by simp
  hence \<open>\<lblot>c STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot> \<turnstile> (POPMANY (\<Gamma>[c]\<rightarrow>ret), t, push_many_stack stack s (\<Gamma>[c]\<rightarrow>ret)) 
          \<Rightarrow>\<^bsup>Suc (length ((\<Gamma>[c]\<rightarrow>ret)))\<^esup> (s(ret := t ret), stack)\<close> by (metis stack_memory_many)
  hence \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> ((PUSHMANY (\<Gamma>[c]\<rightarrow>ret) ;; TAIL ;; POPMANY (\<Gamma>[c]\<rightarrow>ret)), s, stack) \<Rightarrow>\<^bsup>Suc (length (\<Gamma>[c]\<rightarrow>ret)) + 5 + t' + Suc (length (\<Gamma>[c]\<rightarrow>ret))\<^esup>  (s(ret := t ret), stack)\<close>
    using
      \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (PUSHMANY \<Gamma>[c]\<rightarrow>ret ;; TAIL, s, stack) \<Rightarrow>\<^bsup>Suc (length \<Gamma>[c]\<rightarrow>ret) + 5 + t'\<^esup> (t, push_many_stack stack s \<Gamma>[c]\<rightarrow>ret)\<close>
    by blast
  hence \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> ((PUSHMANY (\<Gamma>[c]\<rightarrow>ret) ;; TAIL ;; POPMANY (\<Gamma>[c]\<rightarrow>ret)), s, stack) \<Rightarrow>\<^bsup>5 + t' + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret))\<^esup>  (s(ret := t ret), stack)\<close>
    by fastforce
  have \<open>(1 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)) \<le> (5 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close>
    by (meson add_le_mono1 mult_le_mono1 one_le_numeral)
  have \<open>5 + t' + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret)) \<le> 5 + (z + z * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))) + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret))\<close>
    using \<open>t' \<le> z + z * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close> by simp
  hence \<open>5 + t' + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret)) \<le> 5 + (z + (z + 1) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)))\<close>
    by simp
  hence \<open>5 + t' + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret)) \<le> 5 + (z + (1 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)))\<close> 
    by auto
  hence \<open>5 + t' + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret)) \<le> 5 + (z + (5 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)))\<close> 
    using \<open>(1 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)) \<le> (5 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret))\<close> by simp
  then show ?case 
    using \<open>\<lblot>RECURSE STACK (\<Gamma>[c]\<rightarrow>ret)\<rblot> = (PUSHMANY (\<Gamma>[c]\<rightarrow>ret) ;; TAIL ;; POPMANY (\<Gamma>[c]\<rightarrow>ret))\<close> 
      \<open>5 + t' + 2 * Suc (length (\<Gamma>[c]\<rightarrow>ret)) \<le> 5 + (z + (5 + z) * (2 * Suc (length \<Gamma>[c]\<rightarrow>ret)))\<close> 
    by (metis
        \<open>\<lblot>c STACK \<Gamma>[c]\<rightarrow>ret\<rblot> \<turnstile> (PUSHMANY \<Gamma>[c]\<rightarrow>ret ;; TAIL;; POPMANY \<Gamma>[c]\<rightarrow>ret , s, stack) \<Rightarrow>\<^bsup>5 + t' + 2 * Suc (length \<Gamma>[c]\<rightarrow>ret)\<^esup> (s (ret := t ret), stack)\<close>
        ab_semigroup_add_class.add_ac(1))
qed fastforce+

end