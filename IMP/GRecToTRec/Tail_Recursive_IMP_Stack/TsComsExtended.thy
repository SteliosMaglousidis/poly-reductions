theory TsComsExtended
  imports IMP_Tailcall_Stacked
begin

abbreviation if_lequals_var ("(IF _/=_ THEN _/ ELSE _ )"  [0, 0, 0, 61] 61) where
"if_lequals_var b v c1 c2  \<equiv> 
  (PUSH b ;; (b ::= Sub (V b) (V v)) ;; IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1))"

abbreviation if_lequals_val ("(IF _/=_ THEN _/ ELSE _ )"  [0, 0, 0, 61] 61) where
"if_lequals_val b v c1 c2  \<equiv> 
  (PUSH b ;; (b ::= Sub (V b) (N v)) ;; IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1))"

lemma tIfleVTrue: 
  assumes 
    "s b \<le> s v" 
    "c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')" 
    "y=x+5" 
  shows
    (* why is this needed ? *)
    "(c \<turnstile> (IF b = (v::vname) THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack'))"
proof-
  from \<open>s b \<le> s v\<close> have \<open>aval (Sub (V b) (V v)) s = 0\<close> by simp
  have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (V v)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := 0),stack(b := s b # stack b))\<close>
    using tSeq[OF tsPush[of c b s stack] tAssign[of c b "Sub (V b) (V v)" s]] \<open>aval (Sub (V b) (V v)) s = 0\<close>
    by (simp add: numeral_3_eq_3)
  have \<open>c \<turnstile> (POP b,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close>
    using tsPop[of "stack(b := s b # stack b)" b "s b" "stack b" c "s(b := 0)"] by simp
  hence \<open>c \<turnstile> (POP b;; c1,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (POP b,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close> \<open>c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')\<close>]
    by auto
  have \<open>(s(b := 0)) b = 0\<close> by auto
  have \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>
    using tIfFalse[OF \<open>(s(b := 0)) b = 0\<close> \<open>c \<turnstile> (POP b;; c1,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>]
    by fastforce 
  have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (V v)) ;; IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s,stack) \<Rightarrow>\<^bsup>x + 5\<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (V v)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := 0),stack(b := s b # stack b))\<close> \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>]
    by fastforce
  then show ?thesis 
    by (simp add: assms(3))
qed 

lemma tIfleVFalse: 
  assumes 
    "s b > s v" 
    "c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')" 
    "y=x+5" 
  shows 
    "(c \<turnstile> (IF b = (v::vname) THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack'))"
proof-
  from \<open>s b > s v\<close> have \<open>aval (Sub (V b) (V v)) s \<noteq> 0\<close> by simp
  hence \<open>aval (A(V b)) s -  aval (A(V v)) s \<noteq> 0\<close> by simp
  hence \<open>(s(b := aval (A(V b)) s -  aval (A(V v)) s)) b \<noteq> 0\<close> by simp
  have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (V v)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b))\<close>
    using tSeq[OF tsPush[of c b s stack] tAssign[of c b "Sub (V b) (V v)" s]] \<open>aval (Sub (V b) (V v)) s \<noteq> 0\<close>
    by (simp add: numeral_3_eq_3)
  have \<open>c \<turnstile> (POP b,s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close>
    using tsPop[of "stack(b := s b # stack b)" b "s b" "stack b" c "s(b := aval (A(V b)) s -  aval (A(V v)) s)"] by simp
  hence \<open>c \<turnstile> (POP b;; c2,s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (POP b,s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close> \<open>c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')\<close>]
    by simp
  have \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>
    using tIfTrue[of \<open>(s(b := aval (A(V b)) s -  aval (A(V v)) s))\<close> b c \<open>POP b ;; c2\<close> \<open>stack(b := s b # stack b)\<close>
                  "Suc x" t stack' \<open>Suc x + 1\<close> \<open>POP b ;; c1\<close>,
                  OF \<open>(s(b := aval (A(V b)) s -  aval (A(V v)) s)) b \<noteq> 0\<close> \<open>c \<turnstile> (POP b;; c2,s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>]
    by simp
    have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (V v)) ;; IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s,stack) \<Rightarrow>\<^bsup>x + 5\<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (V v)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b))\<close> \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := aval (A(V b)) s -  aval (A(V v)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>]
    by fastforce
  then show ?thesis 
    by (simp add: assms(3))
qed 

lemma tIfleNTrue: 
  assumes 
    "s b \<le> n" 
    "c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')" 
    "y=x+5" 
  shows
    (* why is this needed ? *)
    "(c \<turnstile> (IF b = (n::val) THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack'))"
proof-
  from \<open>s b \<le> n\<close> have \<open>aval (Sub (V b) (N n)) s = 0\<close> by simp
  have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (N n)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := 0),stack(b := s b # stack b))\<close>
    using tSeq[OF tsPush[of c b s stack] tAssign[of c b "Sub (V b) (N n)" s]] \<open>aval (Sub (V b) (N n)) s = 0\<close>
    by (simp add: numeral_3_eq_3)
  have \<open>c \<turnstile> (POP b,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close>
    using tsPop[of "stack(b := s b # stack b)" b "s b" "stack b" c "s(b := 0)"] by simp
  hence \<open>c \<turnstile> (POP b;; c1,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (POP b,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close> \<open>c \<turnstile> (c1,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')\<close>]
    by auto
  have \<open>(s(b := 0)) b = 0\<close> by auto
  have \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>
    using tIfFalse[OF \<open>(s(b := 0)) b = 0\<close> \<open>c \<turnstile> (POP b;; c1,s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>]
    by fastforce 
  have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (N n)) ;; IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s,stack) \<Rightarrow>\<^bsup>x + 5\<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (N n)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := 0),stack(b := s b # stack b))\<close> \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := 0),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>]
    by fastforce
  then show ?thesis 
    by (simp add: assms(3))
qed 

lemma tIfleNFalse: 
  assumes 
    "s b > n" 
    "c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')" 
    "y=x+5" 
  shows 
    "(c \<turnstile> (IF b = (n::val) THEN c1 ELSE c2,s,stack) \<Rightarrow>\<^bsup>y \<^esup> (t,stack'))"
proof-
  from \<open>s b > n\<close> have \<open>aval (Sub (V b) (N n)) s \<noteq> 0\<close> by simp
  hence \<open>aval (A(V b)) s -  aval (A(N n)) s \<noteq> 0\<close> by simp
  hence \<open>(s(b := aval (A(V b)) s -  aval (A(N n)) s)) b \<noteq> 0\<close> by simp
  have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (N n)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b))\<close>
    using tSeq[OF tsPush[of c b s stack] tAssign[of c b "Sub (V b) (N n)" s]] \<open>aval (Sub (V b) (N n)) s \<noteq> 0\<close>
    by (simp add: numeral_3_eq_3)
  have \<open>c \<turnstile> (POP b,s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close>
    using tsPop[of "stack(b := s b # stack b)" b "s b" "stack b" c "s(b := aval (A(V b)) s -  aval (A(N n)) s)"] by simp
  hence \<open>c \<turnstile> (POP b;; c2,s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (POP b,s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack)\<close> \<open>c \<turnstile> (c2,s,stack) \<Rightarrow>\<^bsup>x \<^esup> (t,stack')\<close>]
    by simp
  have \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>
    using tIfTrue[of \<open>(s(b := aval (A(V b)) s -  aval (A(N n)) s))\<close> b c \<open>POP b ;; c2\<close> \<open>stack(b := s b # stack b)\<close>
                  "Suc x" t stack' \<open>Suc x + 1\<close> \<open>POP b ;; c1\<close>,
                  OF \<open>(s(b := aval (A(V b)) s -  aval (A(N n)) s)) b \<noteq> 0\<close> \<open>c \<turnstile> (POP b;; c2,s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup> Suc x \<^esup> (t,stack')\<close>]
    by simp
    have \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (N n)) ;; IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s,stack) \<Rightarrow>\<^bsup>x + 5\<^esup> (t,stack')\<close>
    using tSeq[OF \<open>c \<turnstile> (PUSH b ;; (b ::= Sub (V b) (N n)),s,stack) \<Rightarrow>\<^bsup> 3 \<^esup> (s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b))\<close> \<open>c \<turnstile> (IF b\<noteq>0 THEN POP b ;; c2 ELSE (POP b ;; c1),s(b := aval (A(V b)) s -  aval (A(N n)) s),stack(b := s b # stack b)) \<Rightarrow>\<^bsup>Suc x + 1\<^esup> (t,stack')\<close>]
    by fastforce
  then show ?thesis 
    by (simp add: assms(3))
qed 


(* works properly if switch values are ordered *)
fun switch :: "vname \<Rightarrow> (val*tscom) list \<Rightarrow> tscom" where
"switch b [] = tsSKIP" |
(*fancy*)
"switch b ((v,c)#vcs) = (IF b = v THEN c ELSE (switch b vcs))" 

lemma switch_empty_sem: "(c \<turnstile> (switch b [],s,stack)  \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack))"
  by auto

lemma switch_true: "s b \<le> v \<Longrightarrow> (c' \<turnstile> (c,s,stack) \<Rightarrow>\<^bsup> x \<^esup> (t,stack')) 
                        \<Longrightarrow> (c' \<turnstile> (switch b ((v,c)#vcs),s,stack)  \<Rightarrow>\<^bsup> x + 5 \<^esup> (t,stack'))"
  by fastforce

lemma switch_false: "s b > v \<Longrightarrow> (c' \<turnstile> (switch b vcs,s,stack)  \<Rightarrow>\<^bsup> x \<^esup> (t,stack'))
                        \<Longrightarrow> (c' \<turnstile> (switch b ((v,c)#vcs),s,stack)  \<Rightarrow>\<^bsup> x + 5 \<^esup> (t,stack'))"
  by fastforce

fun switch_basic_acc :: "vname \<Rightarrow> tscom list \<Rightarrow> nat \<Rightarrow> tscom" where
"switch_basic_acc b [] n = tsSKIP" |
"switch_basic_acc b (c#vcs) n = (IF b = n THEN c ELSE (switch_basic_acc b vcs (Suc n)))" 

abbreviation "switch_basic b vcs \<equiv> switch_basic_acc b vcs 1"

fun push_many :: "vname list \<Rightarrow> tscom" ("(PUSH# _ )"  [61] 61) where
"push_many [] = tsSKIP" |
"push_many (v#vs) = (PUSH v) ;; push_many vs" 

fun pop_many :: "vname list \<Rightarrow> tscom" ("(POP# _ )"  [61] 61) where
"pop_many [] = tsSKIP" |
"pop_many (v#vs) = (POP v) ;; pop_many vs" 

lemma push_many_empty_sem: "(c \<turnstile> (PUSH# [],s,stack)  \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack))"
  by auto

lemma pop_many_empty_sem: "(c \<turnstile> (POP# [],s,stack)  \<Rightarrow>\<^bsup> Suc 0 \<^esup> (s,stack))"
  by auto




end 