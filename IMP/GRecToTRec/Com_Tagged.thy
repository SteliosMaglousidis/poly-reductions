theory Com_Tagged
  imports "General_Recursive_IMP/IMP_GRec" 
          "Tail_Recursive_IMP_Stack/IMP_Tailcall_Stacked"
          "Tail_Recursive_IMP_Stack/TsComsExtended"
begin


datatype
  com_tagged = SKIPTagged nat
      | AssignTagged vname aexp
      | SeqTagged com_tagged com_tagged
      | IfTagged vname com_tagged com_tagged
      | CallTagged com vname
      | RecTagged nat 
      | TailTagged 
      | PushTagged vname
      | PopTagged vname

notation AssignTagged ("_ #::= _" [1000, 61] 61) and
         SeqTagged ("_ #;; _" [60, 61] 60) and
         IfTagged ("(#IF _/\<noteq>0 THEN _ ELSE _)" [0, 0, 61] 61) and
         CallTagged ("#CALL _ RETURN _") and
         RecTagged ("#RECURSE _") and
         PushTagged ("#PUSH _" [61] 61) and
         PopTagged ("#POP _" [61] 61)

fun push_many_tagged :: "vname list \<Rightarrow> com_tagged" ("(#PUSH# _ )"  [61] 61) where
"push_many_tagged [] = SKIPTagged 0" |
"push_many_tagged (v#vs) = (#PUSH v) #;; push_many_tagged vs" 

fun pop_many_tagged :: "vname list \<Rightarrow> com_tagged" ("(#POP# _ )"  [61] 61) where
"pop_many_tagged [] = SKIPTagged 0" |
"pop_many_tagged (v#vs) = (#POP v)  #;; pop_many_tagged vs" 

unbundle rcom_syntax and no com'_syntax and no tscom_syntax

fun tag_rcom :: "rcom \<Rightarrow> com_tagged" where
  "tag_rcom (ct1 ;; ct2) = tag_rcom ct1 #;; tag_rcom ct2" |
  "tag_rcom (IF b\<noteq>0 THEN ct1 ELSE ct2) = (#IF b\<noteq>0 THEN tag_rcom ct1 ELSE tag_rcom ct2)" |
  "tag_rcom RECURSE = #RECURSE 0" |
  "tag_rcom (rSKIP) = (SKIPTagged 0)" |
  "tag_rcom (x ::= a) = (x #::= a)" |
  "tag_rcom (CALL v RETURN r) = (#CALL v RETURN r)" 

fun untag_rcom :: "com_tagged \<Rightarrow> rcom" where
  "untag_rcom (ct1 #;; ct2) = untag_rcom ct1 ;; untag_rcom ct2" |
  "untag_rcom (#IF b\<noteq>0 THEN ct1 ELSE ct2) = (IF b\<noteq>0 THEN untag_rcom ct1 ELSE untag_rcom ct2)" |
  "untag_rcom #RECURSE n = RECURSE" |
  "untag_rcom (SKIPTagged n) = rSKIP" |
  "untag_rcom (x #::= a) = (x ::= a)" |
  "untag_rcom (#CALL v RETURN r) = (CALL v RETURN r)" 

lemma rcom_tagged_sound: "d \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile>\<^sub>R (untag_rcom (tag_rcom c),s,ret) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s ret z t  rule: tag_rcom.induct) fastforce+

lemma rcom_tagged_complete: "d \<turnstile>\<^sub>R (untag_rcom (tag_rcom c),s,ret) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s z t ret rule: tag_rcom.induct) fastforce+

lemma rcom_tagged_correct: "d \<turnstile>\<^sub>R (untag_rcom (tag_rcom c),s,ret) \<Rightarrow>\<^bsup>z \<^esup> t   
  \<longleftrightarrow> d \<turnstile>\<^sub>R (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t" using rcom_tagged_sound rcom_tagged_complete by metis

unbundle tscom_syntax and no com'_syntax and no rcom_syntax

fun tag_tscom :: "tscom \<Rightarrow> com_tagged" where
  "tag_tscom (ct1 ;; ct2) = tag_tscom ct1 #;; tag_tscom ct2" |
  "tag_tscom (IF b\<noteq>0 THEN ct1 ELSE ct2) = (#IF b\<noteq>0 THEN tag_tscom ct1 ELSE tag_tscom ct2)" |
  "tag_tscom tsTAIL = TailTagged" |
  "tag_tscom (tsSKIP) = (SKIPTagged 0)" |
  "tag_tscom (x ::= a) = (x #::= a)" |
  "tag_tscom (CALL v RETURN r) = (#CALL v RETURN r)" |
  "tag_tscom (PUSH v) = (#PUSH v)" |
  "tag_tscom (POP v) = (#POP v)" 

fun untag_tscom :: "com_tagged \<Rightarrow> tscom" where
  "untag_tscom (ct1 #;; ct2) = untag_tscom ct1 ;; untag_tscom ct2" |
  "untag_tscom (#IF b\<noteq>0 THEN ct1 ELSE ct2) = (IF b\<noteq>0 THEN untag_tscom ct1 ELSE untag_tscom ct2)" |
  "untag_tscom TailTagged = tsTAIL" |
  "untag_tscom (SKIPTagged n) = tsSKIP" |
  "untag_tscom (x #::= a) = (x ::= a)" |
  "untag_tscom (#CALL v RETURN r) = (CALL v RETURN r)"|
  "untag_tscom (#PUSH v) = (PUSH v)" |
  "untag_tscom (#POP v) = (POP v)" 

lemma tscom_tagged_sound: "d \<turnstile> (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile> (untag_tscom (tag_tscom c),s,ret) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s ret z t  rule: tag_tscom.induct) fastforce+

lemma tscom_tagged_complete: "d \<turnstile> (untag_tscom (tag_tscom c),s,ret) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile> (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s z t ret rule: tag_tscom.induct) fastforce+

lemma tscom_tagged_correct: "d \<turnstile> (untag_tscom (tag_tscom c),s,ret) \<Rightarrow>\<^bsup>z \<^esup> t   
  \<longleftrightarrow> d \<turnstile> (c,s,ret) \<Rightarrow>\<^bsup>z \<^esup> t" using tscom_tagged_sound tscom_tagged_complete by metis

end