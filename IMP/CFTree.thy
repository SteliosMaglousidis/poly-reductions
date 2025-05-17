
section \<open>Binary Tree\<close>

theory CFTree
imports IMP_GRec "HOL-Library.Tree"
begin

unbundle no com'_syntax

unbundle rcom_syntax

datatype
  rcom_tag = rSKIPtag
      | rAssigntag vname aexp
      | rSeqtag   
      | rIftag vname 
      | rCalltag com vname
      | rRectag  

notation rAssigntag ("_ ::=# _" [1000, 61] 61) and
         rSeqtag (";;#" ) and
         rIftag ("(IF# _/\<noteq>0 THEN ELSE)" [0] 61) and
         rCalltag ("CALL# _ RETURN _") and
         rRectag ("RECURSE#")

fun rcom_to_tag :: "rcom \<Rightarrow> rcom_tag" where
"rcom_to_tag (rSKIP) = rSKIPtag" |
"rcom_to_tag (x ::= a) = rAssigntag x a" | 
"rcom_to_tag (c1 ;; c2) = rSeqtag" |
"rcom_to_tag (IF b\<noteq>0 THEN c1 ELSE c2) = rIftag b" |
"rcom_to_tag (CALL C RETURN r) = rCalltag C r"|
"rcom_to_tag RECURSE = rRectag"

fun rcom_to_tree :: "rcom \<Rightarrow> rcom_tag tree" where 
"rcom_to_tree (c1 ;; c2) = \<langle>rcom_to_tree c1,rSeqtag,rcom_to_tree c2\<rangle>" |
"rcom_to_tree (IF b\<noteq>0 THEN c1 ELSE c2) = \<langle>rcom_to_tree c1,rIftag b,rcom_to_tree c2\<rangle>" |
"rcom_to_tree c = \<langle>\<langle>\<rangle>,rcom_to_tag c,\<langle>\<rangle>\<rangle>"

fun tree_to_rcom :: "rcom_tag tree \<Rightarrow> rcom" where 
"tree_to_rcom \<langle>\<rangle> = rSKIP" |
"tree_to_rcom \<langle>ct1,rSeqtag, ct2\<rangle> = (tree_to_rcom ct1 ;; tree_to_rcom ct2)" |
"tree_to_rcom \<langle>ct1,rIftag b, ct2\<rangle> = (IF b\<noteq>0 THEN tree_to_rcom ct1 ELSE tree_to_rcom ct2)" |
"tree_to_rcom \<langle>\<langle>\<rangle>,rCalltag C r,\<langle>\<rangle>\<rangle> = (CALL C RETURN r)"|
"tree_to_rcom \<langle>\<langle>\<rangle>,rAssigntag x a ,\<langle>\<rangle>\<rangle> = (x ::= a)" |
"tree_to_rcom \<langle>\<langle>\<rangle>,rSKIPtag,\<langle>\<rangle>\<rangle> = rSKIP" |
"tree_to_rcom \<langle>\<langle>\<rangle>,rRectag,\<langle>\<rangle>\<rangle> = RECURSE" |
"tree_to_rcom \<langle>_,_,_\<rangle> = rSKIP" 

lemma rcom_tree_sound: "d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile>\<^sub>R (tree_to_rcom (rcom_to_tree c),s) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s z t rule: tree_cf.induct) fastforce+

lemma rcom_tree_complete: "d \<turnstile>\<^sub>R (tree_to_rcom (rcom_to_tree c),s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<Longrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t"
  by (induction c arbitrary: d s z t rule: tree_cf.induct) fastforce+

lemma rcom_tree_comp: "d \<turnstile>\<^sub>R (tree_to_rcom (rcom_to_tree c),s) \<Rightarrow>\<^bsup>z \<^esup> t  
  \<longleftrightarrow> d \<turnstile>\<^sub>R (c,s) \<Rightarrow>\<^bsup>z \<^esup> t" using rcom_tree_sound rcom_tree_complete by metis

fun rcom_tree_in_the_end :: "rcom_tag tree \<Rightarrow> rcom_tag tree \<Rightarrow> rcom_tag tree" where 
"rcom_tree_in_the_end \<langle>\<rangle> ct = \<langle>\<rangle>" |
"rcom_tree_in_the_end \<langle>ct1,rSeqtag, ct2\<rangle> ct = \<langle>ct1,rSeqtag, rcom_tree_in_the_end ct2 ct\<rangle>" |
"rcom_tree_in_the_end \<langle>ct1,rIftag b, ct2\<rangle> ct = \<langle>rcom_tree_in_the_end ct1 ct,rIftag b, rcom_tree_in_the_end ct2 ct\<rangle>" |
"rcom_tree_in_the_end \<langle>\<langle>\<rangle>,c,\<langle>\<rangle>\<rangle> ct = \<langle>\<langle>\<langle>\<rangle>,c,\<langle>\<rangle>\<rangle>,rSeqtag, ct\<rangle>"|
"rcom_tree_in_the_end _ ct = \<langle>\<langle>\<rangle>,rSKIPtag,\<langle>\<rangle>\<rangle>" 


end
