theory Stack_Coms_Proof
  imports Upto_Rec_Rest_Proof "Tail_Recursive_IMP_Stack/TRec_Upto" "Tail_Recursive_IMP_Stack/Stack_Memory"
begin

text \<open>General recursive call with return point\<close>
lemma stack_pushed: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) 
                      \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (ut \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',Some i,True)
                      \<Longrightarrow> \<turnstile>UPTO\<lparr> (#\<lbrakk> \<lblot> (ut \<diamondop>Ret n) \<mapsto>\<^sub>#TREC STACK vs PC pc TRP trp \<rblot> \<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',b)
                      \<Longrightarrow> stack' = push_many_stack stack (s'(pc := i)) (pc#vs)"
  sorry

lemma pc_rec_return_point: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) 
                      \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (ut \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',Some i,True)
                      \<Longrightarrow> \<turnstile>UPTO\<lparr> (#\<lbrakk> \<lblot> (ut \<diamondop>Ret n) \<mapsto>\<^sub>#TREC STACK vs PC pc TRP trp \<rblot> \<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',b)
                      \<Longrightarrow> hd (stack' pc) = i"
  sorry


text \<open>Tail recursive call returning to termination point\<close>
lemma pc_tc_rp: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) 
                      \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (ut \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',None,True)
                      \<Longrightarrow> \<turnstile>UPTO\<lparr> (#\<lbrakk>\<lblot> (ut \<diamondop>Ret n) \<mapsto>\<^sub>#TREC STACK vs PC pc TRP trp \<rblot>\<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',b)
                      \<Longrightarrow> hd (stack' pc) = trp"
  sorry

text \<open>Recursive calls recurse from program start\<close>
lemma pr_rec: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) 
                      \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (ut \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',i,True)
                      \<Longrightarrow> \<turnstile>UPTO\<lparr> (#\<lbrakk>\<lblot> (ut \<diamondop>Ret n) \<mapsto>\<^sub>#TREC STACK vs PC pc TRP trp \<rblot>\<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',b)
                      \<Longrightarrow> s' pc = 1"
  sorry

text \<open>Stack is popped at termination points\<close>
lemma stack_popped: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) 
                      \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (ut \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',None,False)
                      \<Longrightarrow> \<turnstile>UPTO\<lparr> (#\<lbrakk>\<lblot> (ut \<diamondop>Ret n) \<mapsto>\<^sub>#TREC STACK vs PC pc TRP trp \<rblot>\<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',b)
                      \<Longrightarrow> stack' = pop_many_stack stack (pc#vs)"
  sorry

lemma pc_popped: "(UPTO\<lbrakk> c \<rbrakk> n \<Zsurj> False) = (ut,rest) 
                      \<Longrightarrow> c' \<turnstile>Rec\<rightharpoonup>i (ut \<diamondop>Ret n,s,ret)  \<Rightarrow>\<^bsup>x\<^esup> (s',None,False)
                      \<Longrightarrow> \<turnstile>UPTO\<lparr> (#\<lbrakk>\<lblot> (ut \<diamondop>Ret n) \<mapsto>\<^sub>#TREC STACK vs PC pc TRP trp \<rblot>\<rbrakk>\<inverse>,s,stack) \<Rightarrow>\<^bsup>t\<^esup> (s',stack',b)
                      \<Longrightarrow> s' pc = hd (stack pc)"
  sorry

end