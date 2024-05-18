theory Nat_Dom_Lifted
  imports  "~~/src/HOL/Library/Simps_Case_Conv"
begin

definition Plus_lifted :: "('a \<Rightarrow> ('b :: plus)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
 "Plus_lifted f g = (\<lambda>x. (f x) + (g x))"

definition Suc_lifted :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat)" where
 "Suc_lifted f = (\<lambda>x. Suc (f x))"
                                          
definition times_lifted :: "('a \<Rightarrow> ('b :: times)) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
 "times_lifted f g = (\<lambda>x. (f x) * (g x))"

lemma equality_lifted: "(\<lambda>x. y) = (\<lambda>x. z) \<longleftrightarrow> y = z"
  by metis

lemma add_left_cancel_lifted: "(\<lambda>x. (a :: 'a \<Rightarrow> nat) x + b x) = (\<lambda>x. a x + c x) \<longleftrightarrow> b = c"
proof
  assume "(\<lambda>x. a x + b x) = (\<lambda>x. a x + c x)" show "b = c"
  proof(rule ccontr)
    assume "b \<noteq> c"
    have "(\<lambda>x. b x) \<noteq> (\<lambda>x. c x)"
      by (simp add: \<open>b \<noteq> c\<close>)
    hence "(\<lambda>x. a x + b x) \<noteq> (\<lambda>x. a x + c x)"
      by (meson add_left_cancel)
    thus False 
      by (simp add: \<open>(\<lambda>x. a x + b x) = (\<lambda>x. a x + c x)\<close>)
  qed
next 
  assume "b = c" show "(\<lambda>x. a x + b x) = (\<lambda>x. a x + c x)"
    by (simp add: \<open>b = c\<close>)
qed

lemma add_right_cancel_lifted: "(\<lambda>x. (a :: 'a \<Rightarrow> nat) x + c x) = (\<lambda>x. b x + c x) \<longleftrightarrow> a = b"
proof
  assume "(\<lambda>x. a x + c x) = (\<lambda>x. b x + c x) " show "a = b"
  proof(rule ccontr)
    assume "a \<noteq> b"
    have "(\<lambda>x. a x) \<noteq> (\<lambda>x. b x)"
      by (simp add: \<open>a \<noteq> b\<close>)
    hence "(\<lambda>x. a x + c x) \<noteq> (\<lambda>x. b x + c x)"
      by (metis add.commute add_left_cancel)
    thus False 
      by (simp add: \<open>(\<lambda>x. a x + c x) = (\<lambda>x. b x + c x)\<close>)
  qed
next 
  assume "a = b" show "(\<lambda>x. a x + c x) = (\<lambda>x. b x + c x)"
    by (simp add: \<open>a = b\<close>)
qed

lemma Suc_inject_lifted: "(\<lambda>x. Suc (y x)) = (\<lambda>x. Suc (z x)) \<longleftrightarrow> y = z"
proof
  assume "(\<lambda>x. Suc (y x)) = (\<lambda>x. Suc (z x))" show "y = z"
  proof(rule ccontr)
    assume "y \<noteq> z"
    have "(\<lambda>x. y x) \<noteq> (\<lambda>x. z x)"
      by (simp add: \<open>y \<noteq> z\<close>)
    hence "(\<lambda>x. Suc (y x)) \<noteq> (\<lambda>x. Suc (z x))"
      by (meson nat.inject)
    thus False 
      by (simp add: \<open>(\<lambda>x. Suc (y x)) = (\<lambda>x. Suc (z x))\<close>)
  qed
next 
  assume "y = z" show "(\<lambda>x. Suc (y x)) = (\<lambda>x. Suc (z x))"
    by (simp add: \<open>y = z\<close>)
qed

lemma add_diff_cancel_right'_lifted [simp]: "(\<lambda>x. ((a :: 'a \<Rightarrow> nat) x + b x) - b x) = (\<lambda>x. a x)"
  by simp

end