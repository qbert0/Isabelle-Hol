theory TestRivList
  imports BinaryLaws_Images
   Main
begin

(* CÂU 1: a \<and> \<not>b \<longrightarrow> a \<or> b *)
lemma cau1: "a \<and> \<not>b \<longrightarrow> a \<or> b"
  apply (subst inclusion_def)
  apply (subst duality_and )
  apply (subst double_neg)
  apply (simp add:  assoc_or)
  done

(* CÂU 2: ((a \<longrightarrow> b) \<longrightarrow> a) = a  *)
lemma cau2: "((a \<longrightarrow> b) \<longrightarrow> a) = a"
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (subst duality_or)
  apply (subst double_neg)
  apply (simp add: comm_or)
  apply (subst absorption)
  apply (rule refl)
done

(* CÂU 3: a \<and> \<not>a \<Longrightarrow> b (Mâu thuẫn suy ra tất cả) *)
lemma cau3: "a \<and> \<not>a \<longrightarrow> b"
  apply (subst inclusion_def)
  apply (subst noncontradiction)
  apply (simp add: comm_or Base_laws)
  done

(* CÂU 4: (a \<longrightarrow> b) \<or> (b \<longrightarrow> a) *)
lemma cau4: "(a \<longrightarrow> b) \<or> (b \<longrightarrow> a)"
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (simp add:  ac_simps) 
  done


(* CÂU 5: \<not>(a \<and> \<not>(a \<or> b)) *)
lemma cau5: "\<not>(a \<and> \<not>(a \<or> b))"
  apply (subst duality_or)
  apply (simp add: comm_or )
  done

(* CÂU 6: a = b \<or> a = c \<or> b = c (Nguyên lý chuồng bồ câu) *)
lemma cau6:
  fixes a b c :: bool
  shows "a = b \<or> a = c \<or> b = c"

  by (cases a; cases b; cases c) auto

(* CÂU 7: (a \<longrightarrow> \<not>a) \<longrightarrow> \<not>a *)
lemma cau7: "(a \<longrightarrow> \<not>a) \<longrightarrow> \<not>a"
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (simp)
  done

(* CÂU 8: ((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> b)) = b *)
lemma cau8: "((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> b)) = b"
(*   apply (subst inclusion_def)*)
(*   apply (subst inclusion_def)*)
(*   apply (subst double_neg)*)
(*  apply (subst comm_or)*)
(* apply (subst (2) comm_or)*)

apply (simp)
  done

(* CÂU 9: a \<longrightarrow> (b \<longrightarrow> a) *)
lemma cau9: "a \<longrightarrow> (b \<longrightarrow> a)"
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (simp add: ac_simps)
  done

lemma cau11: "((a \<and> b) \<or> (a \<and> \<not>b)) = a"
  apply (subst distributive_and_or3)
  apply (subst excluded_middle)
  apply (simp)
  done
  

(* Question 12 *)
lemma cau12: "((a \<longrightarrow> a \<and> b) = (a \<longrightarrow> b)) \<and> ((a \<longrightarrow> b) = (a \<or> b \<longrightarrow> b))"
 apply (simp)
  done

(* Question 13 *)
lemma cau13: "((\<not>a \<longrightarrow> \<not>b) \<and> (a \<noteq> b)) \<or> (a \<and> c \<longrightarrow> b \<and> c)"
  apply (subst inclusion_def)
  apply (subst difference_def)
  apply (subst inclusion_def)
  apply simp
  done

(* Question 14 *)
lemma cau14: "(a \<longrightarrow> a \<and> b) \<or> (b \<longrightarrow> a \<and> b)"
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (subst distributive_and_or2)
  apply simp
  done                                  

(* Question 15 *)
lemma cau15: "(a \<longrightarrow> b) \<and> (c \<longrightarrow> d) \<and> (a \<or> c) \<longrightarrow> (b \<or> d)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule disjE)
   apply (rule disjI1)
   apply (drule mp) apply assumption+            
  apply (rule disjI2)
  apply (simp)
  done

(* Question 16 *)
lemma cau16: "(a \<longrightarrow> b \<longrightarrow> \<not>a) \<or> (b \<and> c \<longrightarrow> a \<and> c)"
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (subst inclusion_def)
  apply (subst duality_and)
  apply (simp)
  done

end
