theory TestRivList
  imports BinaryLaws_Images
   Main
begin

(* CÂU 1: a \<and> \<not>b \<longrightarrow> a \<or> b *)
lemma cau1: "a \<and> \<not>b \<longrightarrow> a \<or> b"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

(* CÂU 2: ((a \<longrightarrow> b) \<longrightarrow> a) = a  *)
lemma cau2: "((a \<longrightarrow> b) \<longrightarrow> a) = a"
  (* Dạng này là một tautology trong HOL cổ điển; dùng simp/auto *)
  by auto

(* CÂU 3: a \<and> \<not>a \<Longrightarrow> b (Mâu thuẫn suy ra tất cả) *)
lemma cau3: "a \<and> \<not>a \<longrightarrow> b"
  apply (rule impI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done

(* CÂU 4: (a \<longrightarrow> b) \<or> (b \<longrightarrow> a) *)
lemma cau4: "(a \<longrightarrow> b) \<or> (b \<longrightarrow> a)"
  (* Có thể chứng minh bằng excluded_middle và inclusion_def *)
  apply (simp)
  done


(* CÂU 5: \<not>(a \<and> \<not>(a \<or> b)) *)
lemma cau5: "\<not>(a \<and> \<not>(a \<or> b))"
  apply (simp)
  done

(* CÂU 6: a = b \<or> a = c \<or> b = c (Nguyên lý chuồng bồ câu) *)
lemma cau6:
  fixes a b c :: bool
  shows "a = b \<or> a = c \<or> b = c"

  by (cases a; cases b; cases c) auto

(* CÂU 7: (a \<longrightarrow> \<not>a) \<longrightarrow> \<not>a *)
lemma cau7: "(a \<longrightarrow> \<not>a) \<longrightarrow> \<not>a"
  apply (rule impI)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

(* CÂU 8: ((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> b)) = b *)
lemma cau8: "((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> b)) = b"
  (* Dùng luật phân tích implication inclusion_def + case on a,
     nhưng ta có thể chứng minh bằng equivalence antisymmetry và tính toàn cục *)
  apply (rule iffI)
   apply (erule conjE)
   apply (case_tac a)
    apply simp
   apply simp
  apply (rule conjI)
   apply (rule impI)
   apply assumption
  apply (rule impI)
  apply assumption
  done

(* CÂU 9: a \<longrightarrow> (b \<longrightarrow> a) *)
lemma cau9: "a \<longrightarrow> (b \<longrightarrow> a)"
  apply (rule impI)
  apply (rule impI)
  apply assumption
  done

lemma cau11: "(a \<and> b) \<or> (a \<and> \<not> b) = a"
  by auto
  

(* Question 12 *)
lemma cau12: "((a \<longrightarrow> a \<and> b) = (a \<longrightarrow> b)) \<and> ((a \<longrightarrow> b) = (a \<or> b \<longrightarrow> b))"
 apply (simp)
  done

(* Question 13 *)
lemma cau13: "((\<not>a \<longrightarrow> \<not>b) \<and> (a \<noteq> b)) \<or> (a \<and> c \<longrightarrow> b \<and> c)"
  (* Dùng case analysis theo a bằng tactic cases, nhưng không triển khai case_tac tay *)
  apply (simp)
  done

(* Question 14 *)
lemma cau14: "(a \<longrightarrow> a \<and> b) \<or> (b \<longrightarrow> a \<and> b)"         
  apply (simp)            
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
  apply (simp)
  done

end
