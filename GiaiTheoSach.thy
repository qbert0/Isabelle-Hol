theory GiaiTheoSach
  imports Main
begin

(* --- 1. KHAI BÁO CÁC LUẬT (Dựa trên ảnh của bạn) --- *)
lemma inclusion_def: "(a \<longrightarrow> b) = (\<not>a \<or> b)" by auto
lemma duality_and:   "\<not>(a \<and> b) = (\<not>a \<or> \<not>b)" by auto
lemma double_neg:    "\<not>\<not>a = a" by auto
lemma excluded_middle: "a \<or> \<not>a = True" by auto
lemma Base_laws_or:  "a \<or> True = True" by auto

(* --- 2. LỜI GIẢI CHUẨN ISAR (Theo Concrete Semantics) --- *)
lemma cau1: "\<not>(a \<and> (a \<or> b))"
 
  apply (subst duality_and ) 
  
  (* Bước 3: Khử phủ định kép *)
  apply (subst double_neg)
  
  (* Bước 4: Sắp xếp lại. Dùng simp để tự động đảo chỗ *)
  apply (simp add: ac_simps) 
  
  (* Bước 5: Bài trung *)
  apply (subst excluded_middle)
  
  (* Bước 6: Luật Base *)
  apply (simp add: Base_laws)
  
  (* Kết thúc *)
  done
end