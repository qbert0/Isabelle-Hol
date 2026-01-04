theory BinaryLaws_Images
  imports Main
begin

section ‹PHẦN 1: CÁC LUẬT CƠ BẢN (Từ ảnh fd241b.png)›

text ‹--- Binary & Base ---›
lemma Binary_constants: "(True ≠ False)" by auto

lemma Base_laws:
  "(¬(a ∧ False)) = True"      (* Đã bọc ngoặc ngoài cùng cho vế trái *)
  "(a ∨ True) = True"          
  "(a ⟶ True) = True"      
  "(False ⟶ a) = True"     
  by auto

text ‹--- Excluded Middle & Noncontradiction ---›
lemma excluded_middle: "(a ∨ ¬a) = True" by auto (* Viết rõ = True cho chuẩn *)
lemma noncontradiction: "(¬(a ∧ ¬a)) = True" by auto (* Hoặc định nghĩa là mệnh đề đúng *)

text ‹--- Duality (De Morgan) ---›
(* Đã thêm ngoặc bảo vệ như bạn yêu cầu *)
lemma duality_and: "(¬(a ∧ b)) = (¬a ∨ ¬b)" by auto
lemma duality_or:  "(¬(a ∨ b)) = (¬a ∧ ¬b)" by auto

text ‹--- Double Negation ---›
lemma double_neg: "(¬¬a) = a" by auto

text ‹--- Inclusion (Material Implication) ---›
lemma inclusion_def: "(a ⟶ b) = (¬a ∨ b)" by auto
lemma inclusion_eq:  "(a ⟶ b) = ((a ∧ b) = a)" by auto

section ‹PHẦN 2: CÁC LUẬT CẤU TRÚC (Từ ảnh fd243b.png)›

text ‹--- Identity & Idempotent ---›
lemma identity_laws:
  "(True ∧ a) = a"
  "(False ∨ a) = a"
  "(True ⟶ a) = a"
  "(True = a) = a"
  by auto

lemma idempotent_laws:
  "(a ∧ a) = a"
  "(a ∨ a) = a"
  by auto

text ‹--- Absorption ---›
lemma absorption:
  "(a ∧ (a ∨ b)) = a"
  "(a ∨ (a ∧ b)) = a"
  by auto

text ‹--- Antisymmetry (Double Implication) ---›
lemma antisymmetry: "((a ⟶ b) ∧ (b ⟶ a)) = (a = b)" by auto

text ‹--- Discharge (Xả nén) ---›
lemma discharge:
  "(a ∧ (a ⟶ b)) = (a ∧ b)"
  "(a ⟶ (a ∧ b)) = (a ⟶ b)"
  by auto

text ‹--- Distributive (Phân phối) ---›
lemma distributive_and_or1:
  "(a ∧ (b ∨ c)) = ((a ∧ b) ∨ (a ∧ c))"
  by auto

lemma distributive_and_or2:
  "(a ∨ (b ∧ c)) = ((a ∨ b) ∧ (a ∨ c))"
  by auto

lemma distributive_and_or3:
  "(a ∧ b ∨ a ∧ c) = (a ∧ (b ∨ c))"
  by auto

lemma distributive_and_or4:
  "(((b ∨ a) ∧ (c ∨ a))) = (a ∨ b ∧ c)"
  by auto

lemma distributive_imply:
  "(a ⟶ (b ∧ c)) = ((a ⟶ b) ∧ (a ⟶ c))"
  "(a ⟶ (b ∨ c)) = ((a ⟶ b) ∨ (a ⟶ c))" 
  by auto

text ‹--- Portation (Chuyển vế) ---›
lemma portation:
  "((a ∧ b) ⟶ c) = (a ⟶ (b ⟶ c))" (* Bọc (a ∧ b) cho chắc chắn *)
  by auto

text ‹--- Equality and Difference ---›
lemma equality_def: "(a = b) = ((a ∧ b) ∨ (¬a ∧ ¬b))" by auto
lemma difference_def: "(a ≠ b) = ((a ∧ ¬b) ∨ (¬a ∧ b))" by auto


section ‹PHẦN 3: CÁC LUẬT VỀ CASE ANALYSIS (Từ ảnh fd2134.png)›

text ‹--- Case Analysis Definition ---›
lemma case_analysis_def:
  "(if a then b else c) = ((a ∧ b) ∨ (¬a ∧ c))"
  by auto

lemma case_analysis_imply_def:
  "(if a then b else c) = ((a ⟶ b) ∧ (¬a ⟶ c))"
  by auto

text ‹--- One Case (Trường hợp đặc biệt) ---›
lemma one_case_true:  "(if a then True else b) = (a ∨ b)" by auto
lemma one_case_false: "(if a then False else b) = (¬a ∧ b)" by auto

text ‹--- Case Distributive (Phân phối qua if) ---›
(* Luật này rất cần ngoặc vì có phủ định ở đầu *)
lemma case_dist_not: 
  "(¬(if a then b else c)) = (if a then ¬b else ¬c)" 
  by auto

lemma case_dist_and: 
  "((if a then b else c) ∧ d) = (if a then (b ∧ d) else (c ∧ d))" 
  by auto

text ‹--- Case Creation (Tạo case) ---›
lemma case_creation:
  "a = (if b then (b ⟶ a) else (¬b ⟶ a))"
  
  sledgehammer

text ‹--- Resolution (Luật phân giải) ---›
(* Bọc toàn bộ biểu thức vì đây là phép suy diễn, không phải đẳng thức *)
lemma resolution:
  "(((a ∨ b) ∧ (¬b ∨ c)) ⟶ (a ∨ c))"
  by auto
  
(* BỔ SUNG: Luật giao hoán và kết hợp để dùng cho lệnh simp *)
lemma comm_or: "(a ∨ b) = (b ∨ a)" by auto
lemma assoc_or: "((a ∨ b) ∨ c) = (a ∨ (b ∨ c))" by auto

end