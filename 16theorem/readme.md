## 1. Cấu trúc của một bản chứng minh Isar

### A. Khai báo mục tiêu

- `lemma` / `theorem` Đưa ra mệnh đề cần chứng minh.

- `proof` Bắt đầu khối chứng minh.

- `proof (rule ...)` Áp dụng quy tắc _ngược_ (Backward reasoning) để chia nhỏ mục tiêu.

- `proof -` Không áp dụng quy tắc tự động nào, bắt đầu chứng minh thủ công.

---

### B. Thiết lập ngữ cảnh (Context)

- `assume` Đặt giả thuyết cho chứng minh.

- `fix`Khai báo các biến như `x`, `y` ( gán kiểu dữ liệu).

---

### C. Diễn tiến lập luận (Intermediate Steps)

- `have` Khẳng định một giả thuyết trung gian.

- `then` / `hence` Dùng giả thuyết vừa có ở dòng ngay phía trên cho dòng này.

- `from A B have` Chỉ định rõ dùng các giả thuyết `A` và `B` để suy ra bước tiếp theo.

- `with A have` Kết hợp giả thuyết dòng trước với giả thuyết `A`.

---

### D. Chia nhánh (Branching)

Dùng khi gặp dấu `∨` hoặc khi chứng minh tương đương:

- `next` Ngăn cách giữa các trường hợp (cases) hoặc các vế chứng minh. Lệnh này xóa bỏ các `assume` của nhánh trước để tránh nhầm lẫn.

---

### E. Chốt hạ mục tiêu (Conclusion)

- `show` Từ khóa quan trọng nhất: khẳng định rằng bước này khớp hoàn toàn với **Goal** hiện tại.

- `qed` Kết thúc khối chứng minh.

---

## 2. Phân biệt `rule`, `erule`, `drule` trong script (apply style)

Trong Isabelle, mỗi dấu logic ($\wedge, \vee, \longrightarrow, \neg, \longleftrightarrow$) luôn đi kèm với 2 nhóm quy tắc chính:

### `rule` : **Introduction Rule**

- Xây dựng: Tạo ra dấu logic mới.
- Áp dụng với mục tiêu

### `erule`: **Elimination Rule**

- Phá bỏ: Xử lý dấu logic từ giả thiết.
- Áp dụng với giả thuyết

### `drule`**Destruct Rule**

- Trích xuất: Lấy một phần từ giả thiết.
- Thường dùng để lấy nhanh dữ liệu từ dấu ^

## Bảng ký hiệu và luật suy diễn trong Logic

## Các luật suy diễn cơ bản trong Logic

| Dấu    | Tên luật                  | Introduction                                                       | Elimination / Destruction                          |
| ------ | ------------------------- | ------------------------------------------------------------------ | -------------------------------------------------- |
| ∧      | Conjunction (VÀ)          | **conjI**: Có `A`, `B` ⟹ `A ∧ B`                                   | **conjunct1**: lấy `A` <br> **conjunct2**: lấy `B` |
| ∨      | Disjunction (HOẶC)        | **disjI1**: `A` ⟹ `A ∨ B` <br> **disjI2**: `B` ⟹ `A ∨ B`           | **disjE**: Chia trường hợp (case analysis)         |
| ⟶      | Implication (KÉO THEO)    | **impI**: Giả sử vế trái, chứng minh vế phải                       | **mp** (Modus Ponens): Có `A ⟶ B` và `A` ⟹ `B`     |
| =      | Equivalence (TƯƠNG ĐƯƠNG) | **iffI**: Chứng minh hai chiều                                     | **iffD1**, **iffD2**: Thay A = B hoặc ngược lại    |
| ¬      | Negation (PHỦ ĐỊNH)       | **notI**: Giả sử `A`, dẫn đến `False`                              | **notE**: Có `A` và `¬A` ⟹ mâu thuẫn (`False`)     |
| ccontr | Phản chứng                | Giả sử `¬P`, chứng minh mâu thuẫn ⇒ `P` đúng                       |                                                    |
| disjCI | Classical ∨ Intro         | Giả sử vế phải sai (`¬Q`), chứng minh vế trái (`P`) đúng ⇒ `P ∨ Q` |                                                    |
