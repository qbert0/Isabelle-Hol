# Lý thuyết Hợp hàm (Function Composition)
## 1. Định nghĩa cơ bản
Hai hàm f và g, và nếu g không nằm trong miền xác định của f ( ¬ g: ☐f )., thì việc viết f g cạnh nhau được hiểu là hợp của hai hàm này.

### Tiên đề hợp hàm:
* **Miền xác định:** ☐(f g) = §x: ☐g· g x: ☐f
( miền của f g bằng nghiệm của phương trình 〈x:☐g · g x : ☐f 〉)
* **Ứng dụng:** (f g) x = f (g x)

## 2. Các quy tắc quan trọng
* **Lược bỏ dấu ngoặc:** Có thể bỏ dấu ngoặc giữa các hàm và giữ nguyên ví trí. (quy tắc *Polish prefix*).
* **Quy tắc phân phối:** Hợp hàm thỏa mãn tính phân phối khi áp dụng với các **Bunch**:
  - $f (g, h) = f g, f h$
  - $(f, g) h = f h, g h$

## 3. Toán tử và Định luật Đối ngẫu
| Công thức | ngữ nghĩa | 
| :--- | :---:|
| ¬∀f = ∃¬f | ~( a1 ^ … ^ an) = ( ~a1 V …V ~an) | 
| ¬∃f = ∀¬f | ~( a1 V … V an) = ( ~a1 ^ …^ ~an) | 
| –⇓f = ⇑–f |  | 
| –⇑f = ⇓–f | | 


## 4. Giới hạn và Số thực (Limits and Reals)

với f: nat→rat ta coi f 0; f 1; f 2; ... là các số hạng của dãy. ⇕f là giới hạn của hàm hay là giới hạn của dãy số tương ứng khi phần từ tiến tới vô cùng.

### Ví dụ điển hình
ví dụ: ⇕〈n: nat· (1 + 1/n)n〉 sẽ tiến tới e ( 2.718281828459) 

### Công thức xác định Giới hạn (Limit Axiom)
Giới hạn được xác định bằng cách kẹp giữa hai giá trị biên ổn định:

(⇑m· ⇓n· f (m+n)) ≤ ⇕f ≤ (⇓m· ⇑n· f (m+n))

**Phân tích cơ chế:**
* **Vế trái (Limit Inferior):** Giá trị lớn nhất trên chuỗi các giá trị nhỏ nhất của hàm số
* **Vế phải (Limit Superior):** Giá trị nhỏ nhất trên chuỗi các giá trị lớn nhất của hàm số

**Mục đích:** Tìm được giá trị biên ổn định. 


### Các tính chất đặc biệt
* **Tính đơn điệu:**
  - Nếu f không giảm (monotonic): ⇕f = ⇑f (Giới hạn bằng giá trị cực đại).
  - Nếu f không tăng (antimonotonic): ⇕f = ⇓f (Giới hạn bằng giá trị cực tiểu).
