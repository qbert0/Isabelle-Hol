theory TestRivList
   imports Main
begin

(* CÂU 1: a \<and> \<not>b \<longrightarrow> a \<or> b *)
lemma cau1: "a \<and> \<not>b \<longrightarrow> a \<or> b"
proof (rule impI)
  assume H: "a \<and> \<not>b"
  from H have "a"  by (rule conjunct1)
  from \<open>a\<close> show "a \<or> b"  by (rule disjI1)
qed


(* CÂU 2: ((a \<longrightarrow> b) \<longrightarrow> a) = a  *)
lemma cau2: "((a \<longrightarrow> b) \<longrightarrow> a) = a" (is "?L = ?R")
proof (rule iffI)
  assume a1: "?L"
  show "a"
  proof (rule ccontr)
    assume nota : " \<not>a"
    have "a\<longrightarrow>b" proof (rule impI) assume "a" from nota \<open>a\<close> show "b" by (rule notE) qed
    from a1 \<open>a\<longrightarrow>b\<close>  have "a" by (rule mp)
    from nota \<open>a\<close> show "False" by (rule notE) 
  qed
next
  assume a2: "?R"
  show "?L"
  proof (rule impI)
    assume a3 : "a\<longrightarrow>b"
    from a2 show "a" by assumption
  qed
qed

(* CÂU 3: a \<and> \<not>a \<Longrightarrow> b (Mâu thuẫn suy ra tất cả) *)
lemma cau3: "a \<and> \<not>a \<longrightarrow> b" (is "?L \<longrightarrow> ?R")
proof (rule impI)
  assume H: "?L"
  from H have "a" by (rule conjunct1)
  from H have "\<not>a" by (rule conjunct2)
  from \<open>\<not>a\<close> \<open>a\<close> show "b" by (rule notE)
qed

(* CÂU 4: (a \<longrightarrow> b) \<or> (b \<longrightarrow> a) *)
lemma cau4: "(a \<longrightarrow> b) \<or> (b \<longrightarrow> a)" (is "?L V ?R")
proof (rule disjCI)
  assume "\<not>(b\<longrightarrow>a)"
  show "a\<longrightarrow>b"
  proof (rule impI)
    assume "a"
    show "b"
    proof (rule ccontr)
      assume "\<not>b"
      have  "b\<longrightarrow>a" proof (rule impI) assume "b" from \<open>\<not>b\<close> \<open>b\<close> show "a" by (rule notE) qed
      from \<open>\<not>(b\<longrightarrow>a)\<close> \<open>b\<longrightarrow>a\<close> show "False" by (rule notE)
    qed 
  qed
qed



(* CÂU 5: \<not>(a \<and> \<not>(a \<or> b)) *)
lemma cau5: "\<not>(a \<and> \<not>(a \<or> b))" (is "\<not>?E")
proof (rule notI)
  assume ss: "?E"
  from ss have "a" by (rule conjunct1)
  from ss have 2: "\<not>(a \<or> b)" by (rule conjunct2)
  from \<open>a\<close> have 3: "a \<or> b" by (rule disjI1)
  from 2 3 show "False" by (rule notE)
qed


(* CÂU 6: a = b \<or> a = c \<or> b = c (Nguyên lý chuồng bồ câu) *)
lemma cau6:
  fixes a b c :: bool
  shows "a = b \<or> a = c \<or> b = c"

  by (cases a; cases b; cases c) auto

(* CÂU 7: (a \<longrightarrow> \<not>a) \<longrightarrow> \<not>a *)
lemma cau7: "(a \<longrightarrow> \<not>a) \<longrightarrow> \<not>a"
proof (rule impI)
  assume 1: "a\<longrightarrow>\<not>a"
  
  show "\<not>a"
  proof (rule notI) 
    assume "a"
    from 1 \<open>a\<close> have "\<not>a" by (rule mp)
    from \<open>\<not>a\<close> \<open>a\<close> show "False" by (rule notE)
  qed
qed

(* CÂU 8: ((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> b)) = b *)
lemma cau8: "((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> b)) = b" (is "?L = ?R")
proof (rule iffI)
  assume 1: "?L"
  from 1 have 2: "a\<longrightarrow> b" by (rule conjunct1)
  from 1 have 3: "\<not>a\<longrightarrow>b" by (rule conjunct2)
  show "b"
  proof (rule ccontr)
    assume sub1: "\<not>b"
    have "\<not>a" proof (rule notI) assume "a" 
      from 2 \<open>a\<close> have b1: "b" by (rule mp)
      from sub1 \<open>b\<close> show "False" by (rule notE)
    qed

    have "a" proof (rule ccontr) assume "\<not>a"
      from 3 \<open>\<not>a\<close> have b2: "b" by (rule mp)
      from sub1 \<open>b\<close> show "False" by (rule notE)
    qed
    from \<open>\<not>a\<close> \<open>a\<close> show "False" by (rule notE)
  qed 
next
  assume sub2: "?R"
  show "?L"
  proof (rule conjI)
    show "a\<longrightarrow>b" proof from sub2 show "b" by assumption qed
next 
  show "\<not>a\<longrightarrow>b" proof from sub2 show "b" by assumption qed
qed 
qed 



(* CÂU 9: a \<longrightarrow> (b \<longrightarrow> a) *)
lemma cau9: "a \<longrightarrow> (b \<longrightarrow> a)"
proof (rule impI)
  assume "a"
  show "b\<longrightarrow>a" 
  proof (rule impI) 
    from \<open>a\<close> show "a" by assumption qed
qed


lemma cau11: "((a \<and> b) \<or> (a \<and> \<not>b)) = a" (is "?L = ?R")
proof (rule iffI)
  assume l : "?L"
  from l show "a" proof (rule disjE)
    assume "a \<and> b"
    then show "a" by (rule conjunct1)
  next
    assume "a\<and>\<not>b" then show "a" by (rule conjunct1)
  qed
next
  assume r: "?R"
  show "?L"
  proof (rule ccontr)
    assume "\<not> (a \<and> b \<or> a \<and> \<not> b)"
  have "\<not> b"
  proof (rule notI)
    assume "b"
    from r \<open>b\<close> have "a \<and> b" by (rule conjI)
    hence "a \<and> b \<or> a \<and> \<not> b" by (rule disjI1)
    with \<open>\<not> (a \<and> b \<or> a \<and> \<not> b)\<close> show "False" by (rule notE)
  qed

  from \<open>a\<close> \<open>\<not> b\<close> have "a \<and> \<not> b" by (rule conjI)
  hence "a \<and> b \<or> a \<and> \<not> b" by (rule disjI2)
  with \<open>\<not> (a \<and> b \<or> a \<and> \<not> b)\<close> show "False" by (rule notE)
qed 
qed

  

(* Question 12 *)
lemma cau12: "((a \<longrightarrow> a \<and> b) = (a \<longrightarrow> b)) \<and> ((a \<longrightarrow> b) = (a \<or> b \<longrightarrow> b))"
proof (rule conjI)
  \<comment> \<open>Vế 1: (a \<longrightarrow> a \<and> b) = (a \<longrightarrow> b)\<close>
  show "(a \<longrightarrow> a \<and> b) = (a \<longrightarrow> b)"
  proof (rule iffI)
    assume "a \<longrightarrow> a \<and> b"
    show "a \<longrightarrow> b"
    proof (rule impI)
      assume "a"
      with \<open>a \<longrightarrow> a \<and> b\<close> have "a \<and> b" by (rule mp)
      thus "b" by (rule conjunct2)
    qed
  next
    assume "a \<longrightarrow> b"
    show "a \<longrightarrow> a \<and> b"
    proof (rule impI)
      assume "a"
      with \<open>a \<longrightarrow> b\<close> have "b" by (rule mp)
      with \<open>a\<close> show "a \<and> b" by (rule conjI)
    qed
  qed

next
  \<comment> \<open>Vế 2: (a \<longrightarrow> b) = (a \<or> b \<longrightarrow> b)\<close>
  show "(a \<longrightarrow> b) = (a \<or> b \<longrightarrow> b)"
  proof (rule iffI)
    assume "a \<longrightarrow> b"
    show "a \<or> b \<longrightarrow> b"
    proof (rule impI)
      assume "a \<or> b"
      thus "b"
      proof (rule disjE)
        assume "a"
        with \<open>a \<longrightarrow> b\<close> show "b" by (rule mp)
      next
        assume "b"
        thus "b" by assumption
      qed
    qed
  next
    assume "a \<or> b \<longrightarrow> b"
    show "a \<longrightarrow> b"
    proof (rule impI)
      assume "a"
      hence "a \<or> b" by (rule disjI1)
      with \<open>a \<or> b \<longrightarrow> b\<close> show "b" by (rule mp)
    qed
  qed
qed
 

(* Question 13 *)
lemma cau13: "((\<not>a \<longrightarrow> \<not>b) \<and> (a \<noteq> b)) \<or> (a \<and> c \<longrightarrow> b \<and> c)"
proof (rule disjCI)
  assume Not_R: "\<not> (a \<and> c \<longrightarrow> b \<and> c)"

  have A: "a" and C: "c" and NB: "\<not> b"
  proof -
    have "a \<and> c \<and> \<not> b"
    proof (rule ccontr)
      assume "\<not> (a \<and> c \<and> \<not> b)"
      hence "a \<and> c \<longrightarrow> b \<and> c" by auto
      with Not_R show False by (rule notE)
    qed
    thus "a" "c" "\<not> b" by auto
  qed

  show "(\<not> a \<longrightarrow> \<not> b) \<and> (a \<noteq> b)"
  proof (rule conjI)
    show "\<not> a \<longrightarrow> \<not> b"
    proof (rule impI)
      assume "\<not> a"
      from \<open>\<not>a\<close> \<open>a\<close> show "\<not> b" by (rule notE)
    qed
  next
    show "a \<noteq> b"
    proof (rule notI)
      assume "a = b"
      with \<open>a\<close> have "b" by simp
      with \<open>\<not> b\<close> show False by (rule notE)
    qed
  qed
qed

(* Question 14 *)
lemma cau14: "(a \<longrightarrow> a \<and> b) \<or> (b \<longrightarrow> a \<and> b)" (is "?L \<or> ?R")
proof (rule disjCI)
assume r: "\<not>?R"
  show "?L"
  proof (rule impI)
    assume "a"       
    show "a \<and> b"
    proof (rule ccontr)
      assume "\<not> (a \<and> b)"
      have "b \<longrightarrow> a \<and> b" proof (rule impI)  assume "b" from \<open>a\<close> \<open>b\<close> show "a \<and> b" by (rule conjI) qed
      from r \<open>b \<longrightarrow> a \<and> b\<close> show "False" by (rule notE)
    qed
  qed
qed

(* Question 15 *)
lemma cau15: "(a \<longrightarrow> b) \<and> (c \<longrightarrow> d) \<and> (a \<or> c) \<longrightarrow> (b \<or> d)"
proof (rule impI)
  assume H: "(a \<longrightarrow> b) \<and> (c \<longrightarrow> d) \<and> (a \<or> c)"
  from H have AB: "a \<longrightarrow> b" by (rule conjunct1)
  from H have CD_AC: "(c \<longrightarrow> d) \<and> (a \<or> c)" by (rule conjunct2)
  from CD_AC have CD: "c \<longrightarrow> d" by (rule conjunct1)
  from CD_AC have AC: "a \<or> c" by (rule conjunct2)

  from AC show "b \<or> d"
  proof (rule disjE)

  assume "a"
    from AB \<open>a\<close> have "b" by (rule mp)
    then show "b \<or> d" by (rule disjI1)

  next
  assume "c"
    from CD \<open>c\<close> have "d" by (rule mp)
    then show "b \<or> d" by (rule disjI2)
  qed
qed

(* Question 16 *)
lemma cau16: "(a \<longrightarrow> b \<longrightarrow> \<not>a) \<or> (b \<and> c \<longrightarrow> a \<and> c)" (is "?L \<or> ?R")
proof (rule disjCI)
  assume r: "\<not>?R"
  show "?L"
  proof (rule impI)
    assume "a"
    show "b \<longrightarrow> \<not>a"
    proof (rule impI)
      assume "b"
      have "b \<and> c \<longrightarrow> a \<and> c"
      proof (rule impI)
        assume "b \<and> c"
        hence "c" by (rule conjunct2)
        from \<open>a\<close> \<open>c\<close> show "a \<and> c" by (rule conjI)
      qed
      with r have "False" by (rule notE)
      thus "\<not>a" by (rule notI)
    qed
  qed
qed

end
