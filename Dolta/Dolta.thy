theory Dolta
  imports Main
begin

lemma dolta:
  fixes P W R :: bool
  assumes H1: "\<not> P \<longrightarrow> W"
      and H2: "\<not> W \<longrightarrow> R"
      and liveness: "P \<or> W \<or> R" 
      and satifies: "(P \<longrightarrow> \<not>W \<and> \<not>R) \<and> (W \<longrightarrow> \<not>P \<and> \<not>R) \<and> (R \<longrightarrow> \<not>P \<and> \<not>W)"
  shows "\<not> R" 
proof (rule notI)
  assume "R"
  from satifies have s1: "(W \<longrightarrow> \<not>P \<and> \<not>R) \<and> (R \<longrightarrow> \<not>P \<and> \<not>W)"  by (rule conjunct2)
  from s1 have s2: "(R \<longrightarrow> \<not>P \<and> \<not>W)" by (rule conjunct2)
  from s2 \<open>R\<close> have s3: "\<not>P \<and> \<not>W" by (rule mp) 
  from s3 have "\<not>P" by (rule conjunct1)
  from s3 have "\<not>W" by (rule conjunct2)
  from H1 \<open>\<not>P\<close> have "W" by (rule mp)
  from \<open>\<not>W\<close> \<open>W\<close> show "False" by (rule notE)
qed

lemma dolta1:
  fixes P W R :: bool
  assumes H1: "\<not> P \<longrightarrow> W"
      and H2: "\<not> W \<longrightarrow> R"
      and liveness: "P \<or> W \<or> R" 
      and satifies: "(P \<longrightarrow> \<not>W \<and> \<not>R) \<and> (W \<longrightarrow> \<not>P \<and> \<not>R) \<and> (R \<longrightarrow> \<not>P \<and> \<not>W)"
    shows "W"
proof (rule ccontr)
  assume "\<not>W"
  from satifies have s1: "(W \<longrightarrow> \<not>P \<and> \<not>R) \<and> (R \<longrightarrow> \<not>P \<and> \<not>W)"  by (rule conjunct2)
  from s1 have s2: "(R \<longrightarrow> \<not>P \<and> \<not>W)" by (rule conjunct2)
  from H2 \<open>\<not>W\<close> have "R" by (rule mp) 
  from s2 \<open>R\<close> have s3: " \<not>P \<and> \<not>W" by (rule mp)
  from s3 have "\<not>P" by (rule conjunct1)
  from H1 \<open>\<not>P\<close> have "W" by (rule mp)
  from \<open>\<not>W\<close> \<open>W\<close> show "False" by (rule notE)
qed
  
  
  
 
  
 
