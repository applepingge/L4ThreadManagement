theory L4_Basic_Lemmas
  imports "L4_Inv_Def"
begin
lemma elim_assm':"Q \<Longrightarrow> (P \<Longrightarrow> Q)"
  by simp

lemma elim_assm:"Q \<Longrightarrow> P \<longrightarrow> Q"
  by simp

lemma elim_assms1:"A \<longrightarrow> C \<Longrightarrow> A \<and> B \<longrightarrow> C"
  by simp

lemma elim_assms2:"B \<longrightarrow> C \<Longrightarrow> A \<and> B \<longrightarrow> C"
  by simp
  thm if_split
lemma elim_if_and_pre:"\<lbrakk>P x;P y\<rbrakk> \<Longrightarrow> P (if (Q) then (x) else (y))"
  by simp

lemma elim_if:"(Q \<Longrightarrow> P x) \<Longrightarrow> (\<not>Q \<Longrightarrow> P y) \<Longrightarrow> P (if Q then x else y)"
  by simp

lemma elim_if_in_pre:"(a \<and> P b \<Longrightarrow> Q) \<Longrightarrow> (\<not>a \<and> P c \<Longrightarrow> Q) \<Longrightarrow> P (if a then b else c) \<Longrightarrow> Q"
  by presburger

thm option.case
thm option.case_eq_if[no_vars]
thm prod.case_eq_if[no_vars]
thm if_split[no_vars]
thm option.the_def
not_None_eq
not_Some_eq

lemma elim_case_option:
"(option = None \<Longrightarrow> P f1) \<Longrightarrow> ((option \<noteq> None) \<Longrightarrow> P (f2 (the option))) \<Longrightarrow> P (case option of None \<Rightarrow> f1 | Some x \<Rightarrow> f2 x)"
  by (auto simp:option.case_eq_if)

lemma elim_case_option_ex:
"(option = None \<Longrightarrow> P f1) \<Longrightarrow> (\<And>x. (option = Some x) \<Longrightarrow> P (f2 (the option))) \<Longrightarrow> P (case option of None \<Rightarrow> f1 | Some x \<Rightarrow> f2 x)"
  by (auto simp:option.case_eq_if)

lemma elim_case_prod:
"(option = None \<Longrightarrow> P f1) \<Longrightarrow> ((option \<noteq> None) \<Longrightarrow> P (f2 (fst (the option)) (snd (the option)))) \<Longrightarrow> P (case option of None \<Rightarrow> f1 | Some (a1,a2) \<Rightarrow> f2 a1 a2)"
  by (auto simp:option.case_eq_if)

lemma if_respect_eq:"(P s1 = P s) \<Longrightarrow>(P s2 = P s) \<Longrightarrow> P (if p then s1 else s2) = P s"
  by simp

lemma if_respect_eq_imply:"(p \<Longrightarrow> P s1 = P s) \<Longrightarrow>(\<not>p \<Longrightarrow> P s2 = P s) \<Longrightarrow> P (if p then s1 else s2) = P s"
  by simp

lemma if_respect_vpeq:"(P s1 s) \<Longrightarrow>(P s2 s) \<Longrightarrow> P (if p then s1 else s2) s"
  by simp

lemma if_respect_vpeq_imply:"(p \<Longrightarrow> P s1 s) \<Longrightarrow>(\<not>p \<Longrightarrow> P s2 s) \<Longrightarrow> P (if p then s1 else s2) s"
  by simp

lemma if_step_eq:"p1 = p2 \<Longrightarrow> P s1 = P t1 \<Longrightarrow> P s2 = P t2 \<Longrightarrow> 
      P (if p1 then s1 else s2) = P (if p2 then t1 else t2)"
  by simp

lemma if_step_eq_imply:"p1 = p2 \<Longrightarrow> (p1 \<Longrightarrow> P s1 = P t1) \<Longrightarrow> (\<not>p1 \<Longrightarrow>P s2 = P t2) \<Longrightarrow> 
      P (if p1 then s1 else s2) = P (if p2 then t1 else t2)"
  by simp

lemma if_step_vpeq:"p1 = p2 \<Longrightarrow> P s1 t1 \<Longrightarrow> P s2 t2 \<Longrightarrow> 
      P (if p1 then s1 else s2) (if p2 then t1 else t2)"
  by simp

lemma if_step_vpeq_imply:"p1 = p2 \<Longrightarrow> (p1 \<Longrightarrow> P s1 t1) \<Longrightarrow> (\<not>p1 \<Longrightarrow> P s2 t2) \<Longrightarrow> 
      P (if p1 then s1 else s2) (if p2 then t1 else t2)"
  by simp

lemma let_respect_eq:"P (f s) = P s \<Longrightarrow>(\<And>t. P (g t) = P t) \<Longrightarrow> P (let s1 = f s in g s1) = P s"
  by simp

lemma let_step_eq:"P s = P t \<Longrightarrow> (\<And> s t. P s = P t \<Longrightarrow> P (f s) = P (f t)) \<Longrightarrow> P (Let s f) = P (Let t f)"
  unfolding Let_def
  by blast

lemma let_step_vpeq:"P s t \<Longrightarrow> (\<And> s t. P s t \<Longrightarrow> P (f s) (f t)) \<Longrightarrow> P (Let s f) (Let t f)"
  by simp

lemma if_vpeq_memory:"p1 = p2 \<Longrightarrow> vpeq_memory s1 d t1 \<Longrightarrow> vpeq_memory s2 d t2 \<Longrightarrow>
vpeq_memory (if p1 then s1 else s2) d (if p2 then t1 else t2)"
  by simp

lemma if_vpeq_memory_imply:"p1 = p2 \<Longrightarrow> p1 \<longrightarrow> vpeq_memory s1 d t1 \<Longrightarrow> \<not>p1 \<longrightarrow> vpeq_memory s2 d t2 \<Longrightarrow>
vpeq_memory (if p1 then s1 else s2) d (if p2 then t1 else t2)"
  by simp

lemma let_vpeq_memory:"vpeq_memory s d t \<Longrightarrow> \<forall>s t. vpeq_memory s d t \<longrightarrow> vpeq_memory (f s) d (f t) \<Longrightarrow>
vpeq_memory (Let s f) d (Let t f)"
  unfolding Let_def
  by auto
end