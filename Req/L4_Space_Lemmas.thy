theory L4_Space_Lemmas
  imports L4_State_Lemmas
begin

section\<open>basic lemmas\<close>
lemma basic1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>+z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z"
  apply(induction rule:tran_path.induct)
  using tran_path
  by auto

lemma basic11:"s\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>1z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z"
  apply(induction rule:rtran_path.induct)
  by(auto simp add:tran_path.intros)

lemma basic111:"s\<turnstile>y\<leadsto>\<^sup>*z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z"
  by (metis refl_tran rtran_tran tran_path.simps)

lemma basic12:"s\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>+z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z"
  apply(induction rule:rtran_path.induct)
  by(auto simp add:tran_path.intros)

lemma basic13:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>1z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z"
  apply(induction rule:tran_path.induct)
  by(auto simp add:tran_path.intros)

lemma basic14:"s\<turnstile>y\<leadsto>\<^sup>*z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z"
  apply(induction rule:rtran_path.induct)
  using basic13
  by(auto simp add:tran_path.intros)

lemma basic15:"s\<turnstile>x\<leadsto>\<^sup>+z \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>*z"
  apply (induction rule:tran_path.induct)
  using direct_path_def rtran_tran by auto

lemma basic16:"s\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z \<Longrightarrow> \<not>s\<turnstile>z\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>+z"
proof(induction rule:rtran_path.induct)
  case (refl_path x)
  then show ?case by simp
next
  case (refl_tran a b c)
  then have "s\<turnstile>b\<leadsto>\<^sup>+z"
    using basic15 rtran_tran by auto
  then show ?case using refl_tran by simp
qed

lemma basic17:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+z \<Longrightarrow> \<not>s\<turnstile>z\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>y\<leadsto>\<^sup>+z"
  using basic16 rtran_tran
  by auto

lemma basic2:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>+z \<Longrightarrow> \<not>s\<turnstile>y\<leadsto>\<^sup>+z"
  apply(rule ccontr)
  using basic1
  by blast

lemma basic3:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> \<exists>z. s\<turnstile>x\<leadsto>\<^sup>1z"
  apply(induction rule:tran_path.induct)
  by auto

lemma basic4:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow>\<not>s\<turnstile>x\<leadsto>\<^sup>*z \<Longrightarrow> \<not>s\<turnstile>y\<leadsto>\<^sup>*z"
  apply(subst rtran_tran)
  apply auto
  subgoal
    by (simp add: rtran_tran)
  using basic1 rtran_tran
  by blast

lemma basic41:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow>\<not>s\<turnstile>x\<leadsto>\<^sup>*z \<Longrightarrow> \<not>s\<turnstile>y\<leadsto>\<^sup>+z"
  apply(simp add:rtran_tran)
  apply rule
  using basic1
  by blast

lemma basic42:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow>\<not>s\<turnstile>x\<leadsto>\<^sup>+z \<Longrightarrow> \<not>s\<turnstile>y\<leadsto>\<^sup>*z"
  apply(simp add:rtran_tran)
  using basic1
  by blast

lemma basic5:"space_mapping s sp = Some mapping \<Longrightarrow> mapping v = None \<Longrightarrow>
 x = (Virtual sp v) \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>+y"
proof
  assume a1:"space_mapping s sp = Some mapping" and a2:"mapping v = None" and
    a3:"x = (Virtual sp v)" and a4:"s\<turnstile>x\<leadsto>\<^sup>+y"
  have h1:"\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y" using direct_path_def a1 a2 a3 by simp
  show False
    using a4 a1 a2 a3
    apply(induction rule:tran_path.induct)
    by (auto simp add: direct_path_def h1)
qed

lemma Space_Father_Is_Unique:"s \<turnstile> x \<leadsto>\<^sup>1 y1 \<and> s \<turnstile> x \<leadsto>\<^sup>1 y2 \<longrightarrow> y1 = y2"
  using direct_path_def
  by auto

lemma PlusEqOneStar:"s \<turnstile> x \<leadsto>\<^sup>+ z = (\<exists>y. s \<turnstile> x \<leadsto>\<^sup>1 y \<and> s \<turnstile> y \<leadsto>\<^sup>* z)"
  apply rule
  subgoal
    apply(induction rule:tran_path.induct)
    by(auto simp add:rtran_path.intros)
  using one_path rtran_tran tran_path by auto

lemma PlusEqOneStarVirtual:"space_mapping s sp \<noteq> None
\<Longrightarrow> the (space_mapping s sp) v \<noteq> None \<Longrightarrow>
s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ z = (s \<turnstile> (fst(the(the (space_mapping s sp) v))) \<leadsto>\<^sup>* z)"
proof-
  assume a1:"space_mapping s sp \<noteq> None" and a2:"the (space_mapping s sp) v \<noteq> None"
  have h1:"s\<turnstile>(Virtual sp v) \<leadsto>\<^sup>1(fst (the (the (space_mapping s sp) v)))"
    using a1 a2 direct_path_def by auto
  show ?thesis
  proof
    assume a11:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+z"
    then show "s\<turnstile>(fst (the (the (space_mapping s sp) v)))\<leadsto>\<^sup>*z"
      using basic15 a1 h1 by simp
  next
    assume a12:"s\<turnstile>(fst (the (the (space_mapping s sp) v)))\<leadsto>\<^sup>*z"
    then show "s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+z" using a1 basic111 h1 by simp
  qed
qed

lemma path_direct:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1) \<Longrightarrow> \<exists>y. s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>1y"
  using basic3 by simp

lemma path_valid:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1) \<Longrightarrow> s\<turnstile>(Virtual sp vpage)"
  using path_direct valid_page_def by simp

lemma path_space:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1) \<Longrightarrow> 
space_mapping s sp \<noteq> None \<and> the(space_mapping s sp) vpage \<noteq> None"
  using ValidVpageMappingNotNone path_valid by auto

lemma path_space1:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+y \<Longrightarrow> 
space_mapping s sp \<noteq> None \<and> the(space_mapping s sp) vpage \<noteq> None"
  using ValidVpageMappingNotNone path_valid
  by (meson FatherIsValid basic3)

section\<open>sys_unmap\<close>
subsection\<open>user\<close>
lemma sys_unmap_NC_User:
"thread_pager (sys_unmap s sp v perms) = thread_pager s \<and>
 thread_handler (sys_unmap s sp v perms) = thread_handler s \<and>
 thread_message (sys_unmap s sp v perms) = thread_message s \<and>
 thread_rcvWindow (sys_unmap s sp v perms) = thread_rcvWindow s \<and>
 thread_error (sys_unmap s sp v perms) = thread_error s"
  unfolding sys_unmap_def
  by auto

subsection\<open>current\<close>
lemma sys_unmap_NC_Current:
"current_thread (sys_unmap s sp v perms) = current_thread s \<and>
 current_time (sys_unmap s sp v perms) = current_time s"
  unfolding sys_unmap_def
  by auto

subsection\<open>thread\<close>
lemma sys_unmap_NC_Thread:
"threads (sys_unmap s sp v perms) = threads s \<and>
 active_threads (sys_unmap s sp v perms) = active_threads s \<and>
 thread_space (sys_unmap s sp v perms) = thread_space s \<and>
 thread_scheduler (sys_unmap s sp v perms) = thread_scheduler s \<and>
 thread_state (sys_unmap s sp v perms) = thread_state s \<and>
 thread_priority (sys_unmap s sp v perms) = thread_priority s \<and>
 thread_total_quantum (sys_unmap s sp v perms) = thread_total_quantum s \<and>
 thread_timeslice_length (sys_unmap s sp v perms) = thread_timeslice_length s \<and>
 thread_current_timeslice (sys_unmap s sp v perms) = thread_current_timeslice s"
  by(auto simp add:sys_unmap_def)

thm option.exhaust
thm elim_case_option[no_vars]

lemma elim_some:"y \<noteq> None \<Longrightarrow> x = the y \<Longrightarrow> Some x = y"
  by simp

subsection\<open>space\<close>
lemma sys_unmap_NC_Space:
"spaces (sys_unmap s sp v perms) = spaces s \<and>
 initialised_spaces (sys_unmap s sp v perms) = initialised_spaces s \<and>
 space_threads (sys_unmap s sp v perms) = space_threads s \<and>
 dom (space_mapping (sys_unmap s sp v perms)) = dom (space_mapping s)"
  apply(auto simp: sys_unmap_def spaces_def)
  apply(case_tac "space_mapping s x = None")
  by auto

lemma sys_unmap_NC_Space1:
"(space_mapping (sys_unmap s sp v perms) sp1 \<noteq> None) = (space_mapping s sp1 \<noteq> None)"
  by(auto simp: sys_unmap_def)

lemma sys_unmap_NC_Space2:
"(sp1 \<in> spaces (sys_unmap s sp v perms)) = (sp1 \<in> spaces s)"
  unfolding spaces_def sys_unmap_def dom_def
  by auto

subsubsection\<open>space_mapping\<close>
\<comment>\<open>unmap not in path\<close>
lemma sys_unmap_pre:"(sys_unmap s sp v perms)\<turnstile> x \<leadsto>\<^sup>1 y \<Longrightarrow> s \<turnstile> x\<leadsto>\<^sup>1 y"
  unfolding sys_unmap_def direct_path_def
  apply auto
  apply(case_tac "space_mapping s spa = None")
   apply auto
  apply (case_tac "ya va = None")
   apply auto
  apply(case_tac "s\<turnstile>(Virtual spa va)\<leadsto>\<^sup>+(Virtual sp v)")
   apply auto
  apply(case_tac "b \<subseteq> perms")
  by auto

lemma sys_unmap_valid:"(sys_unmap s sp v perms)\<turnstile>x \<Longrightarrow> s \<turnstile> x"
  apply(cases x)
  unfolding valid_page_def
  using sys_unmap_pre
   apply auto
  by blast

thm sys_unmap_def
lemma unmap_not_path_space:"\<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> space_mapping s sp1 \<noteq> None \<Longrightarrow>
the (space_mapping (sys_unmap s sp v perms) sp1) v1 = the (space_mapping s sp1) v1"
  unfolding sys_unmap_def 
  by auto

lemma unmap_not_path_direct:"\<not>s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow>
(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding sys_unmap_def direct_path_def
  apply (cases x)
  by auto

lemma unmap_not_path_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> 
\<not>s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then show ?case using unmap_not_path_direct tran_path.intros by simp
next
  case (tran_path x y z)
  then have "\<not> s\<turnstile>y\<leadsto>\<^sup>+(Virtual sp v)" using tran_path.intros by metis
  then have h1:"(sys_unmap s sp v perms)\<turnstile>y\<leadsto>\<^sup>+z" using tran_path by simp
  have "(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>1y" using tran_path unmap_not_path_direct by simp
  then show ?case using h1 tran_path.intros by simp
qed

lemma unmap_not_path_tran2:"(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> 
\<not>s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then show ?case using sys_unmap_pre tran_path.intros by blast
next
  case (tran_path x y z)
  then have h1:"s\<turnstile>x\<leadsto>\<^sup>1y" using sys_unmap_pre by simp
  then have "\<not> s\<turnstile>y\<leadsto>\<^sup>+(Virtual sp v)" using tran_path tran_path.intros by blast
  then have "s\<turnstile>y\<leadsto>\<^sup>+z" using tran_path by simp
  then show ?case using h1 tran_path.intros by simp
qed

lemma unmap_not_path_tran:"\<not>s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y = (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y"
  using unmap_not_path_tran1 unmap_not_path_tran2 
  by blast

\<comment> \<open>unmap in path\<close>
lemma unmap_path_space:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> get_perms s sp1 v1 \<subseteq> perms \<Longrightarrow>
the (space_mapping (sys_unmap s sp v perms) sp1) v1 = None"
  unfolding sys_unmap_def get_perms_def
  apply auto
  using path_space by simp

lemma unmap_path_tran:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> get_perms s sp1 v1 \<subseteq> perms \<Longrightarrow>
\<not>(sys_unmap s sp v perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+y"
  using unmap_path_space path_space1
  by blast

lemma unmap_path_tran_valid:"s \<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> 
get_perms s sp1 v1 \<subseteq> perms \<Longrightarrow> \<not>(sys_unmap s sp v perms)\<turnstile>(Virtual sp1 v1)"
  using unmap_path_space valid_page_def direct_path_def
  apply auto
  by (metis option.discI option.sel)

\<comment>\<open>unmap not enough perms\<close>
lemma unmap_preserve_direct:"s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>get_perms1 s x \<subseteq> perms \<Longrightarrow>
(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding sys_unmap_def
  apply(cases x)
  subgoal
    unfolding get_perms1_def direct_path_def
    by auto
  using SonIsNoReal by blast

lemma unmap_preserve_space:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ y \<Longrightarrow>
\<not>(get_perms s sp1 v1 \<subseteq> perms) \<Longrightarrow>
space_mapping (sys_unmap s sp v perms) sp1 \<noteq> None \<and>
the (space_mapping (sys_unmap s sp v perms) sp1) v1 \<noteq> None \<and>
fst(the (the (space_mapping (sys_unmap s sp v perms) sp1) v1)) = 
fst(the (the (space_mapping s sp1) v1))"
proof-
  assume a1:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ y" and 
        a2:"\<not>(get_perms s sp1 v1 \<subseteq> perms)"
  then have h1:"\<exists>y. s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>1 y" using basic3 by simp
  then have h2:"space_mapping s sp1 \<noteq> None \<and> the (space_mapping s sp1) v1 \<noteq> None"
    using direct_path_def by auto
  then show ?thesis
    unfolding sys_unmap_def using a2 get_perms_def by auto
qed

lemma unmap_preserve_tran:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ z \<Longrightarrow>
\<not>(get_perms s sp1 v1 \<subseteq> perms) \<Longrightarrow> s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>1 y \<Longrightarrow>
(sys_unmap s sp v perms) \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>1 y"
proof-
  assume a1:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ z" and
         a2:"\<not>get_perms s sp1 v1 \<subseteq> perms" and
         a3:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>1 y"
  have h3:"fst(the (the (space_mapping s sp1) v1)) = y" using a3 direct_path_def by auto
  then have "space_mapping (sys_unmap s sp v perms) sp1 \<noteq> None \<and>
    the (space_mapping (sys_unmap s sp v perms) sp1) v1 \<noteq> None \<and>
    fst(the (the (space_mapping (sys_unmap s sp v perms) sp1) v1)) = 
    fst(the (the (space_mapping s sp1) v1))"
    using unmap_preserve_space a1 a2 by simp
  then show ?thesis using direct_path_def h3 by auto
qed

lemma unmap_preserve_tran_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> \<not>get_perms1 s x \<subseteq> perms \<Longrightarrow> 
Inv_Space_Perms_Subset s \<Longrightarrow> (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then show ?case using unmap_preserve_direct tran_path.intros by simp 
next
  case (tran_path x y z)
  then obtain sp1 v1 sp2 v2 where h1:"x = Virtual sp1 v1 \<and> y = Virtual sp2 v2" 
    using basic3 FatherIsVirtual by meson
  then have h2:"get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" 
    using tran_path Inv_Space_Perms_Subset_def by blast
  have h3:"\<not> get_perms s sp1 v1 \<subseteq> perms" using h1 tran_path get_perms_auxi by simp
  then have "\<not> get_perms s sp2 v2 \<subseteq> perms" using h2 by blast
  then have "\<not> get_perms1 s y \<subseteq> perms" using h1 get_perms_auxi by simp
  then have h4:"(sys_unmap s sp v perms)\<turnstile>y\<leadsto>\<^sup>+z" using tran_path by simp
  have "s\<turnstile>x\<leadsto>\<^sup>+z" using tran_path tran_path.intros by simp
  then have "(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>1y" using tran_path unmap_preserve_tran h1 h3 by simp
  then show ?case using h4 tran_path.intros by simp
qed

lemma unmap_preserve_tran_tran2:"(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> \<not>get_perms1 s x \<subseteq> perms \<Longrightarrow> 
Inv_Space_Perms_Subset s \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then show ?case using sys_unmap_pre tran_path.intros by blast
next
  case (tran_path x y z)
  then obtain sp1 v1 sp2 v2 where h1:"x = Virtual sp1 v1 \<and> y = Virtual sp2 v2" 
    using basic3 FatherIsVirtual by meson
  have h2:"s\<turnstile>x\<leadsto>\<^sup>1y" using tran_path sys_unmap_pre by blast
  then have h3:"get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" 
    using h1 tran_path Inv_Space_Perms_Subset_def by blast
  have h4:"\<not> get_perms s sp1 v1 \<subseteq> perms" using h1 tran_path get_perms_auxi by simp
  then have "\<not> get_perms s sp2 v2 \<subseteq> perms" using h3 by blast
  then have "\<not> get_perms1 s y \<subseteq> perms" using h1 get_perms_auxi by simp
  then have "s\<turnstile>y\<leadsto>\<^sup>+z" using tran_path by simp
  then show ?case using h2 h4 tran_path.intros by simp
qed

lemma unmap_preserve_tran_tran:"\<not>get_perms1 s x \<subseteq> perms \<Longrightarrow> 
Inv_Space_Perms_Subset s \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y = (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y"
  using unmap_preserve_tran_tran1 unmap_preserve_tran_tran2
  by metis

lemma unmap_preserve_tran_tran':"\<not>get_perms s sp1 v1 \<subseteq> perms \<Longrightarrow> 
Inv_Space_Perms_Subset s \<Longrightarrow> s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+y = 
(sys_unmap s sp v perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+y"
  using unmap_preserve_tran_tran get_perms_auxi
  by metis

lemma unmap_preserve_perms_subset:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ (Virtual sp v) \<Longrightarrow>
\<not>(get_perms s sp1 v1 \<subseteq> perms) \<Longrightarrow> 
get_perms (sys_unmap s sp v perms) sp1 v1 = get_perms s sp1 v1 - perms"
proof-
  assume a1:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ (Virtual sp v)" and
         a2:"\<not>get_perms s sp1 v1 \<subseteq> perms"
  from a1 have h1:"\<exists>mapping. space_mapping s sp1 = Some mapping \<and> mapping v1 \<noteq> None \<and>
    snd(the(mapping v1)) = get_perms s sp1 v1"
    using FatherIsVirtual basic3 direct_def get_perms_def
    by (metis (mono_tags) ValidVpageHasSon ValidVpageMappingNotNone option.exhaust_sel)
  then obtain mapping where h2:"space_mapping s sp1 = Some mapping \<and> mapping v1 \<noteq> None \<and>
    snd(the(mapping v1)) = get_perms s sp1 v1" by auto
  have h6: "snd(the (the (space_mapping (sys_unmap s sp v perms) sp1) v1)) = 
    snd(the (the (space_mapping s sp1) v1))- perms"
    unfolding sys_unmap_def using h2 a2 a1 apply simp apply rule using h2 by simp
  then show h7: "get_perms (sys_unmap s sp v perms) sp1 v1 =
    get_perms s sp1 v1 - perms"
    unfolding get_perms_def by simp
qed

subsection\<open>IPC\<close>
lemma sys_unmap_NC_IPC:
"thread_ipc_partner (sys_unmap s sp v perms) = thread_ipc_partner s \<and>
 thread_ipc_timeout (sys_unmap s sp v perms) = thread_ipc_timeout s \<and>
 thread_incoming (sys_unmap s sp v perms) =  thread_incoming s"
  by(auto simp add:sys_unmap_def)

subsection\<open>scheduling\<close>
lemma sys_unmap_NC_Scheduling:
"wait_queuing (sys_unmap s sp v perms) = wait_queuing s \<and>
 ready_queuing (sys_unmap s sp v perms) = ready_queuing s \<and>
 current_timeslice (sys_unmap s sp v perms) = current_timeslice s"
  by(auto simp add:sys_unmap_def)

subsection\<open>Inv\<close>
subsubsection\<open>Current\<close>
lemma sys_unmap_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma sys_unmap_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma sys_unmap_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (sys_unmap s sp v perms)"
  using sys_unmap_Inv_Current_Thread_In_Active sys_unmap_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsubsection\<open>Space\<close>
lemma sys_unmap_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (sys_unmap s sp v perms)"
  unfolding Inv_Space_Spaces_In_Config_def spaces_def
  using p1[unfolded Inv_Space_Spaces_In_Config_def spaces_def]
  unfolding sys_unmap_def
  apply auto
  apply(case_tac "space_mapping s x = None")
  by auto

lemma sys_unmap_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (sys_unmap s sp v perms)"
  unfolding Inv_Space_Perms_IsNot_Empty_def
  apply auto
  unfolding sys_unmap_def get_perms_def valid_page_def direct_path_def Let_def
  apply auto
  apply(case_tac "space_mapping s spa = None")
  subgoal
    by auto
  apply auto
  apply(subgoal_tac "y v_page = Some (p2,{})")
  subgoal
    using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def valid_page_def direct_path_def]
    by fastforce
  unfolding Let_def
  apply(case_tac "y v_page = None")
   apply simp
  apply simp
  apply(case_tac "s\<turnstile>(Virtual spa v_page)\<leadsto>\<^sup>+(Virtual sp v)")
  apply auto
   apply(case_tac "b \<subseteq> perms")
  apply auto
  apply(case_tac "b \<subseteq> perms")
  by auto

lemma sys_unmap_Inv_Space_HasNot_Loop1:
  assumes a1:"Inv_Space_HasNot_Loop s"
      and a2:"(sys_unmap s sp v perms)\<turnstile> x\<leadsto>\<^sup>+ y"
      and a3:"x = (Virtual spa v1)"
      and a4:"y = (Virtual spa v2)"
    shows "False"
proof-
  from a2 have h1:"s\<turnstile>x\<leadsto>\<^sup>+y"
  proof(induction rule:tran_path.induct)
    case (one_path x y)
    then show ?case using sys_unmap_pre tran_path.intros
      by blast
  next
    case (tran_path x y z)
    then show ?case using sys_unmap_pre tran_path.intros
      by blast
  qed
  then show False using a3 a4 a1[unfolded Inv_Space_HasNot_Loop_def]
    by auto
qed

lemma sys_unmap_Inv_Space_HasNot_Loop:
  assumes a1:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (sys_unmap s sp v perms)"
  using a1 sys_unmap_Inv_Space_HasNot_Loop1 Inv_Space_HasNot_Loop_def
  by blast

lemma sys_unmap_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Perms_Subset (sys_unmap s sp v perms)"
proof-
  {
    fix sp1 sp2 v1 v2
    assume a1:"(sys_unmap s sp v perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    have h1:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
      using sys_unmap_pre a1 by simp
    have h2:"s\<turnstile>(Virtual sp2 v2)" using YIsValid h1 p2 p3 by simp
    have h3:"get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2"
      using h1 p1[unfolded Inv_Space_Perms_Subset_def] by simp
    have h4:"space_mapping s sp2 \<noteq> None" using h2 valid_page_def direct_path_def by auto
    have "s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) \<or> \<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v)" by simp
    then have "get_perms (sys_unmap s sp v perms) sp1 v1 \<subseteq> get_perms (sys_unmap s sp v perms) sp2 v2"
    proof
      assume a11:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v)"
      have h11:"\<not> get_perms s sp1 v1 \<subseteq> perms"
      proof
        assume "get_perms s sp1 v1 \<subseteq> perms"
        then have "\<not>(sys_unmap s sp v perms)\<turnstile>(Virtual sp1 v1)"
          using unmap_path_tran_valid a11 by blast
        then show False using a1 valid_page_def by auto
      qed
      then have h12:"get_perms (sys_unmap s sp v perms) sp1 v1 = get_perms s sp1 v1 - perms" 
        using unmap_preserve_perms_subset a11 p2 by simp
      have h13:"s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>*(Virtual sp v)"
        using a11 h1 basic15 p2 by simp
      have h14:"\<not> get_perms s sp2 v2 \<subseteq> perms"
        using h11 p1[unfolded Inv_Space_Perms_Subset_def] h1 by blast
      have h15:"Virtual sp2 v2 = Virtual sp v \<or> s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v)"
        using h13 rtran_tran by simp
      have h16:"Virtual sp2 v2 = Virtual sp v \<Longrightarrow> 
          get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2"
      proof-
        assume a161:"Virtual sp2 v2 = Virtual sp v"
        have "\<not>s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v)"
          using p2[unfolded Inv_Space_HasNot_Loop_def] a161 by simp
        then have "the (space_mapping (sys_unmap s sp v perms) sp2) v2 = the (space_mapping s sp2) v2"
          using unmap_not_path_space a161 h4 by simp
        then show ?thesis unfolding get_perms_def by simp
      qed
      have h17:"s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow>
          get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2- perms"
        using unmap_preserve_perms_subset h14 by simp
       show ?thesis using h12 h15 h3 h16 h17 by auto
    next
      assume a21:"\<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v)"
      have h20:"\<not>s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v)" 
        using a21 h1 basic2 one_path by blast
      have h21:"get_perms (sys_unmap s sp v perms) sp1 v1 = get_perms s sp1 v1"
        using unmap_not_path_space a21 p2 h1 direct_path_def get_perms_def by auto
      have h22:"get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2"
        using unmap_not_path_space h20 h2 p2 direct_path_def valid_page_def
        using get_perms_def by auto
      show ?thesis using h21 h22 h3
        by auto
    qed
  } then show ?thesis unfolding Inv_Space_Perms_Subset_def
    by simp
qed

lemma sys_unmap_Inv_Space_Valid_Has_Real1:
"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r)) \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow> Inv_Space_Perms_Subset s \<Longrightarrow>
(sys_unmap s sp v perms)\<turnstile>x \<Longrightarrow> \<exists>r. (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r)"
proof-
  fix x
  assume a1:"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r))" and a2:"(sys_unmap s sp v perms)\<turnstile>x" and
    a3:"Inv_Space_HasNot_Loop s" and a4:"Inv_Space_Perms_Subset s"
  have h1:"s\<turnstile>x" using a2 sys_unmap_valid by simp
  then have h2:"\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r)" using a1 by simp
  then obtain r where h3:"s\<turnstile>x\<leadsto>\<^sup>*(Real r)" by auto
  show "\<exists>r. (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r)"
  proof(cases x)
    case (Virtual x11 x12)
    have h10:"\<not>s\<turnstile>(Real r)\<leadsto>\<^sup>*(Virtual sp v)" 
      using rtran_tran FatherIsValid basic3 by fastforce
    have h11:"s\<turnstile>x\<leadsto>\<^sup>+(Real r)" using Virtual h3 rtran_tran by simp
    have h12:"\<not> s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v) \<or> s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v)" by simp
    then have h13:"(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+(Real r)"
    proof
      assume "\<not> s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v)"
      then show ?thesis using h11 unmap_not_path_tran a3 by simp
    next
      assume a11:"s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v)"
      have "\<not> get_perms s x11 x12 \<subseteq> perms"
      proof
        assume a111:"get_perms s x11 x12 \<subseteq> perms"
        then have "\<not>(sys_unmap s sp v perms)\<turnstile>x"
          using Virtual unmap_path_tran_valid a11 by blast
        then show False using a2 by simp
      qed
      then have h111:"(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v)"
        using unmap_preserve_tran_tran Virtual a3 a4 a11 get_perms_auxi by simp
      have h1111:"\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp v)" 
        using a3[unfolded Inv_Space_HasNot_Loop_def] by simp
      have h112:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Real r)" using h11 h10 basic17 a3 a11 by blast
      then have h113:"(sys_unmap s sp v perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Real r)"
        using unmap_not_path_tran h1111 by auto
      then show ?thesis using h111 basic1 by blast
    qed
    then show ?thesis using rtran_tran by auto
  next
    case (Real x2)
    then show ?thesis using rtran_path.intros(1) by auto
  qed
qed

lemma sys_unmap_Inv_Space_Valid_Has_Real2:
"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r)) \<Longrightarrow> (sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r) \<Longrightarrow> 
(sys_unmap s sp v perms)\<turnstile>x"
proof-
  fix x
  assume a1:"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r))" and a2:"(sys_unmap s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r)"
  show "(sys_unmap s sp v perms)\<turnstile>x"
  proof(cases x)
    case (Virtual x11 x12)
    then show ?thesis using a2 rtran_tran
      by (meson FatherIsValid page_t.distinct(1) rtran_path.cases)
  next
    case (Real x2)
    then show ?thesis using valid_page_def by simp
  qed
qed

lemma sys_unmap_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Valid_Has_Real (sys_unmap s sp v perms)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def] p2 p3
    sys_unmap_Inv_Space_Valid_Has_Real1 sys_unmap_Inv_Space_Valid_Has_Real2
  by auto

lemma sys_unmap_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (sys_unmap s sp v perms)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
     sys_unmap_NC_Space 
  by blast

lemma sys_unmap_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
  shows "Inv_Space_Spaces_IsNot_None (sys_unmap s sp v perms)"
  unfolding Inv_Space_Spaces_IsNot_None_def
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
     sys_unmap_NC_Space 
  by auto

lemma sys_unmap_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
  shows "Inv_Space_Vpage_Range (sys_unmap s sp v perms)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def] sys_unmap_valid by blast

lemma sys_unmap_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (sys_unmap s sp v perms)"
  unfolding Inv_Space_def
  using
    sys_unmap_Inv_Space_HasNot_Loop sys_unmap_Inv_Space_Valid_Has_Real
    sys_unmap_Inv_Space_Perms_IsNot_Empty sys_unmap_Inv_Space_Spaces_In_Config 
   sys_unmap_Inv_Space_InitialSpaces_In_Spaces sys_unmap_Inv_Space_Perms_Subset
   sys_unmap_Inv_Space_Spaces_IsNot_None sys_unmap_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsubsection\<open>Thread\<close>
lemma sys_unmap_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma sys_unmap_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma sys_unmap_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma sys_unmap_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma sys_unmap_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma sys_unmap_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma sys_unmap_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma sys_unmap_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma sys_unmap_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma sys_unmap_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma sys_unmap_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (sys_unmap s sp v perms)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def]
    sys_unmap_NC_Thread sys_unmap_NC_Space
  by auto

lemma sys_unmap_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (sys_unmap s sp v perms)"
  unfolding Inv_Threads_Eq_Space_Threads_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def]
    sys_unmap_NC_Thread sys_unmap_NC_Space
  by auto

lemma sys_unmap_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma sys_unmap_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma sys_unmap_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma sys_unmap_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (sys_unmap s sp v perms)"
  unfolding Inv_IntThreads_Utcb_Is_None_def sys_unmap_def 
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma sys_unmap_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma sys_unmap_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (sys_unmap s sp v perms)"
  unfolding sys_unmap_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma sys_unmap_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (sys_unmap s sp v perms)"
  using assms unfolding Inv_Sigma0_Space_def sys_unmap_def
  by auto

lemma sys_unmap_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (sys_unmap s sp v perms)"
  using assms unfolding Inv_RootServer_Space_def sys_unmap_def
  by auto

lemma sys_unmap_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (sys_unmap s sp v perms)"
  using assms unfolding Inv_IntThreads_Space_def sys_unmap_def
  by auto

lemma sys_unmap_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (sys_unmap s sp v perms)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] sys_unmap_Inv_Idle_NotIn_Threads 
    sys_unmap_Inv_Sigma0_In_Active sys_unmap_Inv_Idle_Space_Is_KernelSpace
    sys_unmap_Inv_RootServer_In_Active sys_unmap_Inv_IntThreads_In_Active 
    sys_unmap_Inv_Threads_Space_Dom
    sys_unmap_Inv_Threads_In_Config sys_unmap_Inv_Active_In_Threads 
    sys_unmap_Inv_NThreads_Is_None sys_unmap_Inv_Threads_IsNot_None 
    sys_unmap_Inv_Threads_Space_In_Spaces sys_unmap_Inv_Threads_Eq_Space_Threads
    sys_unmap_Inv_Threads_Sche_In_Threads 
    sys_unmap_Inv_NActive_Utcb_Is_None sys_unmap_Inv_Active_Utcb_IsNot_None
    sys_unmap_Inv_IntThreads_Utcb_Is_None sys_unmap_Inv_Threads_Partner_In_Threads
    sys_unmap_Inv_Threads_Incoming_In_Threads sys_unmap_Inv_Sigma0_Space
    sys_unmap_Inv_RootServer_Space sys_unmap_Inv_IntThreads_Space
  by auto

lemma sys_unmap_Invariant:
  assumes "Invariants s"
  shows "Invariants (sys_unmap s sp v perms)"
  using Invariants_def sys_unmap_Inv_Current sys_unmap_Inv_Space 
    sys_unmap_Inv_Thread  assms
  by auto

section\<open>sys_flush\<close>
subsection\<open>user\<close>
lemma sys_flush_NC_User:
"thread_pager (sys_flush s sp v perms) = thread_pager s \<and>
 thread_handler (sys_flush s sp v perms) = thread_handler s \<and>
 thread_message (sys_flush s sp v perms) = thread_message s \<and>
 thread_rcvWindow (sys_flush s sp v perms) = thread_rcvWindow s \<and>
 thread_error (sys_flush s sp v perms) = thread_error s"
  by(auto simp: sys_flush_def)

subsection\<open>current\<close>
lemma sys_flush_NC_Current:
"current_thread (sys_flush s sp v perms) = current_thread s \<and>
 current_time (sys_flush s sp v perms) = current_time s"
  by(auto simp: sys_flush_def)

subsection\<open>thread\<close>
lemma sys_flush_NC_Thread:
"threads (sys_flush s sp v perms) = threads s \<and>
 active_threads (sys_flush s sp v perms) = active_threads s \<and>
 thread_space (sys_flush s sp v perms) = thread_space s \<and>
 thread_scheduler (sys_flush s sp v perms) = thread_scheduler s \<and>
 thread_state (sys_flush s sp v perms) = thread_state s \<and>
 thread_priority (sys_flush s sp v perms) = thread_priority s \<and>
 thread_total_quantum (sys_flush s sp v perms) = thread_total_quantum s \<and>
 thread_timeslice_length (sys_flush s sp v perms) = thread_timeslice_length s \<and>
 thread_current_timeslice (sys_flush s sp v perms) = thread_current_timeslice s"
  by(auto simp: sys_flush_def)

subsection\<open>space\<close>
lemma sys_flush_NC_Space:
"spaces (sys_flush s sp v perms) = spaces s \<and>
 initialised_spaces (sys_flush s sp v perms) = initialised_spaces s \<and>
 space_threads (sys_flush s sp v perms) = space_threads s \<and>
 dom (space_mapping (sys_flush s sp v perms)) = dom (space_mapping s)"
  apply(auto simp: sys_flush_def spaces_def)
  apply(case_tac "space_mapping s x = None")
  by auto

subsubsection \<open>flush post-node in same path\<close>
lemma flush_post_tran_vapge:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1) \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow>
Inv_Space_Valid_Has_Real s \<Longrightarrow> space_mapping (sys_flush s sp vpage perms) sp1 \<noteq> None \<and> 
the(space_mapping (sys_flush s sp vpage perms) sp1) v1 = the(space_mapping s sp1) v1"
proof-
  assume a1:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1)" and a2:"Inv_Space_HasNot_Loop s" and
    a3:"Inv_Space_Valid_Has_Real s"
  have h1:"\<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>*(Virtual sp vpage)"
  proof
    assume a11:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>*(Virtual sp vpage)"
    have h11:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp1 v1)" using a11 a1 basic12 by simp 
    then show False using a2[unfolded Inv_Space_HasNot_Loop_def]
      by auto
  qed
  have h2:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1 (fst(the(the (space_mapping s sp1) v1)))"
    using a1 path_direct path_space direct_path_def
    by (metis (no_types, lifting) ValidVpageMappingNotNone YTranIsValid a3 option.collapse prod.collapse)
  have h3:"\<not>s\<turnstile>(fst(the(the (space_mapping s sp1) v1)))\<leadsto>\<^sup>*(Virtual sp vpage)"
    using h1 h2 using refl_tran by blast
  then show ?thesis
    unfolding sys_flush_def
    using h1 h2 direct_def apply auto apply blast
    using direct_def by blast
qed

lemma flush_post_tran_direct:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1) \<Longrightarrow>
s\<turnstile>(Virtual sp1 v1) \<leadsto>\<^sup>1 y \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow> Inv_Space_Valid_Has_Real s \<Longrightarrow> 
(sys_flush s sp vpage perms)\<turnstile>(Virtual sp1 v1) \<leadsto>\<^sup>1 y"
  using flush_post_tran_vapge direct_path_def
  by fastforce

lemma flush_post_tran_tran:"s\<turnstile>(Virtual sp1 v1) \<leadsto>\<^sup>+ y \<Longrightarrow> Inv_Space_Valid_Has_Real s \<Longrightarrow> 
s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+(Virtual sp1 v1) \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow> 
(sys_flush s sp vpage perms)\<turnstile>(Virtual sp1 v1) \<leadsto>\<^sup>+ y"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then show ?case using flush_post_tran_direct tran_path.intros
    using FatherIsVirtual by smt
next
  case (tran_path x y z)
  then have h11:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+y"
    using basic11 rtran_tran by blast
  then have h12:"(sys_flush s sp vpage perms)\<turnstile>y\<leadsto>\<^sup>+z"
    using tran_path(3,4,6) by simp
  have "(sys_flush s sp vpage perms)\<turnstile>x\<leadsto>\<^sup>1y"
    using tran_path FatherIsVirtual flush_post_tran_direct by blast
  then show ?case using h12 tran_path.intros by simp
qed

lemma flush_post_tran_rtran:"s\<turnstile>x \<leadsto>\<^sup>* y \<Longrightarrow> Inv_Space_Valid_Has_Real s \<Longrightarrow> 
s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+x \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow> 
(sys_flush s sp vpage perms)\<turnstile>x \<leadsto>\<^sup>* y"
proof(induction rule:rtran_path.induct)
  case (refl_path x)
  then show ?case using flush_post_tran_direct rtran_path.intros
    using FatherIsVirtual by smt
next
  case (refl_tran x y z)
  then have h11:"s\<turnstile>(Virtual sp vpage)\<leadsto>\<^sup>+y"
    using basic11 rtran_tran by blast
  then have h12:"(sys_flush s sp vpage perms)\<turnstile>y\<leadsto>\<^sup>*z"
    using refl_tran(3,4,6) by simp
  have "(sys_flush s sp vpage perms)\<turnstile>x\<leadsto>\<^sup>1y"
    using refl_tran FatherIsVirtual flush_post_tran_direct by blast
  then show ?case using h12 rtran_path.intros by simp
qed

thm flush_post_tran_tran
thm flush_post_tran_rtran

subsubsection \<open>flush pre-node in same path\<close>
lemma flush_space_none:"space_mapping s sp1 = None \<Longrightarrow> space_mapping (sys_flush s sp vpage perms) sp1 = None"
  unfolding sys_flush_def by simp

lemma flush_vpage_none:"space_mapping s sp1 = Some mapping \<Longrightarrow> mapping vpage1 = None \<Longrightarrow> 
the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1 = None"
  unfolding sys_flush_def by simp

lemma flush_in_path_rtran:"space_mapping s sp1 \<noteq> None \<Longrightarrow> the (space_mapping s sp1) vpage1 \<noteq> None \<Longrightarrow>
s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow> snd (the (the (space_mapping s sp1) vpage1)) \<subseteq> perms \<Longrightarrow>
sp \<noteq> Sigma0Space \<Longrightarrow> the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1 = None"
  unfolding sys_flush_def 
  by auto

lemma flush_pre_rtran_valid:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
get_perms s sp1 vpage1 \<subseteq> perms \<Longrightarrow> \<not>(sys_flush s sp vpage perms)\<turnstile>(Virtual sp1 vpage1)"
proof-
  assume a1:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage)" and
         a2:"get_perms s sp1 vpage1 \<subseteq> perms" and
         a3:"sp \<noteq> Sigma0Space"
  then show ?thesis
  proof(cases "space_mapping s sp1")
    case None
    then show ?thesis using flush_space_none
       ValidVpageMappingNotNone by blast
  next
    case (Some a)
    then show ?thesis
    proof(cases "a vpage1")
      case None
      then show ?thesis using flush_vpage_none
        Some ValidVpageMappingNotNone by auto
    next
      case (Some a)
      then show ?thesis using flush_in_path_rtran a1 a2 a3 
          ValidVpageMappingNotNone Some
        by (metis (no_types, lifting) flush_space_none flush_vpage_none get_perms_def option.collapse)
    qed
  qed
qed

lemma flush_pre_tran_valid:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
get_perms s sp1 vpage1 \<subseteq> perms \<Longrightarrow> \<not>(sys_flush s sp vpage perms)\<turnstile>(Virtual sp1 vpage1)"
  using flush_pre_rtran_valid rtran_tran by auto

thm flush_pre_rtran_valid
thm flush_pre_tran_valid

subsubsection \<open>flush not enough perms\<close>
lemma flush_preserve_rtran_vpage:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> space_mapping s sp \<noteq> None \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
the(space_mapping s sp)vpage \<noteq> None \<Longrightarrow> space_mapping (sys_flush s sp vpage perms) sp1 \<noteq> None \<and>
the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1 \<noteq> None \<and>
fst(the (the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1)) = 
fst(the (the (space_mapping s sp1) vpage1))"
proof-
  assume a1:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage)" and
         a2:"\<not>get_perms s sp1 vpage1 \<subseteq> perms" and a3:"space_mapping s sp \<noteq> None" and
         a4:"the(space_mapping s sp)vpage \<noteq> None" and a5:"sp \<noteq> Sigma0Space"
  from a1 have "s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage) \<or> 
            (Virtual sp vpage) = (Virtual sp1 vpage1)" using rtran_tran by auto
  then show ?thesis
  proof
    assume a11:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage)"
    then have "space_mapping s sp1 \<noteq> None \<and> the(space_mapping s sp1)vpage1 \<noteq> None"
      using path_space by auto
    then show ?thesis
      unfolding sys_flush_def
      using a5 a2[unfolded get_perms_def] by auto
  next
    assume a12:"(Virtual sp vpage) = (Virtual sp1 vpage1)"
    then show ?thesis
      unfolding sys_flush_def
      using a2 a3 a4 a5 get_perms_def
      by auto
  qed
qed

lemma flush_preserve_tran_vpage:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
space_mapping (sys_flush s sp vpage perms) sp1 \<noteq> None \<and>
the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1 \<noteq> None \<and>
fst(the (the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1)) = 
fst(the (the (space_mapping s sp1) vpage1))"
  unfolding sys_flush_def get_perms_def
  using path_space by auto

lemma flush_preserve_direct:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>1 (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
(sys_flush s sp vpage perms) \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>1 (Virtual sp vpage)"
  unfolding sys_flush_def get_perms_def
  using path_space direct_path_def by auto

lemma flush_preserve_self_direct:"\<not>(get_perms s sp vpage \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
s \<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y \<Longrightarrow>
(sys_flush s sp vpage perms) \<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y"
proof-
  assume a1:"\<not>get_perms s sp vpage \<subseteq> perms" and 
         a2:"s \<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y" and a3:"sp \<noteq> Sigma0Space"
  then have h1:"space_mapping s sp \<noteq> None \<and> the(space_mapping s sp)vpage \<noteq> None \<and>
    fst(the (the (space_mapping s sp) vpage)) = y" using direct_path_def by auto
  then have "space_mapping (sys_flush s sp vpage perms) sp \<noteq> None \<and>
    the (space_mapping (sys_flush s sp vpage perms) sp) vpage \<noteq> None \<and>
    fst(the (the (space_mapping (sys_flush s sp vpage perms) sp) vpage)) = y" 
    using flush_preserve_rtran_vpage a1 a2 a3 refl_path by blast
  then show ?thesis using direct_path_def by auto
qed

lemma flush_preserve_tran_direct:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>1 (Virtual spa va) \<Longrightarrow>
(sys_flush s sp vpage perms) \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>1 (Virtual spa va)"
proof-
  assume a1:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage)" and
         a2:"\<not>get_perms s sp1 vpage1 \<subseteq> perms" and 
         a3:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>1 (Virtual spa va)" and a4:"sp \<noteq> Sigma0Space"
  from a1 have "s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage) \<or> 
            (Virtual sp vpage) = (Virtual sp1 vpage1)" using rtran_tran by auto
  then show ?thesis
  proof
    assume a11:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage)"
    then have "space_mapping s sp1 \<noteq> None \<and> the (space_mapping s sp1)vpage1 \<noteq> None"
      using path_space by auto
    then have h11:"space_mapping (sys_flush s sp vpage perms) sp1 \<noteq> None \<and>
    the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1 \<noteq> None \<and>
    fst(the (the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1)) = Virtual spa va"
    using a11 a2 a3 a4 flush_preserve_tran_vpage direct_def prod.collapse prod.inject by fastforce
    then show ?thesis using direct_path_def by auto
  next
    assume a12:"(Virtual sp vpage) = (Virtual sp1 vpage1)"
    then show ?thesis using flush_preserve_self_direct a1 a2 a3 a4 by auto
  qed
qed

lemma flush_preserve_self1:"s \<turnstile> x \<leadsto>\<^sup>* m \<Longrightarrow> m = (Virtual sp vpage) \<Longrightarrow>
s \<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y \<Longrightarrow> \<not>(get_perms1 s x \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow> 
Inv_Space_Perms_Subset s \<Longrightarrow> (sys_flush s sp vpage perms)\<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y"
proof(induction rule:rtran_path.induct)
  case (refl_path a)
  then show ?case using flush_preserve_self_direct get_perms_auxi by auto
next
  case (refl_tran a b c)
  then have "s\<turnstile>b\<leadsto>\<^sup>+y" using basic11 by simp
  then obtain sp1 v1 where h1:"b = Virtual sp1 v1" using FatherIsVirtual basic3 by blast
  obtain sp2 v2 where h2:"a = Virtual sp2 v2" using FatherIsVirtual refl_tran(1) by blast
  then have "\<not> get_perms1 s b \<subseteq> perms"
    using refl_tran h1 get_perms_auxi unfolding Inv_Space_Perms_Subset_def by blast
  then show ?case using refl_tran by simp
qed

lemma flush_preserve_self:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow> 
s \<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y \<Longrightarrow> \<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow> 
Inv_Space_Perms_Subset s \<Longrightarrow> (sys_flush s sp vpage perms)\<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y"
  using flush_preserve_self1 get_perms_auxi
  by auto

lemma flush_preserve_rtran_auxi:"s \<turnstile> x \<leadsto>\<^sup>* y \<Longrightarrow> y = (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms1 s x \<subseteq> perms) \<Longrightarrow> Inv_Space_Perms_Subset s \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
(sys_flush s sp vpage perms)\<turnstile> x \<leadsto>\<^sup>* y"
proof(induction rule:rtran_path.induct)
  case (refl_path x)
  then show ?case 
    using rtran_path.intros by simp
next
  case (refl_tran x y z)
  then obtain spa va where h21:"y = Virtual spa va" 
    using FatherIsVirtual by (metis rtran_path.cases)
  then have "\<not> get_perms1 s y \<subseteq> perms" using refl_tran Inv_Space_Perms_Subset_def
    by (metis FatherIsVirtual get_perms_auxi in_mono subset_eq)
  then have h22:"(sys_flush s sp vpage perms)\<turnstile>y\<leadsto>\<^sup>*z" using refl_tran by simp
  obtain spa va where "x = Virtual spa va" 
    using FatherIsVirtual refl_tran(1) by blast
  then have "(sys_flush s sp vpage perms)\<turnstile>x\<leadsto>\<^sup>1y" 
    using refl_tran flush_preserve_tran_direct get_perms_auxi h21 rtran_path.refl_tran by auto
  then show ?case using rtran_path.intros h22 by simp
qed

lemma flush_preserve_rtran:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> Inv_Space_Perms_Subset s \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow> 
(sys_flush s sp vpage perms)\<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage)"
  using flush_preserve_rtran_auxi get_perms_auxi
  by auto

thm flush_preserve_rtran

lemma flush_preserve_perms:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> space_mapping s sp \<noteq> None \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
the (space_mapping s sp) vpage \<noteq> None \<Longrightarrow> 
snd(the (the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1)) = 
snd(the (the (space_mapping s sp1) vpage1))- perms"
  unfolding sys_flush_def get_perms_def  apply auto
  using path_space rtran_tran  by fastforce+

lemma flush_preserve_perms_subset_tran:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>+ (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
get_perms (sys_flush s sp vpage perms) sp1 vpage1 = get_perms s sp1 vpage1 - perms"
  unfolding sys_flush_def get_perms_def  apply auto
  using path_space rtran_tran  by fastforce+

lemma flush_preserve_perms_subset_self:"\<not>(get_perms s sp vpage \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
 space_mapping s sp \<noteq> None \<Longrightarrow> the (space_mapping s sp) vpage \<noteq> None \<Longrightarrow> 
get_perms (sys_flush s sp vpage perms) sp vpage = get_perms s sp vpage - perms"
  unfolding sys_flush_def get_perms_def  apply auto
  using path_space rtran_tran by fastforce

lemma flush_preserve_perms_subset_rtran:"s \<turnstile> (Virtual sp1 vpage1) \<leadsto>\<^sup>* (Virtual sp vpage) \<Longrightarrow>
\<not>(get_perms s sp1 vpage1 \<subseteq> perms) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow> space_mapping s sp \<noteq> None \<Longrightarrow>
the (space_mapping s sp) vpage \<noteq> None \<Longrightarrow> 
get_perms (sys_flush s sp vpage perms) sp1 vpage1 = get_perms s sp1 vpage1 - perms"
  unfolding sys_flush_def get_perms_def  apply auto
  using path_space rtran_tran  by fastforce+

subsubsection\<open>flush node in different path\<close>
lemma flush_not_path_rtran:"\<not>s\<turnstile>(Virtual sp1 vpage1)\<leadsto>\<^sup>*(Virtual sp vpage) \<Longrightarrow>
the (space_mapping (sys_flush s sp vpage perms) sp1) vpage1 = the(space_mapping s sp1) vpage1"
  unfolding sys_flush_def
  by auto

lemma flush_not_path_valid:"\<not>s\<turnstile>(Virtual sp1 vpage1)\<leadsto>\<^sup>*(Virtual sp vpage) \<Longrightarrow>
(sys_flush s sp vpage perms)\<turnstile>(Virtual sp1 vpage1) = s\<turnstile>(Virtual sp1 vpage1)"
  unfolding sys_flush_def valid_page_def direct_path_def
  by auto

lemma flush_not_path_space:"s\<turnstile>(Virtual sp1 v1) \<Longrightarrow> \<not> s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>*(Virtual sp v) \<Longrightarrow> 
the (space_mapping (sys_flush s sp v perms) sp1) v1 = the (space_mapping s sp1) v1"
  using flush_not_path_rtran by simp

lemma flush_not_path_direct:"s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not> s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v) \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>1y"
proof-
  assume a1:"s\<turnstile>x\<leadsto>\<^sup>1y" and a2:"\<not> s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)"
  then obtain sp1 v1 where h1:"x = Virtual sp1 v1 \<and> s\<turnstile>(Virtual sp1 v1) \<and> space_mapping s sp1 \<noteq> None \<and>
    the(space_mapping s sp1) v1 \<noteq> None \<and> fst(the(the (space_mapping s sp1)v1)) = y"
    using direct_path_def valid_page_def by force
  then have h2:"fst (the (the (space_mapping (sys_flush s sp v perms) sp1) v1)) = y"
    using flush_not_path_rtran a2 by simp
  have "(sys_flush s sp v perms)\<turnstile>(Virtual sp1 v1)" using flush_not_path_valid a2 h1 by simp
  then show ?thesis using h1 h2 direct_path_def ValidVpageMappingNotNone by auto
qed

lemma flush_not_path_tran_rtran:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v) \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y"
proof-
  assume a1:"s\<turnstile>x\<leadsto>\<^sup>+y" and a2:"\<not>s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)"
  then show "(sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>+y"
  proof(induction rule:tran_path.induct)
    case (one_path x y)
    then show ?case using flush_not_path_direct tran_path.intros by simp
  next
    case (tran_path x y z)
    then have "\<not> s\<turnstile>y\<leadsto>\<^sup>*(Virtual sp v)" using refl_tran by blast
    then have h1:"(sys_flush s sp v perms)\<turnstile>y\<leadsto>\<^sup>+z" using tran_path by simp
    have h2:"(sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>1y" using tran_path flush_not_path_direct by simp
    then show ?case using h1 tran_path.tran_path by simp
  qed
qed

thm flush_not_path_tran_rtran

lemma sys_flush_pre:"(sys_flush s sp v perms)\<turnstile> x \<leadsto>\<^sup>1 y \<Longrightarrow> s \<turnstile> x\<leadsto>\<^sup>1 y"
  unfolding sys_flush_def direct_path_def
  apply auto
  apply(cases "sp = Sigma0Space")
   apply simp
  apply simp
  apply(case_tac "space_mapping s spa = None")
  apply auto
  apply (case_tac "ya va = None")
  apply auto
  by (metis fst_conv option.discI option.sel)

lemma sys_flush_valid:"(sys_flush s sp v perms)\<turnstile> x \<Longrightarrow> s \<turnstile> x"
  apply(cases x)
  unfolding valid_page_def
  using sys_flush_pre
   apply auto
  by blast

subsection\<open>IPC\<close>
lemma sys_flush_NC_IPC:
"thread_ipc_partner (sys_flush s sp v perms) = thread_ipc_partner s \<and>
 thread_ipc_timeout (sys_flush s sp v perms) = thread_ipc_timeout s \<and>
 thread_incoming (sys_flush s sp v perms) =  thread_incoming s"
  by(auto simp: sys_flush_def)

subsection\<open>scheduling\<close>
lemma sys_flush_NC_Scheduling:
"wait_queuing (sys_flush s sp v perms) = wait_queuing s \<and>
 ready_queuing (sys_flush s sp v perms) = ready_queuing s \<and>
 current_timeslice (sys_flush s sp v perms) = current_timeslice s"
  by(auto simp: sys_flush_def)

subsection\<open>inv\<close>
subsubsection\<open>Current\<close>
lemma sys_flush_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma sys_flush_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma sys_flush_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (sys_flush s sp v perms)"
  using sys_flush_Inv_Current_Thread_In_Active sys_flush_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsubsection\<open>Space\<close>
lemma sys_flush_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (sys_flush s sp v perms)"
  using p1 
  unfolding Inv_Space_HasNot_Loop_def 
  apply auto
proof-
  {
    fix spa v1 v2 x y
    assume a1:"\<forall>sp v1 v2. \<not> s\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)" and
           a2:"(sys_flush s sp v perms)\<turnstile> x\<leadsto>\<^sup>+ y" and
           a3:"x = (Virtual spa v1)" and
           a4:"y = (Virtual spa v2)"
    have h1:"s\<turnstile>x\<leadsto>\<^sup>+y"
      using a2
      apply(induction rule:tran_path.induct)
      subgoal
        using sys_flush_pre tran_path.intros
        by blast
      using sys_flush_pre tran_path.intros
      by blast
    have h2:"s \<turnstile> (Virtual spa v1) \<leadsto>\<^sup>+ (Virtual spa v2)"
      using h1 a3 a4 by simp
    have False using a1 h2 by simp
  }
  then show "\<And>spa v1 v2. \<forall>sp v1 v2. \<not> s\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2) \<Longrightarrow>
       (sys_flush s sp v perms)\<turnstile>(Virtual spa v1)\<leadsto>\<^sup>+(Virtual spa v2) \<Longrightarrow> False"
    by blast
qed

lemma sys_flush_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
  shows "Inv_Space_Perms_IsNot_Empty (sys_flush s sp v perms)"
  using p1
  unfolding Inv_Space_Perms_IsNot_Empty_def
  apply auto
  unfolding sys_flush_def get_perms_def
  apply(cases "sp=Sigma0Space")
   apply auto
  unfolding valid_page_def direct_path_def Let_def
  apply(case_tac "space_mapping s spa = None")
  subgoal
    by auto
  apply auto
  apply(subgoal_tac "y v_page = Some (p2,{})")
  subgoal
    using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def valid_page_def direct_path_def]
    by fastforce
  unfolding Let_def
  apply(case_tac "y v_page = None")
   apply simp
  apply simp
  apply(case_tac "s\<turnstile>(Virtual spa v_page)\<leadsto>\<^sup>*(Virtual sp v)")
  apply auto
   apply(case_tac "b \<subseteq> perms")
  apply auto
  apply(case_tac "b \<subseteq> perms")
  by auto

lemma sys_flush_Inv_Space_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (sys_flush s sp v perms)"
  unfolding Inv_Space_Spaces_In_Config_def spaces_def
  using p1[unfolded Inv_Space_Spaces_In_Config_def spaces_def]
  unfolding sys_flush_def
  apply auto
  apply(case_tac "space_mapping s x = None")
  by auto

lemma sys_flush_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Perms_Subset (sys_flush s sp v perms)"
proof-
  {
    fix sp1 sp2 v1 v2
    assume a1:"(sys_flush s sp v perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    have h1:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
      using sys_flush_pre a1 by simp
    have h2:"s\<turnstile>(Virtual sp2 v2)" using YIsValid h1 p2 p3 by simp
    have h3:"get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2"
      using h1 p1[unfolded Inv_Space_Perms_Subset_def] by simp
    have h4:"space_mapping s sp2 \<noteq> None" using h2 valid_page_def direct_path_def by auto
    have "s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) \<or> \<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v)" by simp
    then have "get_perms (sys_flush s sp v perms) sp1 v1 \<subseteq> get_perms (sys_flush s sp v perms) sp2 v2"
    proof
      assume a11:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v)"
      have h11:"sp \<noteq> Sigma0Space \<Longrightarrow> \<not> get_perms s sp1 v1 \<subseteq> perms"
      proof
        assume "get_perms s sp1 v1 \<subseteq> perms" and "sp \<noteq> Sigma0Space"
        then have "\<not>(sys_flush s sp v perms)\<turnstile>(Virtual sp1 v1)"
          using flush_pre_tran_valid a11 by auto
        then show False using a1 valid_page_def by auto
      qed
      then have h12:"sp \<noteq> Sigma0Space \<Longrightarrow> get_perms (sys_flush s sp v perms) sp1 v1 = get_perms s sp1 v1 - perms" 
        using flush_preserve_perms_subset_tran h11 a11 by simp
      have h13:"s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>*(Virtual sp v)"
        using a11 h1 basic15 p2 by simp
      have h14:"sp \<noteq> Sigma0Space \<Longrightarrow> \<not> get_perms s sp2 v2 \<subseteq> perms"
        using h11 p1[unfolded Inv_Space_Perms_Subset_def] h1 by blast
      have h15:"Virtual sp2 v2 = Virtual sp v \<or> s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v)"
        using h13 rtran_tran by simp
      have h16:"Virtual sp2 v2 = Virtual sp v \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
          get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2"
      proof-
        assume a161:"Virtual sp2 v2 = Virtual sp v"
        have "\<not>s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v)"
          using p2[unfolded Inv_Space_HasNot_Loop_def] a161 by simp
        then have "the (space_mapping (sys_unmap s sp v perms) sp2) v2 = the (space_mapping s sp2) v2"
          using unmap_not_path_space a161 h4 by simp
        then show ?thesis unfolding get_perms_def by simp
      qed
      have h17:"s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow>
          get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2- perms"
        using unmap_preserve_perms_subset h14 by simp
      have h15:"sp \<noteq> Sigma0Space \<Longrightarrow> get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2
          \<or> get_perms (sys_unmap s sp v perms) sp2 v2 = get_perms s sp2 v2 - perms"
        using h15 h16 h17 by blast
      have h16:"sp = Sigma0Space \<Longrightarrow> 
        get_perms (sys_flush s sp v perms) sp1 v1 \<subseteq> get_perms (sys_flush s sp v perms) sp2 v2"
        unfolding sys_flush_def using h3 by simp
      have h17:"sp \<noteq> Sigma0Space \<Longrightarrow>
        get_perms (sys_flush s sp v perms) sp1 v1 \<subseteq> get_perms (sys_flush s sp v perms) sp2 v2"
        using h12 h15 h3 
        by (metis Diff_mono ValidVpageMappingNotNone flush_preserve_perms_subset_self flush_preserve_perms_subset_tran h13 h14 h2 order_refl page_t.inject(1) rtran_tran)
       show ?thesis using h16 h17 by auto
    next
      assume a21:"\<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v)"
      have h20:"\<not>s\<turnstile>(Virtual sp2 v2)\<leadsto>\<^sup>*(Virtual sp v)" 
        using a21 h1 basic42 one_path by blast
      from a21 have "(Virtual sp1 v1) = (Virtual sp v) \<or> \<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>*(Virtual sp v)"
        using rtran_tran by auto
      then have h21:"get_perms (sys_flush s sp v perms) sp1 v1 \<subseteq> get_perms s sp1 v1"
      proof
        assume a211:"(Virtual sp1 v1) = (Virtual sp v)"
        then have h211:"space_mapping s sp \<noteq> None \<and> the(space_mapping s sp) v \<noteq> None"
          using path_space h1 tran_path.intros by blast
        have "sp \<noteq> Sigma0Space \<Longrightarrow> \<not>(get_perms s sp v \<subseteq> perms)"
        proof
          assume "get_perms s sp v \<subseteq> perms" and "sp \<noteq> Sigma0Space"
          then have "\<not>(sys_flush s sp v perms)\<turnstile>(Virtual sp v)"
            using flush_pre_rtran_valid a211 refl_path by auto
          then show False using a1 valid_page_def a211 by auto
        qed
        then have h212:"sp \<noteq> Sigma0Space \<Longrightarrow> get_perms (sys_flush s sp v perms) sp v = get_perms s sp v - perms"
          using a211 flush_preserve_perms_subset_self h211 by simp
        have "sp = Sigma0Space \<Longrightarrow> get_perms (sys_flush s sp v perms) sp v = get_perms s sp v"
          unfolding sys_flush_def by simp
        then show ?thesis  using h212 a211 by auto
      next
        assume a212:"\<not>s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>*(Virtual sp v)"
        then show ?thesis using flush_not_path_rtran get_perms_def by auto
      qed
      have h22:"get_perms (sys_flush s sp v perms) sp2 v2 = get_perms s sp2 v2"
        using flush_not_path_rtran h20 get_perms_def by auto
      show ?thesis using h21 h22 h3
        by auto
    qed
  } then show ?thesis unfolding Inv_Space_Perms_Subset_def
    by simp
qed

lemma sys_flush_Inv_Space_Valid_Has_Real1:
"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r)) \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow> Inv_Space_Perms_Subset s \<Longrightarrow>
(sys_flush s sp v perms)\<turnstile>x \<Longrightarrow> \<exists>r. (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r)"
proof-
  fix x
  assume a1:"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r))" and a2:"(sys_flush s sp v perms)\<turnstile>x" and
    a3:"Inv_Space_HasNot_Loop s" and a4:"Inv_Space_Perms_Subset s"
  have h1:"s\<turnstile>x" using a2 sys_flush_valid by simp
  then have h2:"\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r)" using a1 by simp
  then obtain r where h3:"s\<turnstile>x\<leadsto>\<^sup>*(Real r)" by auto
  show "\<exists>r. (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r)"
  proof(cases x)
    case (Virtual x11 x12)
    have h10:"\<not>s\<turnstile>(Real r)\<leadsto>\<^sup>*(Virtual sp v)" 
      using rtran_tran FatherIsValid basic3 by fastforce
    have h11:"s\<turnstile>x\<leadsto>\<^sup>+(Real r)" using Virtual h3 rtran_tran by simp
    have h12:"\<not> s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v) \<or> s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)" by simp
    then have h13:"(sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>+(Real r)"
    proof
      assume "\<not> s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)"
      then show ?thesis using h11 flush_not_path_tran_rtran a3 by simp
    next
      assume a11:"s\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)"
      have h110:"sp \<noteq> Sigma0Space \<Longrightarrow> \<not> get_perms s x11 x12 \<subseteq> perms"
      proof
        assume a111:"get_perms s x11 x12 \<subseteq> perms" and a112:"sp \<noteq> Sigma0Space"
        then have "\<not>(sys_flush s sp v perms)\<turnstile>x"
          using Virtual flush_pre_rtran_valid a11 by blast
        then show False using a2 by simp
      qed
      thm YTranIsValid
      then have h111:"sp \<noteq> Sigma0Space \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)"
        using flush_preserve_rtran Virtual a3 a4 a11 by simp
      have h112:"sp = Sigma0Space \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)"
        unfolding sys_flush_def using a11 by simp
      then have h113:"(sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Virtual sp v)" using h111 by auto
      have h114:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Real r)" using h11 h10 basic16 a3 a11 by blast
      then have "\<exists>y. s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y \<and> s\<turnstile>y \<leadsto>\<^sup>*(Real r)" using PlusEqOneStar by blast
      then obtain y where h115:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y \<and> s\<turnstile>y \<leadsto>\<^sup>*(Real r)" by auto 
      then have h116:"(sys_flush s sp v perms)\<turnstile>y \<leadsto>\<^sup>*(Real r)" 
        using flush_post_tran_rtran[unfolded Inv_Space_Valid_Has_Real_def] h114 a3 a1 one_path by simp
      have h117:"sp \<noteq> Sigma0Space \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y"
        using a11 h110 flush_preserve_self Virtual a4 h115 by simp
      have h118:"sp = Sigma0Space \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y"
        unfolding sys_flush_def using h115 by simp
      then have h119:"(sys_flush s sp v perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y"
        using h117 by auto
      then show ?thesis using h113 h116
        by (metis basic1 basic11  rtran_tran)
    qed
    then show ?thesis using rtran_tran by auto
  next
    case (Real x2)
    then show ?thesis using rtran_path.intros(1) by auto
  qed
qed


lemma sys_flush_Inv_Space_Valid_Has_Real2:
"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r)) \<Longrightarrow> (sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r) \<Longrightarrow> 
(sys_flush s sp v perms)\<turnstile>x"
proof-
  fix x
  assume a1:"\<forall>x. s\<turnstile>x = (\<exists>r. s\<turnstile>x\<leadsto>\<^sup>*(Real r))" and a2:"(sys_flush s sp v perms)\<turnstile>x\<leadsto>\<^sup>*(Real r)"
  show "(sys_flush s sp v perms)\<turnstile>x"
  proof(cases x)
    case (Virtual x11 x12)
    then show ?thesis using a2 rtran_tran
      by (meson FatherIsValid page_t.distinct(1) rtran_path.cases)
  next
    case (Real x2)
    then show ?thesis using valid_page_def by simp
  qed
qed

lemma sys_flush_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Valid_Has_Real (sys_flush s sp v perms)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  p2 p3 sys_flush_Inv_Space_Valid_Has_Real1 
    sys_flush_Inv_Space_Valid_Has_Real2
  by auto

lemma sys_flush_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (sys_flush s sp v perms)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
     sys_flush_NC_Space 
  by blast

lemma sys_flush_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
  shows "Inv_Space_Spaces_IsNot_None (sys_flush s sp v perms)"
  unfolding Inv_Space_Spaces_IsNot_None_def
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
     sys_flush_NC_Space 
  by auto

lemma sys_flush_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
  shows "Inv_Space_Vpage_Range (sys_flush s sp v perms)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def] sys_flush_valid by blast

lemma sys_flush_Inv_Space:
  assumes "Inv_Space s"
  shows "Inv_Space (sys_flush s sp v perms)"
  using Inv_Space_def assms sys_flush_Inv_Space_In_Config
    sys_flush_Inv_Space_HasNot_Loop sys_flush_Inv_Space_Perms_IsNot_Empty
    sys_flush_Inv_Space_Perms_Subset sys_flush_Inv_Space_Valid_Has_Real
    sys_flush_Inv_Space_InitialSpaces_In_Spaces sys_flush_Inv_Space_Spaces_IsNot_None
    sys_flush_Inv_Space_Vpage_Range
  by auto

subsubsection\<open>Thread\<close>
lemma sys_flush_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma sys_flush_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma sys_flush_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma sys_flush_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma sys_flush_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma sys_flush_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma sys_flush_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma sys_flush_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma sys_flush_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma sys_flush_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma sys_flush_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (sys_flush s sp v perms)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def]
    sys_flush_NC_Thread sys_flush_NC_Space
  by auto

lemma sys_flush_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (sys_flush s sp v perms)"
  unfolding Inv_Threads_Eq_Space_Threads_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def]
    sys_flush_NC_Thread sys_flush_NC_Space
  by auto

lemma sys_flush_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma sys_flush_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma sys_flush_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma sys_flush_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (sys_flush s sp v perms)"
  unfolding Inv_IntThreads_Utcb_Is_None_def sys_flush_def 
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma sys_flush_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma sys_flush_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (sys_flush s sp v perms)"
  unfolding sys_flush_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma sys_flush_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (sys_flush s sp v perms)"
  using assms unfolding Inv_Sigma0_Space_def sys_flush_def
  by auto

lemma sys_flush_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (sys_flush s sp v perms)"
  using assms unfolding Inv_RootServer_Space_def sys_flush_def
  by auto

lemma sys_flush_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (sys_flush s sp v perms)"
  using assms unfolding Inv_IntThreads_Space_def sys_flush_def
  by auto

lemma sys_flush_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (sys_flush s sp v perms)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] sys_flush_Inv_Idle_NotIn_Threads 
    sys_flush_Inv_Sigma0_In_Active sys_flush_Inv_Idle_Space_Is_KernelSpace
    sys_flush_Inv_RootServer_In_Active sys_flush_Inv_IntThreads_In_Active 
    sys_flush_Inv_Threads_Space_Dom    
    sys_flush_Inv_Threads_In_Config sys_flush_Inv_Active_In_Threads
    sys_flush_Inv_NThreads_Is_None sys_flush_Inv_Threads_IsNot_None 
    sys_flush_Inv_Threads_Space_In_Spaces sys_flush_Inv_Threads_Eq_Space_Threads
    sys_flush_Inv_Threads_Sche_In_Threads 
    sys_flush_Inv_NActive_Utcb_Is_None sys_flush_Inv_Active_Utcb_IsNot_None
    sys_flush_Inv_IntThreads_Utcb_Is_None sys_flush_Inv_Threads_Partner_In_Threads
    sys_flush_Inv_Threads_Incoming_In_Threads sys_flush_Inv_Sigma0_Space
    sys_flush_Inv_RootServer_Space sys_flush_Inv_IntThreads_Space
  by auto

lemma sys_flush_Invariant:
  assumes "Invariants s"
  shows "Invariants (sys_flush s sp v perms)"
  using Invariants_def sys_flush_Inv_Current sys_flush_Inv_Space 
    sys_flush_Inv_Thread assms
  by auto

lemma Flush_fpage_Invariant:
  assumes "Invariants s"
  shows "Invariants (Flush_fpage s sp v perms n)"
  using assms sys_flush_Invariant
  apply(induction n)
  by auto

section \<open>sys_map\<close>
subsection\<open>user\<close>
thm prod.case_eq_if
lemma sys_map_NC_User:
"thread_pager (sys_map s sp1 v1 sp2 v2 perms) = thread_pager s \<and>
 thread_handler (sys_map s sp1 v1 sp2 v2 perms) = thread_handler s \<and>
 thread_message (sys_map s sp1 v1 sp2 v2 perms) = thread_message s \<and>
 thread_rcvWindow (sys_map s sp1 v1 sp2 v2 perms) = thread_rcvWindow s \<and>
 thread_error (sys_map s sp1 v1 sp2 v2 perms) = thread_error s"
  unfolding sys_map_def Let_def
  by simp

subsection\<open>current\<close>
lemma sys_map_NC_Current:
"current_thread (sys_map s sp1 v1 sp2 v2 perms) = current_thread s \<and>
 current_time (sys_map s sp1 v1 sp2 v2 perms) = current_time s"
  unfolding sys_map_def
  by simp

subsection\<open>thread\<close>
lemma sys_map_NC_Thread:
"threads (sys_map s sp1 v1 sp2 v2 perms) = threads s \<and>
 active_threads (sys_map s sp1 v1 sp2 v2 perms) = active_threads s \<and>
 thread_space (sys_map s sp1 v1 sp2 v2 perms) = thread_space s \<and>
 thread_scheduler (sys_map s sp1 v1 sp2 v2 perms) = thread_scheduler s \<and>
 thread_state (sys_map s sp1 v1 sp2 v2 perms) = thread_state s \<and>
 thread_priority (sys_map s sp1 v1 sp2 v2 perms) = thread_priority s \<and>
 thread_total_quantum (sys_map s sp1 v1 sp2 v2 perms) = thread_total_quantum s \<and>
 thread_timeslice_length (sys_map s sp1 v1 sp2 v2 perms) = thread_timeslice_length s \<and>
 thread_current_timeslice (sys_map s sp1 v1 sp2 v2 perms) = thread_current_timeslice s"
  unfolding sys_map_def
  by simp

subsection\<open>space\<close>
lemma sys_map_NC_Space:
"spaces (sys_map s sp1 v1 sp2 v2 perms) = spaces s \<and>
 initialised_spaces (sys_map s sp1 v1 sp2 v2 perms) = initialised_spaces s \<and>
 space_threads (sys_map s sp1 v1 sp2 v2 perms) = space_threads s \<and>
 dom (space_mapping (sys_map s sp1 v1 sp2 v2 perms)) = dom (space_mapping s)"
  apply(auto simp add: sys_map_def spaces_def)
  apply(case_tac "space_mapping s xa = None")
  by auto

lemma sys_map_pre:
  assumes a1:"x \<noteq> Virtual sp_to v_to"
  shows "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding sys_map_def direct_path_def
  apply auto
  apply(cases "sp_to = Sigma0Space")
   apply simp
  apply simp
  apply(cases "perms \<noteq> {} \<and> s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and>
       (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum")
   prefer 2
  apply (smt option.discI)
  apply auto
  apply(case_tac "space_mapping s sp = None")
  apply auto
  apply (case_tac "yaa v = None \<and> (sp = sp_to \<longrightarrow> v \<noteq> v_to)")
   apply simp
  apply(case_tac "s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to)")
   apply auto
  apply(case_tac "sp = sp_to \<and> v = v_to")
  using a1 by auto

lemma sys_map_pre1:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
sp_to \<noteq> Sigma0Space \<and> s \<turnstile> (Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
perms \<noteq> {} \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
  using sys_map_def direct_path_def
  by (metis (no_types, lifting))

lemma sys_map_pre2:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
x = (Virtual sp_to v_to)"
proof(rule ccontr)
  assume a1:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" and a2:"\<not> s\<turnstile>x\<leadsto>\<^sup>1y" and
    "x \<noteq> Virtual sp_to v_to"
  then show False using sys_map_pre by metis
qed

lemma sys_map_pre3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
y = (Virtual sp_from v_from)"
proof(rule ccontr)
  assume a1:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" and a2:"\<not> s\<turnstile>x\<leadsto>\<^sup>1y" and
    a3:"y \<noteq> Virtual sp_from v_from"
  then have "x = Virtual sp_to v_to" using sys_map_pre2 by simp
  then have "\<not>(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" 
    using a2 a3 unfolding sys_map_def direct_path_def by auto
  then show False using sys_map_def using a1 by simp
qed

lemma sys_map_valid:
  assumes a1:"x \<noteq> Virtual sp_to v_to"
  shows "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile> x \<Longrightarrow> s \<turnstile> x"
  unfolding valid_page_def
  apply(cases x)
  subgoal
    using a1 sys_map_pre
    by fastforce
  by auto

subsubsection\<open>not influence other\<close>
lemma map_not_path:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow> 
the (space_mapping s sp) v = the (space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp) v"
  unfolding sys_map_def
  by auto

lemma map_not_path_perms:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow> 
snd(the(the (space_mapping s sp) v)) = 
snd(the(the (space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp) v))"
  unfolding sys_map_def
  by auto

lemma map_not_path_direct:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow> 
s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>1 y \<Longrightarrow> (sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>1 y"
  unfolding sys_map_def direct_path_def
  by auto

lemma map_not_path_tran1:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow>
s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y \<Longrightarrow> (sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y"
proof-
  assume a1:"s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y" and a2:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
  then show ?thesis
  proof(induction rule:tran_path.induct)
    case (one_path x y)
    then have "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" 
      using map_not_path_direct FatherIsVirtual by metis
    then show ?case using tran_path.intros by blast
  next
    case (tran_path x y z)
    then have "\<not> s\<turnstile>y\<leadsto>\<^sup>*(Virtual sp_to v_to)"
      using refl_tran by blast
    then have h1:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>y\<leadsto>\<^sup>+z"
      using tran_path by simp
    have "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" 
      using tran_path map_not_path_direct FatherIsVirtual by metis
    then show ?case using h1 tran_path.intros by simp
  qed
qed

lemma map_not_path_tran2:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow>
(sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y \<Longrightarrow> s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y"
proof-
  assume a1:"(sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y" and 
    a2:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
  then show ?thesis
  proof(induction rule:tran_path.induct)
    case (one_path x y)
    then have "x \<noteq> Virtual sp_to v_to"
      using a2 refl_path by metis
    then have "s\<turnstile> x\<leadsto>\<^sup>1 y" using one_path sys_map_pre by blast
    then show ?case using tran_path.intros by blast
  next
    case (tran_path x y z)
    then have h1:"s\<turnstile>x\<leadsto>\<^sup>1y" using rtran_path.intros sys_map_pre by metis
    then have "\<not> s\<turnstile>y\<leadsto>\<^sup>*(Virtual sp_to v_to)"
      using tran_path refl_tran by blast
    then have "s\<turnstile>y\<leadsto>\<^sup>+z"
      using tran_path by simp
    then show ?case using h1 tran_path.intros by simp
  qed
qed

lemma map_not_path_tran:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow>
(sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y = s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y"
  using map_not_path_tran1 map_not_path_tran2 by blast

lemma map_not_path_rtran:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow>
(sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>* y = s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* y"
  using map_not_path_tran rtran_tran by auto

thm map_not_path_tran
thm map_not_path_rtran

subsubsection\<open>influence to _self\<close>
lemma map_to_self_space:"sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and>
 perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> 
(\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<Longrightarrow>
space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp_to \<noteq> None \<and> 
the (space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp_to) v_to \<noteq> None \<and>
fst(the(the (space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp_to) v_to)) = Virtual sp_from v_from"
  unfolding sys_map_def
  using rtran_path.refl_path
  by auto

lemma map_to_self_perms:"sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and>
 perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> 
(\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<Longrightarrow>
snd (the(the (space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp_to) v_to)) = perms"
  unfolding sys_map_def
  using rtran_path.refl_path
  by auto

lemma map_to_self_direct:"sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and>
 perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> 
(\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<Longrightarrow>
(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp_to v_to)\<leadsto>\<^sup>1(Virtual sp_from v_from)"
  unfolding sys_map_def direct_path_def
  using rtran_path.refl_path
  by auto

subsubsection\<open>influence to _post\<close>
lemma map_to_post_space:"Inv_Space_HasNot_Loop s \<Longrightarrow> sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<and>
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to) \<Longrightarrow>
space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp \<noteq> None \<and> 
the (space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp) v = None"
  unfolding sys_map_def Inv_Space_HasNot_Loop_def
  using rtran_tran path_space
  by auto

lemma map_to_post_valid:"Inv_Space_HasNot_Loop s \<Longrightarrow> sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<and>
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to) \<Longrightarrow>
\<not>(sys_map s sp_from v_from sp_to v_to perms) \<turnstile> (Virtual sp v)"
  using map_to_post_space ValidVpageMappingNotNone by auto

lemma map_to_post_tran:"Inv_Space_HasNot_Loop s \<Longrightarrow> sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> (\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<Longrightarrow>
s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to) \<Longrightarrow>
\<not>(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+y"
  using map_to_post_space path_space1
  by metis

subsubsection\<open>not_influence to _pre\<close>
lemma map_to_pre_rtran:"Inv_Space_HasNot_Loop s \<Longrightarrow> s \<turnstile>(Virtual sp_to v_to)\<leadsto>\<^sup>+(Virtual sp v) \<Longrightarrow> 
s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*y = (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*y"
proof-
  assume a1:"Inv_Space_HasNot_Loop s" and a2:"s \<turnstile>(Virtual sp_to v_to)\<leadsto>\<^sup>+(Virtual sp v)"
  have h1:"\<not>s \<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to)"
    using a2 a1[unfolded Inv_Space_HasNot_Loop_def] by (meson basic14)
  then show ?thesis using map_not_path_rtran a1 a2 by simp
qed

subsubsection\<open>not_influence from _pre\<close>
lemma map_from_self_perms:"sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
space_mapping s sp_to \<noteq> None \<and> (\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<Longrightarrow>
snd(the(the(space_mapping (sys_map s sp_from v_from sp_to v_to perms) sp_from)v_from)) = 
snd(the(the(space_mapping s sp_from)v_from))"
proof-
  assume a1:"sp_to \<noteq> Sigma0Space" and a2:"perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> 
    sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> 
    (\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v))"
  have "\<not>s\<turnstile>(Virtual sp_from v_from) \<leadsto>\<^sup>*(Virtual sp_to v_to)"
    using a2 rtran_tran by auto
  then show ?thesis unfolding sys_map_def by auto
qed

lemma map_from_pre_rtran:"sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
space_mapping s sp_to \<noteq> None \<and> (\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v)) \<Longrightarrow>
s\<turnstile>(Virtual sp_from v_from) \<leadsto>\<^sup>* y = 
(sys_map s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>* y"
proof-
  assume a1:"sp_to \<noteq> Sigma0Space" and a2:"perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> 
    sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> 
    (\<forall>v. \<not> s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Virtual sp_to v))"
  thm map_not_path_rtran
  have "\<not>s\<turnstile>(Virtual sp_from v_from) \<leadsto>\<^sup>*(Virtual sp_to v_to)"
    using a2 rtran_tran by auto
  then show ?thesis using map_not_path_rtran by simp
qed

subsection\<open>IPC\<close>
lemma sys_map_NC_IPC:
"thread_ipc_partner (sys_map s sp1 v1 sp2 v2 perms) = thread_ipc_partner s \<and>
 thread_ipc_timeout (sys_map s sp1 v1 sp2 v2 perms) = thread_ipc_timeout s \<and>
 thread_incoming (sys_map s sp1 v1 sp2 v2 perms) =  thread_incoming s"
  unfolding sys_map_def
  by simp

subsection\<open>scheduling\<close>
lemma sys_map_NC_Scheduling:
"wait_queuing (sys_map s sp1 v1 sp2 v2 perms) = wait_queuing s \<and>
 ready_queuing (sys_map s sp1 v1 sp2 v2 perms) = ready_queuing s \<and>
 current_timeslice (sys_map s sp1 v1 sp2 v2 perms) = current_timeslice s"
  unfolding sys_map_def
  by simp

subsection\<open>Inv\<close>
subsubsection\<open>Current\<close>
lemma sys_map_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (sys_map s sp1 v1 sp2 v2 perms)"
  unfolding sys_map_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma sys_map_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (sys_map s sp1 v1 sp2 v2 perms)"
  unfolding sys_map_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma sys_map_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (sys_map s sp1 v1 sp2 v2 perms)"
  using sys_map_Inv_Current_Thread_In_Active sys_map_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
    by auto

subsubsection\<open>Space\<close>
lemma sys_map_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Spaces_In_Config_def spaces_def
  using p1[unfolded Inv_Space_Spaces_In_Config_def spaces_def]
  unfolding sys_map_def
  apply auto
  apply(case_tac "space_mapping s x = None")
  by auto

lemma sys_map_Inv_Space_Perms_IsNot_Empty1:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
      and p4:"Inv_Space_HasNot_Loop s"
    shows "get_perms (sys_map s sp_from v_from sp_to v_to perms) sp v \<noteq> {}"
proof(cases "Virtual sp v = Virtual sp_to v_to")
  case True
  then show ?thesis using map_to_self_perms p2 get_perms_def by auto
next
  case False
  then have "s\<turnstile>(Virtual sp v)" using sys_map_valid p3 by blast
  then have h1:"get_perms s sp v \<noteq> {}"using p1 Inv_Space_Perms_IsNot_Empty_def by simp
  have "\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to)" using map_to_post_valid p3 p2 p4 by metis
  then have "\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to)" using False rtran_tran by simp
  then show ?thesis using map_not_path_perms h1 get_perms_def by simp
qed

lemma sys_map_Inv_Space_Perms_IsNot_Empty2:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
      and p2:"\<not>(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_Perms_IsNot_Empty (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def
  using assms by auto

lemma sys_map_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
      and p2:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_Perms_IsNot_Empty (sys_map s sp_from v_from sp_to v_to perms)"
  using assms sys_map_Inv_Space_Perms_IsNot_Empty1 sys_map_Inv_Space_Perms_IsNot_Empty2
    Inv_Space_Perms_IsNot_Empty_def
  by metis

thm map_not_path_tran
lemma sys_map_Inv_Space_HasNot_Loop11:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)"
      and p4:"s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
    shows "False"
proof-
  have "(Virtual sp v1) = (Virtual sp_to v_to) \<or> s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>+ (Virtual sp_to v_to)"
    using p4 rtran_tran by simp
  then show ?thesis
  proof
    assume a11:"(Virtual sp v1) = (Virtual sp_to v_to)"
    then have "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>1(Virtual sp_from v_from)"
      using map_to_self_direct p2 by simp
    then have "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>*(Virtual sp v2)"
      using basic15 p3 by simp
    then have "s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>*(Virtual sp v2)"
      using map_from_pre_rtran p1 p2 by simp
    then have "(Virtual sp_from v_from) = (Virtual sp v2)" using rtran_tran p2 a11 by auto
    then show ?thesis using p2 a11 by auto
  next
    assume a12:"s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>+ (Virtual sp_to v_to)"
    then have "\<forall>y. \<not>(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+y"
      using map_to_post_tran p1 p2 by simp
    then show ?thesis using p3 by blast
  qed
qed

lemma sys_map_Inv_Space_HasNot_Loop12:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)"
      and p4:"\<not>s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
    shows "False"
proof-
  have "s\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)" using map_not_path_tran p1 p3 p4 by simp
  then show ?thesis using p1[unfolded Inv_Space_HasNot_Loop_def] by simp
qed

lemma sys_map_Inv_Space_HasNot_Loop1:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
    shows "Inv_Space_HasNot_Loop (sys_map s sp_from v_from sp_to v_to perms)"
  using sys_map_Inv_Space_HasNot_Loop11 sys_map_Inv_Space_HasNot_Loop12
    p1 p2 Inv_Space_HasNot_Loop_def
  by metis

lemma sys_map_Inv_Space_HasNot_Loop2:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"\<not>(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_HasNot_Loop (sys_map s sp_from v_from sp_to v_to perms)"
  using p1 p2 unfolding sys_map_def by auto

lemma sys_map_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (sys_map s sp_from v_from sp_to v_to perms)"
  using p1 sys_map_Inv_Space_HasNot_Loop1 sys_map_Inv_Space_HasNot_Loop2
  by metis

lemma sys_map_Inv_Space_Perms_Subset11:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p4:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
      and p5:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
      and p6:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    shows "get_perms (sys_map s sp_from v_from sp_to v_to perms) sp1 v1
       \<subseteq> get_perms (sys_map s sp_from v_from sp_to v_to perms) sp2 v2"
  thm map_to_post_tran
proof-
  have h1:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>+ (Virtual sp_to v_to) \<or> (Virtual sp1 v1) = (Virtual sp_to v_to)"
    using p5 rtran_tran by blast
  then show ?thesis
  proof
    assume a11:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp_to v_to)"
    then have "\<forall>y. \<not>(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+y"
      using map_to_post_tran p2 p4 by simp
    then show ?thesis using p6
      using one_path by auto
  next
    assume a21:"Virtual sp1 v1 = Virtual sp_to v_to"
    then have h22:"Virtual sp2 v2 = Virtual sp_from v_from"
      using map_to_self_direct p4 p6 by (metis Space_Father_Is_Unique)
    have h23:"get_perms (sys_map s sp_from v_from sp_to v_to perms) sp_to v_to = perms"
      unfolding get_perms_def using map_to_self_perms p4 by simp
    have "get_perms s sp_from v_from = get_perms (sys_map s sp_from v_from sp_to v_to perms) sp_from v_from"
      unfolding get_perms_def using map_from_self_perms p4 by simp
    thm map_to_self_perms
    then show ?thesis using a21 h22 h23 p4 by auto
  qed
qed

lemma sys_map_Inv_Space_Perms_Subset12:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"\<not>s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    shows "get_perms (sys_map s sp_from v_from sp_to v_to perms) sp1 v1
       \<subseteq> get_perms (sys_map s sp_from v_from sp_to v_to perms) sp2 v2"
  thm map_not_path_perms
proof-
  have h1:"get_perms (sys_map s sp_from v_from sp_to v_to perms) sp1 v1 = get_perms s sp1 v1"
    unfolding get_perms_def using p2 map_not_path_perms by simp
  have h2:"(Virtual sp1 v1) \<noteq> (Virtual sp_to v_to)" using p2 refl_path by blast
  then have h3:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)" using sys_map_pre p3 by blast
  then have h4:"\<not>s \<turnstile> (Virtual sp2 v2) \<leadsto>\<^sup>* (Virtual sp_to v_to)" using refl_tran p2 by blast
  then have h5:"get_perms (sys_map s sp_from v_from sp_to v_to perms) sp2 v2 = get_perms s sp2 v2"
    unfolding get_perms_def using map_not_path_perms by simp
  have "get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" using h3 p1 Inv_Space_Perms_Subset_def by simp
  then show ?thesis using h1 h5 by blast
qed

lemma sys_map_Inv_Space_Perms_Subset1:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_Perms_Subset (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Perms_Subset_def
  using assms sys_map_Inv_Space_Perms_Subset11 sys_map_Inv_Space_Perms_Subset12 
  by metis

lemma sys_map_Inv_Space_Perms_Subset2:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"\<not>(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_Perms_Subset (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def
  using p1 p2 by auto

lemma sys_map_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_Perms_Subset (sys_map s sp_from v_from sp_to v_to perms)"
  using assms sys_map_Inv_Space_Perms_Subset1 sys_map_Inv_Space_Perms_Subset2
  by metis

lemma sys_map_Inv_Space_Valid_Has_Real11:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
      and p4:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "\<exists>r. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
proof(cases "Virtual sp v = Virtual sp_to v_to")
  case True
  then have h1:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1(Virtual sp_from v_from)"
    using map_to_self_direct p4 by simp
  have "\<exists>r. s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>*(Real r)"
    using p1 p4 Inv_Space_Valid_Has_Real_def by simp
  then obtain r where "s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>*(Real r)" by auto
  then have "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>*(Real r)" 
    using map_from_pre_rtran p4 by simp
  then show ?thesis using h1 refl_tran True by blast
next
  case False
  then have "s\<turnstile>(Virtual sp v)" using sys_map_valid p3 by blast
  then have "\<exists>r. s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"using p1 Inv_Space_Valid_Has_Real_def by simp
  then obtain r where h1:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)" by blast
  have "\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to)" using p4 map_to_post_valid p3 p2 by metis
  then have "\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to)" using False rtran_tran by simp
  then have "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
    using map_not_path_rtran h1 by simp
  then show ?thesis by blast
qed

lemma sys_map_Inv_Space_Valid_Has_Real12:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"\<not>((s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum))"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
    shows "\<exists>r. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
proof-
  have "(sys_map s sp_from v_from sp_to v_to perms) = s"
    unfolding sys_map_def using p2 by auto
  then show ?thesis using p1 p3 Inv_Space_Valid_Has_Real_def by auto
qed

lemma sys_map_Inv_Space_Valid_Has_Real1:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
    shows "\<exists>r. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
  using assms sys_map_Inv_Space_Valid_Has_Real11 sys_map_Inv_Space_Valid_Has_Real12
  by metis

lemma sys_map_Inv_Space_Valid_Has_Real21:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"\<exists>r. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
      and p4:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
proof(cases "Virtual sp v = Virtual sp_to v_to")
  case True
  then have h1:"(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1(Virtual sp_from v_from)"
    using map_to_self_direct p4 by simp
  then show ?thesis using valid_page_def True by auto
next
  case False
  then have "\<exists>y. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v) \<leadsto>\<^sup>1 y"
    using p3 rtran_path.cases by blast
  then show ?thesis using valid_page_def by auto
qed

lemma sys_map_Inv_Space_Valid_Has_Real22:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"\<not>((s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum))"
      and p3:"\<exists>r. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
    shows "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
proof-
  have "(sys_map s sp_from v_from sp_to v_to perms) = s"
    unfolding sys_map_def using p2 by auto
  then show ?thesis using p1 p3 Inv_Space_Valid_Has_Real_def by auto
qed

lemma sys_map_Inv_Space_Valid_Has_Real2:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Perms_Subset s"
      and p4:"\<exists>r. (sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
    shows "(sys_map s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
  using assms sys_map_Inv_Space_Valid_Has_Real21 sys_map_Inv_Space_Valid_Has_Real22
  by metis

lemma sys_map_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Valid_Has_Real (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Valid_Has_Real_def
  apply rule
  apply (case_tac x)
  subgoal
    using assms sys_map_Inv_Space_Valid_Has_Real1 sys_map_Inv_Space_Valid_Has_Real2
    by blast
  using valid_page_def rtran_tran by auto

lemma sys_map_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
     sys_map_NC_Space 
  by blast

lemma sys_map_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
  shows "Inv_Space_Spaces_IsNot_None (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Spaces_IsNot_None_def
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
     sys_map_NC_Space 
  by auto

lemma sys_map_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
  shows "Inv_Space_Vpage_Range (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def]
  apply auto
  by (metis page_t.sel(2) sys_map_def sys_map_valid)

lemma sys_map_Inv_Space:
  assumes "Inv_Space s"
  shows "Inv_Space (sys_map s sp_from v_from sp_to v_to perms)"
  using Inv_Space_def assms sys_map_Inv_Space_Spaces_In_Config
    sys_map_Inv_Space_HasNot_Loop sys_map_Inv_Space_Perms_IsNot_Empty
    sys_map_Inv_Space_Perms_Subset sys_map_Inv_Space_Valid_Has_Real
    sys_map_Inv_Space_InitialSpaces_In_Spaces 
    sys_map_Inv_Space_Spaces_IsNot_None sys_map_Inv_Space_Vpage_Range
  by auto

subsubsection\<open>Thread\<close>
lemma sys_map_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma sys_map_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma sys_map_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma sys_map_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma sys_map_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma sys_map_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma sys_map_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma sys_map_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma sys_map_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma sys_map_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma sys_map_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def]
    sys_map_NC_Thread sys_map_NC_Space
  by auto

lemma sys_map_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Threads_Eq_Space_Threads_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def]
    sys_map_NC_Thread sys_map_NC_Space
  by auto

lemma sys_map_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma sys_map_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma sys_map_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma sys_map_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_IntThreads_Utcb_Is_None_def sys_map_def 
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma sys_map_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma sys_map_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding sys_map_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma sys_map_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (sys_map s sp_from v_from sp_to v_to perms)"
  using assms unfolding Inv_Sigma0_Space_def sys_map_def
  by auto

lemma sys_map_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (sys_map s sp_from v_from sp_to v_to perms)"
  using assms unfolding Inv_RootServer_Space_def sys_map_def
  by auto

lemma sys_map_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (sys_map s sp_from v_from sp_to v_to perms)"
  using assms unfolding Inv_IntThreads_Space_def sys_map_def
  by auto

lemma sys_map_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (sys_map s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] sys_map_Inv_Idle_NotIn_Threads 
    sys_map_Inv_Sigma0_In_Active sys_map_Inv_Idle_Space_Is_KernelSpace
    sys_map_Inv_RootServer_In_Active sys_map_Inv_IntThreads_In_Active
    sys_map_Inv_Threads_Space_Dom
    sys_map_Inv_Threads_In_Config sys_map_Inv_Active_In_Threads 
    sys_map_Inv_NThreads_Is_None sys_map_Inv_Threads_IsNot_None 
    sys_map_Inv_Threads_Space_In_Spaces sys_map_Inv_Threads_Eq_Space_Threads
    sys_map_Inv_Threads_Sche_In_Threads 
    sys_map_Inv_NActive_Utcb_Is_None sys_map_Inv_Active_Utcb_IsNot_None
    sys_map_Inv_IntThreads_Utcb_Is_None sys_map_Inv_Threads_Partner_In_Threads
    sys_map_Inv_Threads_Incoming_In_Threads sys_map_Inv_Sigma0_Space
    sys_map_Inv_RootServer_Space sys_map_Inv_IntThreads_Space
  by auto

lemma sys_map_Invariant:
  assumes "Invariants s"
  shows "Invariants (sys_map s sp_from v_from sp_to v_to perms)"
  using Invariants_def sys_map_Inv_Current sys_map_Inv_Space 
    sys_map_Inv_Thread assms
  by auto

lemma Map_fpage_Invariant:
  assumes "Invariants s"
  shows "Invariants (Map_fpage s sp1 v1 sp2 v2 perms n)"
  using assms sys_map_Invariant
  apply(induction n)
  by auto

section \<open>sys_grant\<close>
subsection\<open>user\<close>
lemma sys_grant_NC_User:
"thread_pager (sys_grant s sp1 v1 sp2 v2 perms) = thread_pager s \<and>
 thread_handler (sys_grant s sp1 v1 sp2 v2 perms) = thread_handler s \<and>
 thread_message (sys_grant s sp1 v1 sp2 v2 perms) = thread_message s \<and>
 thread_rcvWindow (sys_grant s sp1 v1 sp2 v2 perms) = thread_rcvWindow s \<and>
 thread_error (sys_grant s sp1 v1 sp2 v2 perms) = thread_error s"
  unfolding sys_grant_def 
  by simp

subsection\<open>current\<close>
lemma sys_grant_NC_Current:
"current_thread (sys_grant s sp1 v1 sp2 v2 perms) = current_thread s \<and>
 current_time (sys_grant s sp1 v1 sp2 v2 perms) = current_time s"
  unfolding sys_grant_def Let_def
  using sys_flush_NC_Current
  by auto

subsection\<open>thread\<close>
lemma sys_grant_NC_Thread:
"threads (sys_grant s sp1 v1 sp2 v2 perms) = threads s \<and>
 active_threads (sys_grant s sp1 v1 sp2 v2 perms) = active_threads s \<and>
 thread_space (sys_grant s sp1 v1 sp2 v2 perms) = thread_space s \<and>
 thread_scheduler (sys_grant s sp1 v1 sp2 v2 perms) = thread_scheduler s \<and>
 thread_state (sys_grant s sp1 v1 sp2 v2 perms) = thread_state s \<and>
 thread_priority (sys_grant s sp1 v1 sp2 v2 perms) = thread_priority s \<and>
 thread_total_quantum (sys_grant s sp1 v1 sp2 v2 perms) = thread_total_quantum s \<and>
 thread_timeslice_length (sys_grant s sp1 v1 sp2 v2 perms) = thread_timeslice_length s \<and>
 thread_current_timeslice (sys_grant s sp1 v1 sp2 v2 perms) = thread_current_timeslice s"
  unfolding sys_grant_def Let_def
  using sys_flush_NC_Thread
  by auto    

subsection\<open>space\<close>
lemma sys_grant_NC_Space:
"spaces (sys_grant s sp1 v1 sp2 v2 perms) = spaces s \<and>
 initialised_spaces (sys_grant s sp1 v1 sp2 v2 perms) = initialised_spaces s \<and>
 space_threads (sys_grant s sp1 v1 sp2 v2 perms) = space_threads s \<and>
 dom (space_mapping (sys_grant s sp1 v1 sp2 v2 perms)) = dom (space_mapping s)"
  apply(auto simp add: sys_grant_def spaces_def)
  apply(case_tac "space_mapping s xa = None")
  by auto

lemma sys_grant_pre:
  assumes a1:"x \<noteq> Virtual sp_to v_to"
  shows "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding sys_grant_def direct_path_def
  apply auto
  apply(cases "sp_to = Sigma0Space")
   apply simp
  apply simp
  apply(cases "perms \<noteq> {} \<and> s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and>
       (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum")
   prefer 2
  apply (smt option.discI)
  apply auto
  apply(case_tac "space_mapping s sp = None")
  apply auto
  apply (case_tac "yaa v = None \<and> (sp = sp_to \<longrightarrow> v \<noteq> v_to)")
   apply simp
  apply(case_tac "s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to) \<or> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_from v_from)")
   apply auto
  apply(case_tac "sp = sp_to \<and> v = v_to")
  using a1 by auto

lemma sys_grant_pre1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
sp_to \<noteq> Sigma0Space \<and> s \<turnstile> (Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> 
perms \<subseteq> get_perms s sp_from v_from \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and>
(\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v))"
  using sys_grant_def direct_path_def
  by (metis (no_types, lifting))

lemma sys_grant_pre2:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
x = (Virtual sp_to v_to)"
proof(rule ccontr)
  assume a1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" and a2:"\<not> s\<turnstile>x\<leadsto>\<^sup>1y" and
    "x \<noteq> Virtual sp_to v_to"
  then show False using sys_grant_pre by metis
qed

lemma sys_grant_pre3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
y = fst (the (the (space_mapping s sp_from) v_from))"
proof(rule ccontr)
  assume a1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" and a2:"\<not> s\<turnstile>x\<leadsto>\<^sup>1y" and
    a3:"y \<noteq> fst (the (the (space_mapping s sp_from) v_from))"
  then have "x = Virtual sp_to v_to" using sys_grant_pre2 by simp
  then have "\<not>(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" 
    using a2 a3 unfolding sys_grant_def direct_path_def by auto
  then show False using sys_grant_def using a1 by simp
qed

lemma sys_grant_valid:
  assumes a1:"x \<noteq> Virtual sp_to v_to"
  shows "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile> x \<Longrightarrow> s \<turnstile> x"
  unfolding valid_page_def
  apply(cases x)
  subgoal
    using a1 sys_grant_pre
    by fastforce
  by auto

subsubsection\<open>not influence other\<close>
lemma grant_not_path:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<and> 
\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from) \<Longrightarrow> 
the (space_mapping s sp) v = the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp) v"
  unfolding sys_grant_def
  by auto

lemma grant_not_path_perms:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to)  \<and> 
\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from)\<Longrightarrow> 
snd(the(the (space_mapping s sp) v)) = 
snd(the(the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp) v))"
  unfolding sys_grant_def
  by auto

lemma grant_not_path_direct:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to)
 \<and> \<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from) \<Longrightarrow> 
s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>1 y \<Longrightarrow> (sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>1 y"
  unfolding sys_grant_def direct_path_def
  by auto

lemma grant_not_path_tran1:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) 
 \<and> \<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from) \<Longrightarrow>
s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y \<Longrightarrow> (sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y"
proof-
  assume a1:"s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y" and a2:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<and> 
    \<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from)"
  then show ?thesis
  proof(induction rule:tran_path.induct)
    case (one_path x y)
    then have "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" 
      using grant_not_path_direct FatherIsVirtual by metis
    then show ?case using tran_path.intros by blast
  next
    case (tran_path x y z)
    then have "\<not> s\<turnstile>y\<leadsto>\<^sup>*(Virtual sp_to v_to) \<and> \<not> s\<turnstile>y\<leadsto>\<^sup>*(Virtual sp_from v_from)"
      using refl_tran by blast
    then have h1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>y\<leadsto>\<^sup>+z"
      using tran_path by simp
    have "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>x\<leadsto>\<^sup>1y" 
      using tran_path grant_not_path_direct FatherIsVirtual by metis
    then show ?case using h1 tran_path.intros by simp
  qed
qed

lemma grant_not_path_tran2:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<Longrightarrow>
(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y \<Longrightarrow> s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y"
proof-
  assume a1:"(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y" and 
    a2:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to)"
  then show ?thesis
  proof(induction rule:tran_path.induct)
    case (one_path x y)
    then have "x \<noteq> Virtual sp_to v_to"
      using a2 refl_path by metis
    then have "s\<turnstile> x\<leadsto>\<^sup>1 y" using one_path sys_grant_pre by blast
    then show ?case using tran_path.intros by blast
  next
    case (tran_path x y z)
    then have h1:"s\<turnstile>x\<leadsto>\<^sup>1y" using rtran_path.intros sys_grant_pre by metis
    then have "\<not> s\<turnstile>y\<leadsto>\<^sup>*(Virtual sp_to v_to)"
      using tran_path refl_tran by blast
    then have "s\<turnstile>y\<leadsto>\<^sup>+z"
      using tran_path by simp
    then show ?case using h1 tran_path.intros by simp
  qed
qed

lemma grant_not_path_tran:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<and> 
\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from) \<Longrightarrow>
(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>+ y = s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>+ y"
  using grant_not_path_tran1 grant_not_path_tran2 by blast

lemma grant_not_path_rtran:"\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<and> 
\<not>s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* (Virtual sp_from v_from) \<Longrightarrow>
(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(Virtual sp v) \<leadsto>\<^sup>* y = s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>* y"
  using grant_not_path_tran rtran_tran by auto

thm grant_not_path_tran
thm grant_not_path_rtran

subsubsection\<open>influence to _self\<close>
lemma grant_to_self_space:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> 
sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<Longrightarrow>
space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp_to \<noteq> None \<and> 
the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp_to) v_to \<noteq> None \<and>
fst(the(the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp_to) v_to)) = 
(fst (the (the (space_mapping s sp_from) v_from)))"
  unfolding sys_grant_def
  using rtran_path.refl_path
  by auto

lemma grant_to_self_perms:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and>
 perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<Longrightarrow>
snd (the(the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp_to) v_to)) = perms"
  unfolding sys_grant_def
  using rtran_path.refl_path
  by auto

lemma grant_to_self_direct:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> s\<turnstile>(Virtual sp_from v_from) \<and> 
sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<Longrightarrow>
(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp_to v_to)\<leadsto>\<^sup>1
(fst (the (the (space_mapping s sp_from) v_from)))"
  unfolding sys_grant_def direct_path_def
  using rtran_path.refl_path
  by auto

subsubsection\<open>influence to or from _post\<close>
lemma grant_path_space:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and>
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> (Virtual sp v) \<noteq> (Virtual sp_to v_to) \<Longrightarrow>
s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to) \<or> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_from v_from) \<Longrightarrow>
space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp \<noteq> None \<and> 
the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp) v = None"
proof-
  assume a1:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> 
    s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
    (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and>
    space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum" and 
    a2:"(Virtual sp v) \<noteq> (Virtual sp_to v_to)" and 
    a3:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to) \<or> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_from v_from)"
  have "\<exists>y. s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1 y"
  proof(rule ccontr)
    assume a11:"\<nexists>y. s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1y"
    then have "(Virtual sp v) = (Virtual sp_from v_from)"
      using a2 a3 rtran_tran using basic3 by blast
    then show False using a11 a1 valid_page_def by auto
  qed
  then have "space_mapping s sp \<noteq> None" using direct_path_def by auto
  then show ?thesis unfolding sys_grant_def using a1 a2 a3 by auto
qed

lemma grant_path_valid:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and>
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> (Virtual sp v) \<noteq> (Virtual sp_to v_to) \<Longrightarrow>
s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to) \<or> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_from v_from) \<Longrightarrow> 
\<not>(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile> (Virtual sp v)"
  using grant_path_space ValidVpageMappingNotNone by auto

subsubsection\<open>influence to _post\<close>
lemma grant_to_post_space:"Inv_Space_HasNot_Loop s \<Longrightarrow> sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and>
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to) \<Longrightarrow>
space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp \<noteq> None \<and> 
the (space_mapping (sys_grant s sp_from v_from sp_to v_to perms) sp) v = None"
  unfolding sys_grant_def Inv_Space_HasNot_Loop_def
  using rtran_tran path_space
  by auto

lemma grant_to_post_valid:"Inv_Space_HasNot_Loop s \<Longrightarrow> sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and>
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to) \<Longrightarrow>
\<not>(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile> (Virtual sp v)"
  using grant_to_post_space ValidVpageMappingNotNone by auto

lemma grant_to_post_tran:"Inv_Space_HasNot_Loop s \<Longrightarrow> sp_to \<noteq> Sigma0Space \<Longrightarrow> perms \<noteq> {} \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from  \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and> 
space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum \<Longrightarrow> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+(Virtual sp_to v_to) \<Longrightarrow>
\<not>(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>+y"
  using grant_to_post_space path_space1
  by metis

subsubsection \<open>not influence from _pre\<close>
thm grant_not_path_rtran
lemma grant_from_pre_rtran:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<Longrightarrow>
Inv_Space_HasNot_Loop s \<Longrightarrow> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* y = 
(sys_grant s sp_from v_from sp_to v_to perms) \<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>* y"
proof-
  assume a1:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> 
    s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
    (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v))" and
    a2:"Inv_Space_HasNot_Loop s"
  from a1 have h1:"\<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v_to)"
    by simp
  have "s\<turnstile>(Virtual sp_from v_from) \<leadsto>\<^sup>1 (fst (the (the (space_mapping s sp_from) v_from)))"
    using direct_path_def a1 valid_page_def by auto
  then have h2:"\<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_from v_from)"
    using basic111 a2[unfolded Inv_Space_HasNot_Loop_def] by metis
  then show ?thesis using grant_not_path_rtran h1 FatherIsVirtual rtran_path.simps by smt
qed

lemma grant_from_pre_perms:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> 
s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
(\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<Longrightarrow>
Inv_Space_HasNot_Loop s \<Longrightarrow> (fst (the (the (space_mapping s sp_from) v_from))) = Virtual x y \<Longrightarrow>
get_perms s x y = get_perms (sys_grant s sp_from v_from sp_to v_to perms) x y"
proof-
  assume a1:"sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> 
    s\<turnstile>(Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
    (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v))" and
    a2:"Inv_Space_HasNot_Loop s" and a3:"(fst (the (the (space_mapping s sp_from) v_from))) = Virtual x y"
  from a1 have h1:"\<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v_to)"
    by simp
  have "s\<turnstile>(Virtual sp_from v_from) \<leadsto>\<^sup>1 (fst (the (the (space_mapping s sp_from) v_from)))"
    using direct_path_def a1 valid_page_def by auto
  then have h2:"\<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_from v_from)"
    using basic111 a2[unfolded Inv_Space_HasNot_Loop_def] by metis
  then show ?thesis using grant_not_path_perms get_perms_def h1 FatherIsVirtual rtran_path.simps a3
    by smt
qed

subsection\<open>IPC\<close>
lemma sys_grant_NC_IPC:
"thread_ipc_partner (sys_grant s sp1 v1 sp2 v2 perms) = thread_ipc_partner s \<and>
 thread_ipc_timeout (sys_grant s sp1 v1 sp2 v2 perms) = thread_ipc_timeout s \<and>
 thread_incoming (sys_grant s sp1 v1 sp2 v2 perms) =  thread_incoming s"
  unfolding sys_grant_def
  by auto

subsection\<open>scheduling\<close>
lemma sys_grant_NC_Scheduling:
"wait_queuing (sys_grant s sp1 v1 sp2 v2 perms) = wait_queuing s \<and>
 ready_queuing (sys_grant s sp1 v1 sp2 v2 perms) = ready_queuing s \<and>
 current_timeslice (sys_grant s sp1 v1 sp2 v2 perms) = current_timeslice s"
  unfolding sys_grant_def
  by auto

subsection\<open>Inv\<close>
subsubsection\<open>Current\<close>
lemma sys_grant_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (sys_grant s sp1 v1 sp2 v2 perms)"
  unfolding sys_grant_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma sys_grant_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (sys_grant s sp1 v1 sp2 v2 perms)"
  unfolding sys_grant_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma sys_grant_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (sys_grant s sp1 v1 sp2 v2 perms)"
  using sys_grant_Inv_Current_Thread_In_Active sys_grant_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
    by auto

subsubsection\<open>Space\<close>
lemma sys_grant_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Spaces_In_Config_def spaces_def
  using p1[unfolded Inv_Space_Spaces_In_Config_def spaces_def]
  unfolding sys_grant_def
  apply auto
  apply(case_tac "space_mapping s x = None")
  by auto

lemma sys_grant_Inv_Space_Perms_IsNot_Empty1:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
      and p4:"Inv_Space_HasNot_Loop s"
    shows "get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp v \<noteq> {}"
proof(cases "Virtual sp v = Virtual sp_to v_to")
  case True
  then show ?thesis using grant_to_self_perms p2 get_perms_def by auto
next
  case False
  then have "s\<turnstile>(Virtual sp v)" using sys_grant_valid p3 by blast
  then have h1:"get_perms s sp v \<noteq> {}"using p1 Inv_Space_Perms_IsNot_Empty_def by simp
  have "\<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to) \<and> \<not>s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_from v_from)" 
     using grant_path_valid p3 p2 False by metis
  then show ?thesis using grant_not_path_perms h1 get_perms_def by simp
qed

lemma sys_grant_Inv_Space_Perms_IsNot_Empty2:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
      and p2:"\<not>(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_Perms_IsNot_Empty (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def
  using assms by auto

lemma sys_grant_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
      and p2:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_Perms_IsNot_Empty (sys_grant s sp_from v_from sp_to v_to perms)"
  using assms sys_grant_Inv_Space_Perms_IsNot_Empty1 sys_grant_Inv_Space_Perms_IsNot_Empty2
    Inv_Space_Perms_IsNot_Empty_def
  by metis

thm grant_not_path_tran
lemma sys_grant_Inv_Space_HasNot_Loop11:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)"
      and p4:"s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<or>
              s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>* (Virtual sp_from v_from)"
    shows "False"
proof(cases "Virtual sp v1 = Virtual sp_to v_to")
  case True
  then have h1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>1
    (fst (the (the (space_mapping s sp_from) v_from)))"
    using grant_to_self_direct p2 by simp
  then have h2:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>
      (fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp v2)"
    using p3 basic15 by simp
  then have h3:"s\<turnstile> (fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp v2)"
    using grant_from_pre_rtran p1 p2 by simp
  then show ?thesis using True p2 by auto
next
  case False
  thm grant_path_valid
  then have "\<not>(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)"
    using grant_path_valid p2 p4 by simp
  then show ?thesis using p3 valid_page_def path_valid by blast
qed

lemma sys_grant_Inv_Space_HasNot_Loop12:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)"
      and p4:"\<not>s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<and>
              \<not>s \<turnstile> (Virtual sp v1) \<leadsto>\<^sup>* (Virtual sp_from v_from)"
    shows "False"
proof-
  have "s\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>+(Virtual sp v2)" using grant_not_path_tran p1 p3 p4 by simp
  then show ?thesis using p1[unfolded Inv_Space_HasNot_Loop_def] by simp
qed

lemma sys_grant_Inv_Space_HasNot_Loop1:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum"
    shows "Inv_Space_HasNot_Loop (sys_grant s sp_from v_from sp_to v_to perms)"
  using sys_grant_Inv_Space_HasNot_Loop11 sys_grant_Inv_Space_HasNot_Loop12
    p1 p2 Inv_Space_HasNot_Loop_def
  by metis

lemma sys_grant_Inv_Space_HasNot_Loop2:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"\<not>(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_HasNot_Loop (sys_grant s sp_from v_from sp_to v_to perms)"
  using p1 p2 unfolding sys_grant_def by auto

lemma sys_grant_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (sys_grant s sp_from v_from sp_to v_to perms)"
  using p1 sys_grant_Inv_Space_HasNot_Loop1 sys_grant_Inv_Space_HasNot_Loop2
  by metis

lemma sys_grant_Inv_Space_Perms_Subset11:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile> (fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
      and p4:"s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<or> 
              s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>* (Virtual sp_from v_from)"
      and p5:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    shows "get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp1 v1
       \<subseteq> get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp2 v2"
proof(cases "Virtual sp1 v1 = Virtual sp_to v_to")
  case True
  then have h1:"get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp1 v1 = perms"
    using grant_to_self_perms get_perms_def p3 by simp
  have h2:"Virtual sp2 v2 = fst (the(the (space_mapping s sp_from) v_from))"
    using grant_to_self_direct p5 p3 True direct_path_def
    by (metis (no_types, hide_lams) Space_Father_Is_Unique page_t.inject(1))
  then have "s\<turnstile>(Virtual sp_from v_from) \<leadsto>\<^sup>1 (Virtual sp2 v2)"
    using p3 valid_page_def direct_path_def by auto
  then have h3:"get_perms s sp_from v_from \<subseteq> get_perms s sp2 v2"
    using p1 Inv_Space_Perms_Subset_def by simp
  have h4:"get_perms s sp2 v2 = get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp2 v2"
    using h2 grant_from_pre_perms p2 p3 by simp
  then show ?thesis using h1 p3 h3 h4 by auto
next
  case False
  thm grant_path_valid
  then have "\<not>(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp1 v1)"
    using grant_path_valid p3 p4 by simp
  then show ?thesis using p5 valid_page_def by auto
qed

lemma sys_grant_Inv_Space_Perms_Subset12:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"\<not>s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<and> 
              \<not>s \<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>* (Virtual sp_from v_from)"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    shows "get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp1 v1
       \<subseteq> get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp2 v2"
  thm grant_not_path_perms
proof-
  have h1:"get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp1 v1 = get_perms s sp1 v1"
    unfolding get_perms_def using p2 grant_not_path_perms by simp
  have h2:"(Virtual sp1 v1) \<noteq> (Virtual sp_to v_to)" using p2 refl_path by blast
  then have h3:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)" using sys_grant_pre p3 by blast
  then have h4:"\<not>s \<turnstile> (Virtual sp2 v2) \<leadsto>\<^sup>* (Virtual sp_to v_to)" using refl_tran p2 by blast
  have h5:"(Virtual sp1 v1) \<noteq> (Virtual sp_from v_from)" using p2 refl_path by blast
  then have h6:"\<not>s \<turnstile> (Virtual sp2 v2) \<leadsto>\<^sup>* (Virtual sp_from v_from)" using refl_tran p2 h3 by blast
  have h7:"get_perms (sys_grant s sp_from v_from sp_to v_to perms) sp2 v2 = get_perms s sp2 v2"
    unfolding get_perms_def using grant_not_path_perms h4 h6 by simp
  have "get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" using h3 p1 Inv_Space_Perms_Subset_def by simp
  then show ?thesis using h1 h7 by blast
qed

lemma sys_grant_Inv_Space_Perms_Subset1:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
            sp_from \<noteq> sp_to \<and> (\<forall>v. \<not>s \<turnstile>(fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "Inv_Space_Perms_Subset (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Perms_Subset_def
  using assms sys_grant_Inv_Space_Perms_Subset11 sys_grant_Inv_Space_Perms_Subset12 
  by metis

lemma sys_grant_Inv_Space_Perms_Subset2:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"\<not>((s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and> 
            (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum))"
    shows "Inv_Space_Perms_Subset (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def
  using p1 p2 by auto

lemma sys_grant_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_Perms_Subset (sys_grant s sp_from v_from sp_to v_to perms)"
  using assms sys_grant_Inv_Space_Perms_Subset1 sys_grant_Inv_Space_Perms_Subset2
  by metis

lemma sys_grant_Inv_Space_Valid_Has_Real11:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
      and p4:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and> 
            (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "\<exists>r. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
proof(cases "Virtual sp v = Virtual sp_to v_to")
  case True
  then have h1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1
      (fst (the (the (space_mapping s sp_from) v_from)))"
    using grant_to_self_direct p4 by simp
  have h2:"s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>1(fst (the (the (space_mapping s sp_from) v_from)))"
    using p4 valid_page_def direct_path_def by auto
  have "\<exists>r. s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Real r)"
    using p1 p4 Inv_Space_Valid_Has_Real_def rtran_tran by simp
  then obtain r where "s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>+(Real r)" by auto
  then have "s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Real r)"
    using p4 valid_page_def refl_tran h2 basic15 by blast
  then have "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Real r)" 
    using p4 grant_from_pre_rtran p2 rtran_tran by auto
  then show ?thesis using h1 refl_tran True by blast
next
  case False
  then have "s\<turnstile>(Virtual sp v)" using sys_grant_valid p3 by blast
  then have "\<exists>r. s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"using p1 Inv_Space_Valid_Has_Real_def by simp
  then obtain r where h1:"s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)" by blast
  have h2:"s\<turnstile>(Virtual sp_from v_from)\<leadsto>\<^sup>1(fst (the (the (space_mapping s sp_from) v_from)))"
    using p4 valid_page_def direct_path_def by auto
  have "\<not>(s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_to v_to) \<or> s\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Virtual sp_from v_from))" 
    using p4 grant_path_valid p3 p2 False by metis
  then have "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
    using grant_not_path_rtran h1 by simp
  then show ?thesis by blast
qed

lemma sys_grant_Inv_Space_Valid_Has_Real12:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"\<not>((s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and> 
            (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum))"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
    shows "\<exists>r. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
proof-
  have "(sys_grant s sp_from v_from sp_to v_to perms) = s"
    unfolding sys_grant_def using p2 by auto
  then show ?thesis using p1 p3 Inv_Space_Valid_Has_Real_def by auto
qed

lemma sys_grant_Inv_Space_Valid_Has_Real1:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
    shows "\<exists>r. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
  using assms sys_grant_Inv_Space_Valid_Has_Real11 sys_grant_Inv_Space_Valid_Has_Real12
  by metis

lemma sys_grant_Inv_Space_Valid_Has_Real21:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"\<exists>r. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
      and p4:"(s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and> 
            (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum)"
    shows "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
proof(cases "Virtual sp v = Virtual sp_to v_to")
  case True
  then have h1:"(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>1
      (fst (the (the (space_mapping s sp_from) v_from)))"
    using grant_to_self_direct p4 by simp
  then show ?thesis using valid_page_def True by auto
next
  case False
  then have "\<exists>y. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v) \<leadsto>\<^sup>1 y"
    using p3 rtran_path.cases by blast
  then show ?thesis using valid_page_def by auto
qed

thm sys_grant_def
lemma sys_grant_Inv_Space_Valid_Has_Real22:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"\<not>((s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and> 
            (\<forall>v. \<not> s\<turnstile>(fst (the (the (space_mapping s sp_from) v_from)))\<leadsto>\<^sup>*(Virtual sp_to v)) \<and> 
            sp_to \<noteq> Sigma0Space \<and> perms \<noteq> {} \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum))"
      and p3:"\<exists>r. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
    shows "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
proof-
  have "(sys_grant s sp_from v_from sp_to v_to perms) = s"
    unfolding sys_grant_def using p2 by auto
  then show ?thesis using p1 p3 Inv_Space_Valid_Has_Real_def by auto
qed

lemma sys_grant_Inv_Space_Valid_Has_Real2:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Perms_Subset s"
      and p4:"\<exists>r. (sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)\<leadsto>\<^sup>*(Real r)"
    shows "(sys_grant s sp_from v_from sp_to v_to perms)\<turnstile>(Virtual sp v)"
  using assms sys_grant_Inv_Space_Valid_Has_Real21 sys_grant_Inv_Space_Valid_Has_Real22
  by metis

lemma sys_grant_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s" 
      and p2:"Inv_Space_HasNot_Loop s"
      and p3:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Valid_Has_Real (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Valid_Has_Real_def
  apply rule
  apply (case_tac x)
  subgoal
    using assms sys_grant_Inv_Space_Valid_Has_Real1 sys_grant_Inv_Space_Valid_Has_Real2
    by blast
  using valid_page_def rtran_tran by auto

lemma sys_grant_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
     sys_grant_NC_Space 
  by blast

lemma sys_grant_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
  shows "Inv_Space_Spaces_IsNot_None (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Spaces_IsNot_None_def
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
     sys_grant_NC_Space 
  by auto

lemma sys_grant_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
  shows "Inv_Space_Vpage_Range (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def]
  apply auto
  by (metis page_t.sel(2) sys_grant_def sys_grant_valid)

lemma sys_grant_Inv_Space:
  assumes "Inv_Space s"
  shows "Inv_Space (sys_grant s sp_from v_from sp_to v_to perms)"
  using Inv_Space_def assms sys_grant_Inv_Space_Spaces_In_Config
    sys_grant_Inv_Space_HasNot_Loop sys_grant_Inv_Space_Perms_IsNot_Empty
    sys_grant_Inv_Space_Perms_Subset sys_grant_Inv_Space_Valid_Has_Real
    sys_grant_Inv_Space_InitialSpaces_In_Spaces 
    sys_grant_Inv_Space_Spaces_IsNot_None sys_grant_Inv_Space_Vpage_Range
  by auto

subsubsection\<open>Thread\<close>
lemma sys_grant_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma sys_grant_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma sys_grant_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma sys_grant_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma sys_grant_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma sys_grant_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto

lemma sys_grant_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma sys_grant_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma sys_grant_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma sys_grant_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma sys_grant_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def]
    sys_grant_NC_Thread sys_grant_NC_Space
  by auto

lemma sys_grant_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Threads_Eq_Space_Threads_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def]
    sys_grant_NC_Thread sys_grant_NC_Space
  by auto

lemma sys_grant_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma sys_grant_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma sys_grant_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma sys_grant_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_IntThreads_Utcb_Is_None_def sys_grant_def 
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma sys_grant_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma sys_grant_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding sys_grant_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma sys_grant_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (sys_grant s sp_from v_from sp_to v_to perms)"
  using assms unfolding Inv_Sigma0_Space_def sys_grant_def
  by auto

lemma sys_grant_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (sys_grant s sp_from v_from sp_to v_to perms)"
  using assms unfolding Inv_RootServer_Space_def sys_grant_def
  by auto

lemma sys_grant_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (sys_grant s sp_from v_from sp_to v_to perms)"
  using assms unfolding Inv_IntThreads_Space_def sys_grant_def
  by auto

lemma sys_grant_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (sys_grant s sp_from v_from sp_to v_to perms)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] sys_grant_Inv_Idle_NotIn_Threads 
    sys_grant_Inv_Sigma0_In_Active sys_grant_Inv_Idle_Space_Is_KernelSpace
    sys_grant_Inv_RootServer_In_Active sys_grant_Inv_IntThreads_In_Active 
    sys_grant_Inv_Threads_Space_Dom
    sys_grant_Inv_Threads_In_Config sys_grant_Inv_Active_In_Threads 
    sys_grant_Inv_NThreads_Is_None sys_grant_Inv_Threads_IsNot_None 
    sys_grant_Inv_Threads_Space_In_Spaces sys_grant_Inv_Threads_Eq_Space_Threads
    sys_grant_Inv_Threads_Sche_In_Threads 
    sys_grant_Inv_NActive_Utcb_Is_None sys_grant_Inv_Active_Utcb_IsNot_None
    sys_grant_Inv_IntThreads_Utcb_Is_None sys_grant_Inv_Threads_Partner_In_Threads
    sys_grant_Inv_Threads_Incoming_In_Threads sys_grant_Inv_Sigma0_Space
    sys_grant_Inv_RootServer_Space sys_grant_Inv_IntThreads_Space
  by auto

lemma sys_grant_Invariant:
  assumes "Invariants s"
  shows "Invariants (sys_grant s sp_from v_from sp_to v_to perms)"
  using Invariants_def sys_grant_Inv_Current sys_grant_Inv_Space 
    sys_grant_Inv_Thread assms
  by auto

lemma Grant_fpage_Invariant:
  assumes "Invariants s"
  shows "Invariants (Grant_fpage s sp1 v1 sp2 v2 perms n)"
  using assms sys_grant_Invariant
  apply(induction n)
  by auto

section\<open>Unmap_fpage\<close>
subsection\<open>user\<close>
lemma Unmap_fpage_NC_User:
"thread_pager (Unmap_fpage s sp v perms n) = thread_pager s \<and>
 thread_handler (Unmap_fpage s sp v perms n) = thread_handler s \<and>
 thread_message (Unmap_fpage s sp v perms n) = thread_message s \<and>
 thread_rcvWindow (Unmap_fpage s sp v perms n) = thread_rcvWindow s \<and>
 thread_error (Unmap_fpage s sp v perms n) = thread_error s"
  apply(induct n arbitrary: s sp v perms)
  by (auto simp:sys_unmap_def)

subsection\<open>current\<close>
lemma Unmap_fpage_NC_Current:
"current_thread (Unmap_fpage s sp v perms n) = current_thread s \<and>
 current_time (Unmap_fpage s sp v perms n) = current_time s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_unmap_def)

subsection\<open>thread\<close>
lemma Unmap_fpage_NC_Thread:
"threads (Unmap_fpage s sp v perms n) = threads s \<and>
 active_threads (Unmap_fpage s sp v perms n) = active_threads s \<and>
 thread_space (Unmap_fpage s sp v perms n) = thread_space s \<and>
 thread_scheduler (Unmap_fpage s sp v perms n) = thread_scheduler s \<and>
 thread_state (Unmap_fpage s sp v perms n) = thread_state s \<and>
 thread_priority (Unmap_fpage s sp v perms n) = thread_priority s \<and>
 thread_total_quantum (Unmap_fpage s sp v perms n) = thread_total_quantum s \<and>
 thread_timeslice_length (Unmap_fpage s sp v perms n) = thread_timeslice_length s \<and>
 thread_current_timeslice (Unmap_fpage s sp v perms n) = thread_current_timeslice s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_unmap_def)

subsection\<open>space\<close>
lemma Unmap_fpage_NC_Space:
"spaces (Unmap_fpage s sp v perms n) = spaces s \<and>
 initialised_spaces (Unmap_fpage s sp v perms n) = initialised_spaces s \<and>
 space_threads (Unmap_fpage s sp v perms n) = space_threads s \<and>
 dom (space_mapping (Unmap_fpage s sp v perms n)) = dom (space_mapping s)"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_unmap_NC_Space)

lemma Unmap_fpage_NC_Space1:
"(space_mapping (Unmap_fpage s sp v perms n) sp1 \<noteq> None) = (space_mapping s sp1 \<noteq> None)"
  apply(induct n arbitrary: s sp v perms)
   apply simp
  using sys_unmap_NC_Space1
  by fastforce

lemma Unmap_fpage_NC_Space2:
"(sp1 \<in> spaces (Unmap_fpage s sp v perms n)) = (sp1 \<in> spaces s)"
  apply(induct n arbitrary: s sp v perms)
  apply simp
  using sys_unmap_NC_Space2
  by fastforce

subsubsection\<open>space_mapping\<close>
lemma Unmap_fpage_path_space1:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>+(Virtual sp v) 
\<Longrightarrow> get_perms s sp1 v1 \<subseteq> perms \<Longrightarrow>
the (space_mapping (Unmap_fpage s sp v perms 1) sp1) v1 = None"
  apply simp
  using unmap_path_space by simp

subsection\<open>IPC\<close>
lemma Unmap_fpage_NC_IPC:
"thread_ipc_partner (Unmap_fpage s sp v perms n) = thread_ipc_partner s \<and>
 thread_ipc_timeout (Unmap_fpage s sp v perms n) = thread_ipc_timeout s \<and>
 thread_incoming (Unmap_fpage s sp v perms n) =  thread_incoming s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_unmap_def)

subsection\<open>scheduling\<close>
lemma Unmap_fpage_NC_Scheduling:
"wait_queuing (Unmap_fpage s sp v perms n) = wait_queuing s \<and>
 ready_queuing (Unmap_fpage s sp v perms n) = ready_queuing s \<and>
 current_timeslice (Unmap_fpage s sp v perms n) = current_timeslice s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_unmap_def)

subsection\<open>memory\<close>
lemma Unmap_fpage_direct_eq:"(Unmap_fpage s sp v perms n)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  apply(induct n arbitrary: s sp v perms)
   apply auto
  using sys_unmap_pre
  by blast

lemma Unmap_fpage_tran:"(Unmap_fpage s sp v perms n)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(induction rule:tran_path.induct)
  using Unmap_fpage_direct_eq tran_path.intros
  by blast+

lemma Unmap_fpage_rtran:"(Unmap_fpage s sp v perms n)\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>*y"
  using Unmap_fpage_tran rtran_tran
  by auto

lemma Unmap_fpage_valid_vpage:
"(Unmap_fpage s sp v perms n) \<turnstile> (Virtual sp1 v_page) \<Longrightarrow> s \<turnstile> (Virtual sp1 v_page)"
  using Unmap_fpage_direct_eq valid_page_def
  by (meson ValidVpageHasSon)

lemma Unmap_fpage_valid_rpage:"(Unmap_fpage s sp v perms n)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma Unmap_fpage_valid:"(Unmap_fpage s sp v perms n)\<turnstile> x \<Longrightarrow> s\<turnstile>x"
  apply (case_tac x)
  using Unmap_fpage_valid_vpage apply simp
  using Unmap_fpage_valid_rpage by simp

subsection\<open>Inv\<close>
subsubsection\<open>space\<close>
lemma Unmap_fpage_Inv_Space_HasNot_Loop:
  assumes "Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (Unmap_fpage s sp v perms n)"
  using assms sys_unmap_Inv_Space_HasNot_Loop
  apply(induction n)
  by auto

lemma Unmap_fpage_Inv_Space_Perms_IsNot_Empty:
  assumes "Inv_Space_Perms_IsNot_Empty s"
  shows "Inv_Space_Perms_IsNot_Empty (Unmap_fpage s sp v perms n)"
  using assms sys_unmap_Inv_Space_Perms_IsNot_Empty
  apply(induction n)
  by auto

definition "Inv_Space_Three s \<equiv> Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s"
lemma sys_unmap_Inv_Space_Three:"Inv_Space_Three s \<Longrightarrow> Inv_Space_Three (sys_unmap s sp v perms)"
  unfolding Inv_Space_Three_def
  using sys_unmap_Inv_Space_Valid_Has_Real sys_unmap_Inv_Space_HasNot_Loop sys_unmap_Inv_Space_Perms_Subset
  by auto

lemma Unmap_fpage_Inv_Space_Three:"Inv_Space_Three s \<Longrightarrow> Inv_Space_Three (Unmap_fpage s sp v perms n)"
  apply(induction n)
  using sys_unmap_Inv_Space_Three
  by auto

lemma Unmap_fpage_Inv_Space_Perms_Subset:
  assumes "Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s"
  shows "Inv_Space_Perms_Subset (Unmap_fpage s sp v perms n)"
  using assms Unmap_fpage_Inv_Space_Three Inv_Space_Three_def
  by simp

lemma Unmap_fpage_Inv_Space_Valid_Has_Real:
  assumes "Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s"
  shows "Inv_Space_Valid_Has_Real (Unmap_fpage s sp v perms n)"
  using assms Unmap_fpage_Inv_Space_Three Inv_Space_Three_def
  by simp

lemma Unmap_fpage_Inv_Space:
  assumes p1:"Inv_Space s"
  shows "Inv_Space (Unmap_fpage s sp v perms n)"
  using assms sys_unmap_Inv_Space
  apply(induction n)
  by auto

lemma Unmap_fpage_Invariant:
  assumes "Invariants s"
  shows "Invariants (Unmap_fpage s sp v perms n)"
  using assms sys_unmap_Invariant
  apply(induction n)
  by auto

section\<open>Flush_fpage\<close>
subsection\<open>user\<close>
lemma Flush_fpage_NC_User:
"thread_pager (Flush_fpage s sp v perms n) = thread_pager s \<and>
 thread_handler (Flush_fpage s sp v perms n) = thread_handler s \<and>
 thread_message (Flush_fpage s sp v perms n) = thread_message s \<and>
 thread_rcvWindow (Flush_fpage s sp v perms n) = thread_rcvWindow s \<and>
 thread_error (Flush_fpage s sp v perms n) = thread_error s"
  apply(induct n arbitrary: s sp v perms)
  by (auto simp:sys_flush_NC_User)

subsection\<open>current\<close>
lemma Flush_fpage_NC_Current:
"current_thread (Flush_fpage s sp v perms n) = current_thread s \<and>
 current_time (Flush_fpage s sp v perms n) = current_time s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_flush_NC_Current)

subsection\<open>thread\<close>
lemma Flush_fpage_NC_Thread:
"threads (Flush_fpage s sp v perms n) = threads s \<and>
 active_threads (Flush_fpage s sp v perms n) = active_threads s \<and>
 thread_space (Flush_fpage s sp v perms n) = thread_space s \<and>
 thread_scheduler (Flush_fpage s sp v perms n) = thread_scheduler s \<and>
 thread_state (Flush_fpage s sp v perms n) = thread_state s \<and>
 thread_priority (Flush_fpage s sp v perms n) = thread_priority s \<and>
 thread_total_quantum (Flush_fpage s sp v perms n) = thread_total_quantum s \<and>
 thread_timeslice_length (Flush_fpage s sp v perms n) = thread_timeslice_length s \<and>
 thread_current_timeslice (Flush_fpage s sp v perms n) = thread_current_timeslice s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_flush_NC_Thread)

subsection\<open>Space\<close>
lemma Flush_fpage_NC_Space:
"spaces (Flush_fpage s sp v perms n) = spaces s \<and>
 initialised_spaces (Flush_fpage s sp v perms n) = initialised_spaces s \<and>
 space_threads (Flush_fpage s sp v perms n) = space_threads s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_flush_NC_Space)

subsection\<open>IPC\<close>
lemma Flush_fpage_NC_IPC:
"thread_ipc_partner (Flush_fpage s sp v perms n) = thread_ipc_partner s \<and>
 thread_ipc_timeout (Flush_fpage s sp v perms n) = thread_ipc_timeout s \<and>
 thread_incoming (Flush_fpage s sp v perms n) =  thread_incoming s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_flush_NC_IPC)

subsection\<open>scheduling\<close>
lemma Flush_fpage_NC_Scheduling:
"wait_queuing (Flush_fpage s sp v perms n) = wait_queuing s \<and>
 ready_queuing (Flush_fpage s sp v perms n) = ready_queuing s \<and>
 current_timeslice (Flush_fpage s sp v perms n) = current_timeslice s"
  apply(induct n arbitrary: s sp v perms)
  by(auto simp:sys_flush_NC_Scheduling)

section\<open>Map_fpage\<close>
subsection\<open>user\<close>
lemma Map_fpage_NC_User:
"thread_pager (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_pager s \<and>
 thread_handler (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_handler s \<and>
 thread_message (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_message s \<and>
 thread_rcvWindow (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_rcvWindow s \<and>
 thread_error (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_error s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_map_NC_User)

subsection\<open>current\<close>
lemma Map_fpage_NC_Current:
"current_thread (Map_fpage s sp1 v1 sp2 v2 perms n) = current_thread s \<and>
 current_time (Map_fpage s sp1 v1 sp2 v2 perms n) = current_time s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_map_NC_Current)

subsection\<open>thread\<close>
lemma Map_fpage_NC_Thread:
"threads (Map_fpage s sp1 v1 sp2 v2 perms n) = threads s \<and>
 active_threads (Map_fpage s sp1 v1 sp2 v2 perms n) = active_threads s \<and>
 thread_space (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_space s \<and>
 thread_scheduler (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_scheduler s \<and>
 thread_state (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_state s \<and>
 thread_priority (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_priority s \<and>
 thread_total_quantum (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_total_quantum s \<and>
 thread_timeslice_length (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_timeslice_length s \<and>
 thread_current_timeslice (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_current_timeslice s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_map_NC_Thread)

subsection\<open>Space\<close>
lemma Map_fpage_NC_Space:
"spaces (Map_fpage s sp1 v1 sp2 v2 perms n) = spaces s \<and>
 initialised_spaces (Map_fpage s sp1 v1 sp2 v2 perms n) = initialised_spaces s \<and>
 space_threads (Map_fpage s sp1 v1 sp2 v2 perms n) = space_threads s"
  apply(induct n arbitrary:  s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_map_NC_Space)

subsection\<open>IPC\<close>
lemma Map_fpage_NC_IPC:
"thread_ipc_partner (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_ipc_partner s \<and>
 thread_ipc_timeout (Map_fpage s sp1 v1 sp2 v2 perms n) = thread_ipc_timeout s \<and>
 thread_incoming (Map_fpage s sp1 v1 sp2 v2 perms n) =  thread_incoming s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_map_NC_IPC)

subsection\<open>scheduling\<close>
lemma Map_fpage_NC_Scheduling:
"wait_queuing (Map_fpage s sp1 v1 sp2 v2 perms n) = wait_queuing s \<and>
 ready_queuing (Map_fpage s sp1 v1 sp2 v2 perms n) = ready_queuing s \<and>
 current_timeslice (Map_fpage s sp1 v1 sp2 v2 perms n) = current_timeslice s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_map_NC_Scheduling)

section\<open>Grant_fpage\<close>
subsection\<open>user\<close>
lemma Grant_fpage_NC_User:
"thread_pager (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_pager s \<and>
 thread_handler (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_handler s \<and>
 thread_message (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_message s \<and>
 thread_rcvWindow (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_rcvWindow s \<and>
 thread_error (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_error s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_grant_NC_User)

subsection\<open>current\<close>
lemma Grant_fpage_NC_Current:
"current_thread (Grant_fpage s sp1 v1 sp2 v2 perms n) = current_thread s \<and>
 current_time (Grant_fpage s sp1 v1 sp2 v2 perms n) = current_time s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_grant_NC_Current)

subsection\<open>thread\<close>
lemma Grant_fpage_NC_Thread:
"threads (Grant_fpage s sp1 v1 sp2 v2 perms n) = threads s \<and>
 active_threads (Grant_fpage s sp1 v1 sp2 v2 perms n) = active_threads s \<and>
 thread_space (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_space s \<and>
 thread_scheduler (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_scheduler s \<and>
 thread_state (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_state s \<and>
 thread_priority (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_priority s \<and>
 thread_total_quantum (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_total_quantum s \<and>
 thread_timeslice_length (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_timeslice_length s \<and>
 thread_current_timeslice (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_current_timeslice s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_grant_NC_Thread)

subsection\<open>Space\<close>
lemma Grant_fpage_NC_Space:
"spaces (Grant_fpage s sp1 v1 sp2 v2 perms n) = spaces s \<and>
 initialised_spaces (Grant_fpage s sp1 v1 sp2 v2 perms n) = initialised_spaces s \<and>
 space_threads (Grant_fpage s sp1 v1 sp2 v2 perms n) = space_threads s"
  apply(induct n arbitrary:  s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_grant_NC_Space)

subsection\<open>IPC\<close>
lemma Grant_fpage_NC_IPC:
"thread_ipc_partner (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_ipc_partner s \<and>
 thread_ipc_timeout (Grant_fpage s sp1 v1 sp2 v2 perms n) = thread_ipc_timeout s \<and>
 thread_incoming (Grant_fpage s sp1 v1 sp2 v2 perms n) =  thread_incoming s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_grant_NC_IPC)

subsection\<open>scheduling\<close>
lemma Grant_fpage_NC_Scheduling:
"wait_queuing (Grant_fpage s sp1 v1 sp2 v2 perms n) = wait_queuing s \<and>
 ready_queuing (Grant_fpage s sp1 v1 sp2 v2 perms n) = ready_queuing s \<and>
 current_timeslice (Grant_fpage s sp1 v1 sp2 v2 perms n) = current_timeslice s"
  apply(induct n arbitrary: s sp1 v1 sp2 v2 perms)
  by(auto simp:sys_grant_NC_Scheduling)

section\<open>CreateAddressSpace\<close>
subsection\<open>user\<close>
lemma CreateAddressSpace_NC_User:
"thread_pager (CreateAddressSpace SysConf s sp) = thread_pager s \<and>
 thread_handler (CreateAddressSpace SysConf s sp) = thread_handler s \<and>
 thread_message (CreateAddressSpace SysConf s sp) = thread_message s \<and>
 thread_rcvWindow (CreateAddressSpace SysConf s sp) = thread_rcvWindow s \<and>
 thread_error (CreateAddressSpace SysConf s sp) = thread_error s"
  by(auto simp add:CreateAddressSpace_def)

subsection\<open>current\<close>
lemma CreateAddressSpace_NC_Current:
"current_thread (CreateAddressSpace SysConf s sp) = current_thread s \<and>
 current_time (CreateAddressSpace SysConf s sp) = current_time s"
  by(auto simp add:CreateAddressSpace_def)

subsection\<open>thread\<close>
lemma CreateAddressSpace_NC_Thread:
"threads (CreateAddressSpace SysConf s sp) = threads s \<and>
 active_threads (CreateAddressSpace SysConf s sp) = active_threads s \<and>
 thread_space (CreateAddressSpace SysConf s sp) = thread_space s \<and>
 thread_scheduler (CreateAddressSpace SysConf s sp) = thread_scheduler s \<and>
 thread_state (CreateAddressSpace SysConf s sp) = thread_state s \<and>
 thread_priority (CreateAddressSpace SysConf s sp) = thread_priority s \<and>
 thread_total_quantum (CreateAddressSpace SysConf s sp) = thread_total_quantum s \<and>
 thread_timeslice_length (CreateAddressSpace SysConf s sp) = thread_timeslice_length s \<and>
 thread_current_timeslice (CreateAddressSpace SysConf s sp) = thread_current_timeslice s"
  by(auto simp add:CreateAddressSpace_def)

subsection\<open>space\<close>
lemma CreateAddressSpace_C_Space:
"sp \<in> (Address_Space SysConf) \<and> sp \<notin> spaces s \<longrightarrow>
   (spaces (CreateAddressSpace SysConf s sp) = spaces s \<union> {sp}) \<and>
   (initialised_spaces (CreateAddressSpace SysConf s sp) = initialised_spaces s) \<and>
   (space_threads (CreateAddressSpace SysConf s sp) sp = Some {}) \<and>
   (space_mapping (CreateAddressSpace SysConf s sp) sp = Some (\<lambda>vp. None))"
  by(auto simp add:CreateAddressSpace_def spaces_def)

lemma CreateAddressSpace_NC_Space:
"\<not>(sp \<in> (Address_Space SysConf) \<and> sp \<notin> spaces s) \<longrightarrow>
 (spaces (CreateAddressSpace SysConf s sp) = spaces s) \<and>
 (initialised_spaces (CreateAddressSpace SysConf s sp) = initialised_spaces s) \<and>
 (space_threads (CreateAddressSpace SysConf s sp) = space_threads s ) \<and>
 (space_mapping (CreateAddressSpace SysConf s sp) = space_mapping s )"
  by(auto simp add:CreateAddressSpace_def)

lemma CreateAddressSpace_NC_Space_Other:
"sp1 \<noteq> sp \<longrightarrow>
 (space_threads (CreateAddressSpace SysConf s sp) sp1 = space_threads s sp1) \<and>
 (space_mapping (CreateAddressSpace SysConf s sp) sp1 = space_mapping s sp1)"
  by(auto simp add:CreateAddressSpace_def)

subsection\<open>IPC\<close>
lemma CreateAddressSpace_NC_IPC:
"thread_ipc_partner (CreateAddressSpace SysConf s sp) = thread_ipc_partner s \<and>
 thread_ipc_timeout (CreateAddressSpace SysConf s sp) = thread_ipc_timeout s \<and>
 thread_incoming (CreateAddressSpace SysConf s sp) =  thread_incoming s"
  by(auto simp add:CreateAddressSpace_def)

subsection\<open>scheduling\<close>
lemma CreateAddressSpace_NC_Scheduling:
"wait_queuing (CreateAddressSpace SysConf s sp) = wait_queuing s \<and>
 ready_queuing (CreateAddressSpace SysConf s sp) = ready_queuing s \<and>
 current_timeslice (CreateAddressSpace SysConf s sp) = current_timeslice s"
  by(auto simp add:CreateAddressSpace_def)

subsection\<open>memory\<close>
lemma CreateAddressSpace_space:"space_mapping s sp1 \<noteq> None \<Longrightarrow> 
space_mapping (CreateAddressSpace SysConf s sp) sp1 = space_mapping s sp1"
  unfolding CreateAddressSpace_def spaces_def
  by auto

lemma CreateAddressSpace_direct_eq:"(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
proof-
  show "(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  proof(rule iffI)
    show "(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
      unfolding CreateAddressSpace_def direct_path_def
      apply(case_tac "sp \<in> Address_Space SysConf \<and> sp \<notin> spaces s")
       apply auto
      apply(case_tac "spa = sp")
      by auto
  next
    show "s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> (CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>1y"
      unfolding CreateAddressSpace_def direct_path_def
      apply(case_tac "sp \<in> Address_Space SysConf \<and> sp \<notin> spaces s")
       apply auto
      using Inv_Space_Valid_In_Spaces_lemma ValidVpageMappingNotNone by fastforce
  qed
qed

lemma CreateAddressSpace_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>+y"
proof-
  show " s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>+y"
  proof(induct rule:tran_path.induct)
    case (one_path x y)
    thm one_path.hyps
    then have "(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>1y"
      using CreateAddressSpace_direct_eq by simp
    then show ?case
      by(rule tran_path.intros)
  next
    case (tran_path x y z)
    then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
      have h3: "(CreateAddressSpace SysConf s sp)\<turnstile>y\<leadsto>\<^sup>+z"
      by (simp add: tran_path.hyps(3))
    then have h21:"(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>1y"
      using CreateAddressSpace_direct_eq h2 by simp
    then show ?case
      using h3 tran_path.intros(2) by blast
  qed
qed

lemma CreateAddressSpace_tran:"(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
proof-
  show "(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
    apply(rule iffI)
     apply(induct rule: tran_path.induct)
    using CreateAddressSpace_direct_eq tran_path.intros CreateAddressSpace_tran1
    by auto
qed

lemma CreateAddressSpace_rtran:"(CreateAddressSpace SysConf s sp)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using CreateAddressSpace_tran rtran_tran
  by auto

lemma CreateAddressSpace_valid_vpage:"
(CreateAddressSpace SysConf s sp) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using CreateAddressSpace_direct_eq valid_page_def
  by auto

lemma CreateAddressSpace_valid_rpage:"
   (CreateAddressSpace SysConf s sp)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma CreateAddressSpace_valid:"(CreateAddressSpace SysConf s sp)\<turnstile> x = s\<turnstile>x"
  using CreateAddressSpace_valid_vpage CreateAddressSpace_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma CreateAddressSpace_NC_Memory_Cond:
"\<not>(sp \<in> (Address_Space SysConf) \<and> sp \<notin> spaces s) \<Longrightarrow> 
 pt_walk (CreateAddressSpace SysConf s sp) = pt_walk s"
  using CreateAddressSpace_def
  by auto

section\<open>InitialiseAddressSpace\<close>
subsection\<open>user\<close>
lemma InitialiseAddressSpace_NC_User:
"thread_pager (InitialiseAddressSpace s sp) = thread_pager s \<and>
 thread_handler (InitialiseAddressSpace s sp) = thread_handler s \<and>
 thread_message (InitialiseAddressSpace s sp) = thread_message s \<and>
 thread_rcvWindow (InitialiseAddressSpace s sp) = thread_rcvWindow s \<and>
 thread_error (InitialiseAddressSpace s sp) = thread_error s"
  by(auto simp add:InitialiseAddressSpace_def)

subsection\<open>current\<close>
lemma InitialiseAddressSpace_NC_Current:
"current_thread (InitialiseAddressSpace s sp) = current_thread s \<and>
 current_time (InitialiseAddressSpace s sp) = current_time s"
  by(auto simp add:InitialiseAddressSpace_def)

subsection\<open>thread\<close>
lemma InitialiseAddressSpace_NC_Thread:
"threads (InitialiseAddressSpace s sp) = threads s \<and>
 active_threads (InitialiseAddressSpace s sp) = active_threads s \<and>
 thread_space (InitialiseAddressSpace s sp) = thread_space s \<and>
 thread_scheduler (InitialiseAddressSpace s sp) = thread_scheduler s \<and>
 thread_state (InitialiseAddressSpace s sp) = thread_state s \<and>
 thread_priority (InitialiseAddressSpace s sp) = thread_priority s \<and>
 thread_total_quantum (InitialiseAddressSpace s sp) = thread_total_quantum s \<and>
 thread_timeslice_length (InitialiseAddressSpace s sp) = thread_timeslice_length s \<and>
 thread_current_timeslice (InitialiseAddressSpace s sp) = thread_current_timeslice s"
  by(auto simp add:InitialiseAddressSpace_def)

subsection\<open>space\<close>
lemma InitialiseAddressSpace_C_Space:
"sp \<in> spaces s \<longrightarrow>
  (spaces (InitialiseAddressSpace s sp) = spaces s) \<and>
  (initialised_spaces (InitialiseAddressSpace s sp) = initialised_spaces s \<union> {sp}) \<and>
  (space_threads (InitialiseAddressSpace s sp) = space_threads s) \<and>
  (space_mapping (InitialiseAddressSpace s sp) = space_mapping s)"
  by(auto simp add:InitialiseAddressSpace_def spaces_def)

lemma InitialiseAddressSpace_C_Space_Cond:
"sp \<notin> spaces s \<longrightarrow>
  initialised_spaces (InitialiseAddressSpace s sp) = initialised_spaces s"
  by(auto simp add:InitialiseAddressSpace_def spaces_def)

lemma InitialiseAddressSpace_NC_Space:
" spaces (InitialiseAddressSpace s sp) = spaces s \<and>
 space_threads (InitialiseAddressSpace s sp) = space_threads s \<and>
 space_mapping (InitialiseAddressSpace s sp) = space_mapping s"
  by(auto simp add:InitialiseAddressSpace_def spaces_def)

subsection\<open>IPC\<close>
lemma InitialiseAddressSpace_NC_IPC:
"thread_ipc_partner (InitialiseAddressSpace s sp) = thread_ipc_partner s \<and>
 thread_ipc_timeout (InitialiseAddressSpace s sp) = thread_ipc_timeout s \<and>
 thread_incoming (InitialiseAddressSpace s sp) =  thread_incoming s"
  by(auto simp add:InitialiseAddressSpace_def)

subsection\<open>scheduling\<close>
lemma InitialiseAddressSpace_NC_Scheduling:
"wait_queuing (InitialiseAddressSpace s sp) = wait_queuing s \<and>
 ready_queuing (InitialiseAddressSpace s sp) = ready_queuing s \<and>
 current_timeslice (InitialiseAddressSpace s sp) = current_timeslice s"
  by(auto simp add:InitialiseAddressSpace_def)

subsection\<open>memory\<close>
lemma InitialiseAddressSpace_direct_eq:"(InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
proof(rule iffI)
  show "(InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
    unfolding InitialiseAddressSpace_def direct_path_def
    apply(case_tac "sp \<in> spaces s")
    by auto
next
  show "s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> (InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>1y"
    using direct_path_def InitialiseAddressSpace_def by fastforce
qed

lemma InitialiseAddressSpace_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>1y"
    using InitialiseAddressSpace_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(InitialiseAddressSpace s sp)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>1y"
    using InitialiseAddressSpace_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed

lemma InitialiseAddressSpace_tran:"(InitialiseAddressSpace s sp)\<turnstile> x \<leadsto>\<^sup>+ y = s\<turnstile> x \<leadsto>\<^sup>+ y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using InitialiseAddressSpace_direct_eq tran_path.intros InitialiseAddressSpace_tran1
  by auto

lemma InitialiseAddressSpace_rtran:"(InitialiseAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using InitialiseAddressSpace_tran rtran_tran
  by auto

lemma InitialiseAddressSpace_valid_vpage:"(InitialiseAddressSpace s sp)\<turnstile>(Virtual sp1 v_page) =
s\<turnstile>(Virtual sp1 v_page)"
  unfolding valid_page_def
  using InitialiseAddressSpace_direct_eq
  by auto

lemma InitialiseAddressSpace_valid_rpage:"(InitialiseAddressSpace s sp)\<turnstile>(Real r) = s \<turnstile>(Real r)"
  unfolding valid_page_def
  by auto

lemma InitialiseAddressSpace_valid:"(InitialiseAddressSpace s sp) \<turnstile> x = s \<turnstile> x"
  using InitialiseAddressSpace_valid_vpage InitialiseAddressSpace_valid_rpage
    FatherIsVirtual ValidExSon
  by fastforce

section\<open>DeleteAddressSpace\<close>
subsection\<open>user\<close>
lemma DeleteAddressSpace_NC_User:
"thread_pager (DeleteAddressSpace s sp) = thread_pager s \<and>
 thread_handler (DeleteAddressSpace s sp) = thread_handler s \<and>
 thread_message (DeleteAddressSpace s sp) = thread_message s \<and>
 thread_rcvWindow (DeleteAddressSpace s sp) = thread_rcvWindow s \<and>
 thread_error (DeleteAddressSpace s sp) = thread_error s"
  by(auto simp add:DeleteAddressSpace_def Let_def Unmap_fpage_NC_User)
  
subsection\<open>current\<close>
lemma DeleteAddressSpace_NC_Current:
"current_thread (DeleteAddressSpace s sp) = current_thread s \<and>
 current_time (DeleteAddressSpace s sp) = current_time s"
  by(auto simp add:DeleteAddressSpace_def Let_def Unmap_fpage_NC_Current)

subsection\<open>thread\<close>
lemma DeleteAddressSpace_NC_Thread:
"threads (DeleteAddressSpace s sp) = threads s \<and>
 active_threads (DeleteAddressSpace s sp) = active_threads s \<and>
 thread_space (DeleteAddressSpace s sp) = thread_space s \<and>
 thread_scheduler (DeleteAddressSpace s sp) = thread_scheduler s \<and>
 thread_state (DeleteAddressSpace s sp) = thread_state s \<and>
 thread_priority (DeleteAddressSpace s sp) = thread_priority s \<and>
 thread_total_quantum (DeleteAddressSpace s sp) = thread_total_quantum s \<and>
 thread_timeslice_length (DeleteAddressSpace s sp) = thread_timeslice_length s \<and>
 thread_current_timeslice (DeleteAddressSpace s sp) = thread_current_timeslice s"
  by(auto simp add:DeleteAddressSpace_def Let_def Unmap_fpage_NC_Thread)

subsection\<open>space\<close>
lemma DeleteAddressSpace_C_Space:
"sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp \<Longrightarrow>
  (spaces (DeleteAddressSpace s sp) = spaces s - {sp}) \<and>
  (initialised_spaces (DeleteAddressSpace s sp) = initialised_spaces s - {sp}) \<and>
  (space_threads (DeleteAddressSpace s sp) sp = None) \<and>
  (space_mapping (DeleteAddressSpace s sp) sp = None)"
  unfolding DeleteAddressSpace_def Let_def 
  using Unmap_fpage_NC_Space
  by (auto simp:spaces_def)

lemma DeleteAddressSpace_NC_Space:
"\<not>(sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp) \<longrightarrow>
 (spaces (DeleteAddressSpace s sp) = spaces s) \<and>
 (initialised_spaces (DeleteAddressSpace s sp) = initialised_spaces s) \<and>
 (space_threads (DeleteAddressSpace s sp) = space_threads s) \<and>
 (space_mapping (DeleteAddressSpace s sp) = space_mapping s)"
  by(auto simp add:DeleteAddressSpace_def)  

lemma DeleteAddressSpace_NC_Space_Other:
"sp \<noteq> sp1 \<Longrightarrow> 
  (space_threads (DeleteAddressSpace s sp) sp1 = space_threads s sp1)"
  by(auto simp add:DeleteAddressSpace_def Let_def Unmap_fpage_NC_Space)

lemma DeleteAddressSpace_NC_Space_Other1:
"sp \<noteq> sp1 \<Longrightarrow>
  ((space_mapping (DeleteAddressSpace s sp) sp1 \<noteq> None) = (space_mapping s sp1 \<noteq> None))"
  unfolding DeleteAddressSpace_def Let_def
  using Unmap_fpage_NC_Space1
  by auto

lemma DeleteAddressSpace_NC_Space_Other2:
"sp \<noteq> sp1 \<Longrightarrow>
  (sp1 \<in> spaces (DeleteAddressSpace s sp)) = (sp1 \<in> spaces s)"
  unfolding DeleteAddressSpace_def Let_def
  apply (auto simp:spaces_def)
  using Unmap_fpage_NC_Space1 by blast+

subsection\<open>IPC\<close>
lemma DeleteAddressSpace_NC_IPC:
"thread_ipc_partner (DeleteAddressSpace s sp) = thread_ipc_partner s \<and>
 thread_ipc_timeout (DeleteAddressSpace s sp) = thread_ipc_timeout s \<and>
 thread_incoming (DeleteAddressSpace s sp) = thread_incoming s"
  by(auto simp add:DeleteAddressSpace_def Let_def Unmap_fpage_NC_IPC)

subsection\<open>scheduling\<close>
lemma DeleteAddressSpace_NC_Scheduling:
"wait_queuing (DeleteAddressSpace s sp) = wait_queuing s \<and>
 ready_queuing (DeleteAddressSpace s sp) = ready_queuing s \<and>
 current_timeslice (DeleteAddressSpace s sp) = current_timeslice s"
  by(auto simp add:DeleteAddressSpace_def Let_def Unmap_fpage_NC_Scheduling)

subsection\<open>memory\<close>
definition "DeleteAddressSpace_auxi s sp = 
   s\<lparr> initialised_spaces:= initialised_spaces s - {sp},
      space_threads:= (space_threads s)(sp:= None),
      space_mapping:= (space_mapping s)(sp:= None)\<rparr>"

definition "DeleteAddressSpace1 s sp = 
(if sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp 
  then DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp
  else s
)"

lemma DeleteAddressSpace_eq:"DeleteAddressSpace s sp = DeleteAddressSpace1 s sp"
  unfolding DeleteAddressSpace1_def DeleteAddressSpace_def DeleteAddressSpace_auxi_def
    Let_def
  by simp

lemma DeleteAddressSpace_auxi_direct_eq:"(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding DeleteAddressSpace_auxi_def direct_path_def
  apply auto
  apply(case_tac "spa = sp")
  by auto

lemma DeleteAddressSpace_auxi_pre:"sp_name x \<noteq> sp \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> 
(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding DeleteAddressSpace_auxi_def direct_path_def 
  by auto

lemma DeleteAddressSpace_auxi_pre3:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> \<forall>z. s\<turnstile>x\<leadsto>\<^sup>*z \<and> s\<turnstile>z\<leadsto>\<^sup>+y \<longrightarrow> sp_name z \<noteq> sp \<Longrightarrow> 
(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then have "sp_name x \<noteq> sp"
    by (simp add: refl_path tran_path.one_path)
  then show ?case using one_path DeleteAddressSpace_auxi_pre tran_path.intros by auto
next
  case (tran_path x y z)
  then have h1:"sp_name x \<noteq> sp"
    using rtran_tran tran_path.tran_path by auto
  then have h2:"(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>1y"
    using tran_path DeleteAddressSpace_auxi_pre by simp
  from tran_path have "\<forall>za. s\<turnstile>y\<leadsto>\<^sup>*za \<and> s\<turnstile>za\<leadsto>\<^sup>+z \<longrightarrow> sp_name za \<noteq> sp"
    using refl_tran by auto
  then have "(DeleteAddressSpace_auxi s sp)\<turnstile>y\<leadsto>\<^sup>+z" using tran_path by simp
  then show ?case using h2 tran_path.intros by simp
qed


lemma DeleteAddressSpace_auxi_pre1:"(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> sp_name x \<noteq> sp"
  unfolding DeleteAddressSpace_auxi_def direct_path_def
  by auto

lemma DeleteAddressSpace_auxi_pre2:"(DeleteAddressSpace_auxi s sp)\<turnstile>(Virtual sp1 v1) \<Longrightarrow> sp1 \<noteq> sp"
  unfolding valid_page_def DeleteAddressSpace_auxi_def direct_path_def
  by auto

lemma DeleteAddressSpace_auxi_tran:"(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(induction rule:tran_path.induct)
  using DeleteAddressSpace_auxi_direct_eq tran_path.intros
  by blast+

lemma DeleteAddressSpace_auxi_rtran:"(DeleteAddressSpace_auxi s sp)\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>*y"
  using DeleteAddressSpace_auxi_tran rtran_tran
  by auto

lemma DeleteAddressSpace_auxi_valid_vpage:
"(DeleteAddressSpace_auxi s sp) \<turnstile> (Virtual sp1 v_page) \<Longrightarrow> s \<turnstile> (Virtual sp1 v_page)"
  using DeleteAddressSpace_auxi_direct_eq valid_page_def
  by (meson ValidVpageHasSon)

lemma DeleteAddressSpace_auxi_valid_rpage:"(DeleteAddressSpace_auxi s sp)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma DeleteAddressSpace_auxi_valid:"(DeleteAddressSpace_auxi s sp)\<turnstile> x \<Longrightarrow> s\<turnstile>x"
  apply (case_tac x)
  using DeleteAddressSpace_auxi_valid_vpage apply simp
  using DeleteAddressSpace_auxi_valid_rpage by simp

lemma DeleteAddressSpace_auxi_perms:"sp1 \<noteq> sp \<Longrightarrow>
get_perms ((DeleteAddressSpace_auxi s sp)) sp1 v1 = get_perms s sp1 v1"
  unfolding DeleteAddressSpace_auxi_def get_perms_def
  by auto

(*DeleteAddressSpace1*)
lemma DeleteAddressSpace1_direct_eq:"(DeleteAddressSpace1 s sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding DeleteAddressSpace1_def
  apply(case_tac "sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp")
  subgoal
    apply auto
    apply(subgoal_tac "(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x\<leadsto>\<^sup>1y")
    subgoal using Unmap_fpage_direct_eq by simp
    using DeleteAddressSpace_auxi_direct_eq
    by simp
  by simp

lemma DeleteAddressSpace_direct_eq:"(DeleteAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  using DeleteAddressSpace_eq DeleteAddressSpace1_direct_eq
  by simp

lemma DeleteAddressSpace_tran:"(DeleteAddressSpace s sp)\<turnstile> x \<leadsto>\<^sup>+ y \<Longrightarrow> s\<turnstile> x \<leadsto>\<^sup>+ y"
  apply(induct rule: tran_path.induct)
  using DeleteAddressSpace_direct_eq tran_path.intros
  by blast+

lemma DeleteAddressSpace_rtran:"(DeleteAddressSpace s sp)\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>*y"
  using DeleteAddressSpace_tran rtran_tran
  by auto

lemma DeleteAddressSpace_valid_vpage:"(DeleteAddressSpace s sp)\<turnstile>(Virtual sp1 v_page) \<Longrightarrow>
s\<turnstile>(Virtual sp1 v_page)"
  unfolding valid_page_def
  using DeleteAddressSpace_direct_eq
  by fastforce

lemma DeleteAddressSpace_valid_rpage:"(DeleteAddressSpace s sp)\<turnstile>(Real r) = s \<turnstile>(Real r)"
  unfolding valid_page_def
  by auto

lemma DeleteAddressSpace_valid:"(DeleteAddressSpace s sp) \<turnstile> x \<Longrightarrow> s \<turnstile> x"
  using DeleteAddressSpace_valid_vpage DeleteAddressSpace_valid_rpage
    FatherIsVirtual ValidExSon
    by fastforce

(*11*)
end