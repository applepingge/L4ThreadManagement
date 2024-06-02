theory L4_State_Lemmas
imports L4_Basic_Lemmas
begin

section\<open>SetError\<close>
subsection\<open>memory\<close>
lemma SetError_direct_eq:"(SetError s gno error)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by (auto simp add:direct_path_def SetError_def SetThreadError_def)

lemma SetError_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetError s gno error)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetError s gno error)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetError_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(SetError s gno error)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetError s gno error)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetError_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed

lemma SetError_tran2:"(SetError s gno error)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  then show ?case
    using SetError_direct_eq tran_path.intros by auto
next
  case (tran_path x y z)
  then show ?case using SetError_direct_eq tran_path.intros by auto
qed

lemma SetError_tran:"(SetError s gno error)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  using SetError_tran1 SetError_tran2
  by blast

lemma SetError_rtran:"(SetError s gno error)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetError_tran rtran_tran
  by auto

(*
lemma SetError_lookup:"(SetError s gno error)\<turnstile>(Virtual sp v_page)\<leadsto>\<^sup>+(Real r_page) =
s\<turnstile>(Virtual sp v_page)\<leadsto>\<^sup>+(Real r_page)"
  by(auto simp:SetError_tran)
*)

lemma SetError_valid_vpage:"(SetError s gno error)\<turnstile>(Virtual sp1 v_page) =
s\<turnstile>(Virtual sp1 v_page)"
  using SetError_direct_eq valid_page_def
  by auto

lemma SetError_valid_rpage:"(SetError s gno error)\<turnstile> (Real r) = s \<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetError_valid:"(SetError s gno error)\<turnstile> x = s \<turnstile> x"
  using SetError_valid_vpage SetError_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

subsection\<open>user\<close>
lemma SetError_NC_User:
"gno \<notin> active_threads s \<longrightarrow> 
  thread_error (SetError s gno error) = thread_error s \<and>
  thread_pager (SetError s gno error) = thread_pager s \<and>
  thread_handler (SetError s gno error) = thread_handler s \<and>
  thread_message (SetError s gno error) = thread_message s \<and>
  thread_rcvWindow (SetError s gno error) = thread_rcvWindow s"
  by(auto simp add: SetError_def SetThreadError_def)

lemma SetError_NC_User':
" thread_pager (SetError s gno error) = thread_pager s \<and>
  thread_handler (SetError s gno error) = thread_handler s \<and>
  thread_message (SetError s gno error) = thread_message s \<and>
  thread_rcvWindow (SetError s gno error) = thread_rcvWindow s"
  by(auto simp add: SetError_def SetThreadError_def)

lemma SetError_NC_User_Other:
"(gno \<noteq> g \<longrightarrow>
  thread_pager (SetError s gno error) = thread_pager s \<and>
  thread_handler (SetError s gno error) = thread_handler s \<and>
  thread_message (SetError s gno error) = thread_message s \<and>
  thread_rcvWindow (SetError s gno error) = thread_rcvWindow s \<and>
  thread_error (SetError s gno error) g = thread_error s g)"
  by(auto simp add: SetError_def SetThreadError_def)

lemma SetError_C_User:
"(gno \<in> active_threads s \<and> gno \<notin> kIntThreads \<longrightarrow>
  thread_pager (SetError s gno error) gno = thread_pager s gno \<and>
  thread_handler (SetError s gno error) gno = thread_handler s gno \<and>
  thread_message (SetError s gno error) gno = thread_message s gno \<and>
  thread_rcvWindow (SetError s gno error) gno = thread_rcvWindow s gno \<and>
  thread_error (SetError s gno error) gno = Some error)"
  by(auto simp add: SetError_def SetThreadError_def)

subsection\<open>current\<close>
lemma SetError_NC_Current:
"current_thread (SetError s gno error) = current_thread s \<and>
 current_time (SetError s gno error) = current_time s"
  by(auto simp add: SetError_def SetThreadError_def)

subsection \<open>thread\<close>
lemma SetError_NC_Thread:
"threads (SetError s gno error) = threads s \<and>
 active_threads (SetError s gno error) = active_threads s \<and>
 thread_space (SetError s gno error) = thread_space s \<and>
 thread_scheduler (SetError s gno error) = thread_scheduler s \<and>
 thread_state (SetError s gno error) = thread_state s \<and>
 thread_priority (SetError s gno error) = thread_priority s \<and>
 thread_total_quantum (SetError s gno error) = thread_total_quantum s \<and>
 thread_timeslice_length (SetError s gno error) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetError s gno error) = thread_current_timeslice s"
  by(auto simp add: SetError_def SetThreadError_def)

subsection \<open>space\<close>
lemma SetError_NC_Space:
"spaces (SetError s gno error) = spaces s \<and>
 initialised_spaces (SetError s gno error) = initialised_spaces s \<and>
 space_threads (SetError s gno error) = space_threads s \<and>
 space_mapping (SetError s gno error) = space_mapping s"
  by(auto simp add: SetError_def SetThreadError_def spaces_def)

subsection \<open>IPC\<close>
lemma SetError_NC_IPC:
"thread_ipc_partner (SetError s gno error) = thread_ipc_partner s \<and>
 thread_ipc_timeout (SetError s gno error) = thread_ipc_timeout s \<and>
 thread_incoming (SetError s gno error) =  thread_incoming s"
  by(auto simp add: SetError_def SetThreadError_def)

subsection \<open>Scheduling\<close>
lemma SetError_NC_Scheduling:
"wait_queuing (SetError s gno error) = wait_queuing s \<and>
 ready_queuing (SetError s gno error) = ready_queuing s \<and>
 current_timeslice (SetError s gno error) = current_timeslice s"
  by(auto simp add: SetError_def SetThreadError_def)
end