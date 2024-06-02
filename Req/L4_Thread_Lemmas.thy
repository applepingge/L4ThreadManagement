theory L4_Thread_Lemmas       
  imports L4_Space_Lemmas
begin

section\<open>SetThreadPriority\<close>
subsection\<open>memory\<close>
lemma SetThreadPriority_direct_eq:"(SetThreadPriority s gno prio)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetThreadPriority_def direct_path_def)

lemma SetThreadPriority_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetThreadPriority s gno prio)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetThreadPriority s gno prio)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadPriority_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetThreadPriority s gno prio)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetThreadPriority s gno prio)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadPriority_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetThreadPriority_tran:"(SetThreadPriority s gno prio)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetThreadPriority_direct_eq tran_path.intros SetThreadPriority_tran1
  by auto

lemma SetThreadPriority_rtran:"(SetThreadPriority s gno prio)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetThreadPriority_tran rtran_tran
  by auto

lemma SetThreadPriority_valid_vpage:"(SetThreadPriority s gno prio) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetThreadPriority_direct_eq valid_page_def
  by auto

lemma SetThreadPriority_valid_rpage:"(SetThreadPriority s gno prio)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetThreadPriority_valid:"(SetThreadPriority s gno prio)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetThreadPriority_valid_vpage apply simp
  using SetThreadPriority_valid_rpage by simp

lemma SetThreadPriority_NC_Perms:"\<forall>sp v_page. get_perms (SetThreadPriority s gno prio) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetThreadPriority_def)

section\<open>SetThreadQuantum\<close>
subsection\<open>memory\<close>
lemma SetThreadQuantum_direct_eq:"(SetThreadQuantum s gno quan)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetThreadQuantum_def direct_path_def)

lemma SetThreadQuantum_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetThreadQuantum s gno quan)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetThreadQuantum s gno quan)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadQuantum_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetThreadQuantum s gno quan)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetThreadQuantum s gno quan)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadQuantum_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetThreadQuantum_tran:"(SetThreadQuantum s gno quan)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetThreadQuantum_direct_eq tran_path.intros SetThreadQuantum_tran1
  by auto

lemma SetThreadQuantum_rtran:"(SetThreadQuantum s gno quan)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetThreadQuantum_tran rtran_tran
  by auto

lemma SetThreadQuantum_valid_vpage:"(SetThreadQuantum s gno quan) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetThreadQuantum_direct_eq valid_page_def
  by auto

lemma SetThreadQuantum_valid_rpage:"(SetThreadQuantum s gno quan)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetThreadQuantum_valid:"(SetThreadQuantum s gno quan)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetThreadQuantum_valid_vpage apply simp
  using SetThreadQuantum_valid_rpage by simp

lemma SetThreadQuantum_NC_Perms:"\<forall>sp v_page. get_perms (SetThreadQuantum s gno quan) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetThreadQuantum_def)

section\<open>SetThreadTimeslice\<close>
subsection\<open>memory\<close>
lemma SetThreadTimeslice_direct_eq:"(SetThreadTimeslice s gno slice)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetThreadTimeslice_def direct_path_def)

lemma SetThreadTimeslice_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetThreadTimeslice s gno slice)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetThreadTimeslice s gno slice)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadTimeslice_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetThreadTimeslice s gno slice)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetThreadTimeslice s gno slice)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadTimeslice_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetThreadTimeslice_tran:"(SetThreadTimeslice s gno slice)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetThreadTimeslice_direct_eq tran_path.intros SetThreadTimeslice_tran1
  by auto

lemma SetThreadTimeslice_rtran:"(SetThreadTimeslice s gno slice)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetThreadTimeslice_tran rtran_tran
  by auto

lemma SetThreadTimeslice_valid_vpage:"(SetThreadTimeslice s gno slice) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetThreadTimeslice_direct_eq valid_page_def
  by auto

lemma SetThreadTimeslice_valid_rpage:"(SetThreadTimeslice s gno slice)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetThreadTimeslice_valid:"(SetThreadTimeslice s gno slice)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetThreadTimeslice_valid_vpage apply simp
  using SetThreadTimeslice_valid_rpage by simp

lemma SetThreadTimeslice_NC_Perms:"\<forall>sp v_page. get_perms (SetThreadTimeslice s gno slice) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetThreadTimeslice_def)

section\<open>SetThreadPager\<close>
subsection\<open>memory\<close>
lemma SetThreadPager_direct_eq:"(SetThreadPager s gno pager)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetThreadPager_def direct_path_def)

lemma SetThreadPager_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetThreadPager s gno pager)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetThreadPager s gno pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadPager_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetThreadPager s gno pager)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetThreadPager s gno pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadPager_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetThreadPager_tran:"(SetThreadPager s gno pager)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetThreadPager_direct_eq tran_path.intros SetThreadPager_tran1
  by auto

lemma SetThreadPager_rtran:"(SetThreadPager s gno pager)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetThreadPager_tran rtran_tran
  by auto

lemma SetThreadPager_valid_vpage:"(SetThreadPager s gno pager) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetThreadPager_direct_eq valid_page_def
  by auto

lemma SetThreadPager_valid_rpage:"(SetThreadPager s gno pager)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetThreadPager_valid:"(SetThreadPager s gno pager)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetThreadPager_valid_vpage apply simp
  using SetThreadPager_valid_rpage by simp

lemma SetThreadPager_NC_Perms:"\<forall>sp v_page. get_perms (SetThreadPager s gno pager) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetThreadPager_def)

section\<open>SetThreadState\<close>
subsection\<open>user\<close>
lemma SetThreadState_NC_User:
"thread_pager (SetThreadState s gno state) = thread_pager s \<and>
 thread_handler (SetThreadState s gno state) = thread_handler s \<and>
 thread_message (SetThreadState s gno state) = thread_message s \<and>
 thread_rcvWindow (SetThreadState s gno state) = thread_rcvWindow s \<and>
 thread_error (SetThreadState s gno state) = thread_error s"
  by(auto simp add: SetThreadState_def)

subsection\<open>current\<close>
lemma SetThreadState_NC_Current:
"current_thread (SetThreadState s gno state) = current_thread s \<and>
 current_time (SetThreadState s gno state) = current_time s"
  by(auto simp add: SetThreadState_def)

subsection\<open>thread\<close>
lemma SetThreadState_NC_Thread:
"threads (SetThreadState s gno state) = threads s \<and>
 active_threads (SetThreadState s gno state) = active_threads s \<and>
 thread_space (SetThreadState s gno state) = thread_space s \<and>
 thread_scheduler (SetThreadState s gno state) = thread_scheduler s \<and>
 thread_priority (SetThreadState s gno state) = thread_priority s \<and>
 thread_total_quantum (SetThreadState s gno state) = thread_total_quantum s \<and>
 thread_timeslice_length (SetThreadState s gno state) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetThreadState s gno state) = thread_current_timeslice s"
  by(auto simp add: SetThreadState_def)

subsection\<open>space\<close>
lemma SetThreadState_NC_Space:
"spaces (SetThreadState s gno state) = spaces s \<and>
 initialised_spaces (SetThreadState s gno state) = initialised_spaces s \<and>
 space_threads (SetThreadState s gno state) = space_threads s \<and>
 space_mapping (SetThreadState s gno state) = space_mapping s"
  by(auto simp add: SetThreadState_def spaces_def)

subsection\<open>IPC\<close>
lemma SetThreadState_NC_IPC:
"thread_ipc_partner (SetThreadState s gno state) = thread_ipc_partner s \<and>
 thread_ipc_timeout (SetThreadState s gno state) = thread_ipc_timeout s \<and>
 thread_incoming (SetThreadState s gno state) = thread_incoming s"
  by(auto simp add: SetThreadState_def)

subsection\<open>scheduling\<close>
lemma SetThreadState_NC_Scheduling:
"wait_queuing (SetThreadState s gno state) = wait_queuing s \<and>
 ready_queuing (SetThreadState s gno state) = ready_queuing s \<and>
 current_timeslice (SetThreadState s gno state) = current_timeslice s"
  by(auto simp add: SetThreadState_def)

subsection\<open>memory\<close>
lemma SetThreadState_direct_eq:"(SetThreadState s gno state)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetThreadState_def direct_path_def)

lemma SetThreadState_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetThreadState s gno state)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetThreadState s gno state)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadState_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetThreadState s gno state)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetThreadState s gno state)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadState_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetThreadState_tran:"(SetThreadState s gno state)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetThreadState_direct_eq tran_path.intros SetThreadState_tran1
  by auto

lemma SetThreadState_rtran:"(SetThreadState s gno state)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetThreadState_tran rtran_tran
  by auto

lemma SetThreadState_valid_vpage:"(SetThreadState s gno state) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetThreadState_direct_eq valid_page_def
  by auto

lemma SetThreadState_valid_rpage:"(SetThreadState s gno state)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetThreadState_valid:"(SetThreadState s gno state)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetThreadState_valid_vpage apply simp
  using SetThreadState_valid_rpage by simp

lemma SetThreadState_NC_Perms:"\<forall>sp v_page. get_perms (SetThreadState s gno state) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetThreadState_def)

section\<open>SetIpcPartner\<close>
subsection\<open>user\<close>
lemma SetIpcPartner_NC_User:
"thread_pager (SetIpcPartner s gno pa) = thread_pager s \<and>
 thread_handler (SetIpcPartner s gno pa) = thread_handler s \<and>
 thread_message (SetIpcPartner s gno pa) = thread_message s \<and>
 thread_rcvWindow (SetIpcPartner s gno pa) = thread_rcvWindow s \<and>
 thread_error (SetIpcPartner s gno pa) = thread_error s"
  by(auto simp add: SetIpcPartner_def)

subsection\<open>current\<close>
lemma SetIpcPartner_NC_Current:
"current_thread (SetIpcPartner s gno pa) = current_thread s \<and>
 current_time (SetIpcPartner s gno pa) = current_time s"
  by(auto simp add: SetIpcPartner_def)

subsection\<open>thread\<close>
lemma SetIpcPartner_NC_Thread:
"threads (SetIpcPartner s gno pa) = threads s \<and>
 active_threads (SetIpcPartner s gno pa) = active_threads s \<and>
 thread_space (SetIpcPartner s gno pa) = thread_space s \<and>
 thread_state (SetIpcPartner s gno pa) = thread_state s \<and>
 thread_scheduler (SetIpcPartner s gno pa) = thread_scheduler s \<and>
 thread_priority (SetIpcPartner s gno pa) = thread_priority s \<and>
 thread_total_quantum (SetIpcPartner s gno pa) = thread_total_quantum s \<and>
 thread_timeslice_length (SetIpcPartner s gno pa) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetIpcPartner s gno pa) = thread_current_timeslice s"
  by(auto simp add: SetIpcPartner_def)

subsection\<open>space\<close>
lemma SetIpcPartner_NC_Space:
"spaces (SetIpcPartner s gno pa) = spaces s \<and>
 initialised_spaces (SetIpcPartner s gno pa) = initialised_spaces s \<and>
 space_threads (SetIpcPartner s gno pa) = space_threads s \<and>
 space_mapping (SetIpcPartner s gno pa) = space_mapping s"
  by(auto simp add: SetIpcPartner_def spaces_def)

subsection\<open>IPC\<close>
lemma SetIpcPartner_NC_IPC:
"thread_ipc_timeout (SetIpcPartner s gno pa) = thread_ipc_timeout s \<and>
 thread_incoming (SetIpcPartner s gno pa) = thread_incoming s"
  by(auto simp add: SetIpcPartner_def)

subsection\<open>scheduling\<close>
lemma SetIpcPartner_NC_Scheduling:
"wait_queuing (SetIpcPartner s gno pa) = wait_queuing s \<and>
 ready_queuing (SetIpcPartner s gno pa) = ready_queuing s \<and>
 current_timeslice (SetIpcPartner s gno pa) = current_timeslice s"
  by(auto simp add: SetIpcPartner_def)

subsection\<open>memory\<close>
lemma SetIpcPartner_direct_eq:"(SetIpcPartner s gno pa)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetIpcPartner_def direct_path_def)

lemma SetIpcPartner_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetIpcPartner s gno pa)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetIpcPartner s gno pa)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetIpcPartner_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetIpcPartner s gno pa)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetIpcPartner s gno pa)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetIpcPartner_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetIpcPartner_tran:"(SetIpcPartner s gno pa)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetIpcPartner_direct_eq tran_path.intros SetIpcPartner_tran1
  by auto

lemma SetIpcPartner_rtran:"(SetIpcPartner s gno pa)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetIpcPartner_tran rtran_tran
  by auto

lemma SetIpcPartner_valid_vpage:"(SetIpcPartner s gno pa) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetIpcPartner_direct_eq valid_page_def
  by auto

lemma SetIpcPartner_valid_rpage:"(SetIpcPartner s gno pa)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetIpcPartner_valid:"(SetIpcPartner s gno pa)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetIpcPartner_valid_vpage apply simp
  using SetIpcPartner_valid_rpage by simp

lemma SetIpcPartner_NC_Perms:"\<forall>sp v_page. get_perms (SetIpcPartner s gno pa) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetIpcPartner_def)

section\<open>SetIpcTimeout\<close>
subsection\<open>user\<close>
lemma SetIpcTimeout_NC_User:
"thread_pager (SetIpcTimeout s gno t) = thread_pager s \<and>
 thread_handler (SetIpcTimeout s gno t) = thread_handler s \<and>
 thread_message (SetIpcTimeout s gno t) = thread_message s \<and>
 thread_rcvWindow (SetIpcTimeout s gno t) = thread_rcvWindow s \<and>
 thread_error (SetIpcTimeout s gno t) = thread_error s"
  by(auto simp add: SetIpcTimeout_def)

subsection\<open>current\<close>
lemma SetIpcTimeout_NC_Current:
"current_thread (SetIpcTimeout s gno t) = current_thread s \<and>
 current_time (SetIpcTimeout s gno t) = current_time s"
  by(auto simp add: SetIpcTimeout_def)

subsection\<open>thread\<close>
lemma SetIpcTimeout_NC_Thread:
"threads (SetIpcTimeout s gno t) = threads s \<and>
 active_threads (SetIpcTimeout s gno t) = active_threads s \<and>
 thread_space (SetIpcTimeout s gno t) = thread_space s \<and>
 thread_state (SetIpcTimeout s gno t) = thread_state s \<and>
 thread_scheduler (SetIpcTimeout s gno t) = thread_scheduler s \<and>
 thread_priority (SetIpcTimeout s gno t) = thread_priority s \<and>
 thread_total_quantum (SetIpcTimeout s gno t) = thread_total_quantum s \<and>
 thread_timeslice_length (SetIpcTimeout s gno t) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetIpcTimeout s gno t) = thread_current_timeslice s"
  by(auto simp add: SetIpcTimeout_def)

subsection\<open>space\<close>
lemma SetIpcTimeout_NC_Space:
"spaces (SetIpcTimeout s gno t) = spaces s \<and>
 initialised_spaces (SetIpcTimeout s gno t) = initialised_spaces s \<and>
 space_threads (SetIpcTimeout s gno t) = space_threads s \<and>
 space_mapping (SetIpcTimeout s gno t) = space_mapping s"
  by(auto simp add: SetIpcTimeout_def spaces_def)

subsection\<open>IPC\<close>
lemma SetIpcTimeout_NC_IPC:
"thread_ipc_partner (SetIpcTimeout s gno t) = thread_ipc_partner s \<and>
 thread_incoming (SetIpcTimeout s gno t) = thread_incoming s"
  by(auto simp add: SetIpcTimeout_def)

subsection\<open>scheduling\<close>
lemma SetIpcTimeout_NC_Scheduling:
"wait_queuing (SetIpcTimeout s gno t) = wait_queuing s \<and>
 ready_queuing (SetIpcTimeout s gno t) = ready_queuing s \<and>
 current_timeslice (SetIpcTimeout s gno t) = current_timeslice s"
  by(auto simp add: SetIpcTimeout_def)

subsection\<open>memory\<close>
lemma SetIpcTimeout_direct_eq:"(SetIpcTimeout s gno t)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetIpcTimeout_def direct_path_def)

lemma SetIpcTimeout_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetIpcTimeout s gno t)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetIpcTimeout s gno t)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetIpcTimeout_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetIpcTimeout s gno t)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetIpcTimeout s gno t)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetIpcTimeout_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetIpcTimeout_tran:"(SetIpcTimeout s gno t)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetIpcTimeout_direct_eq tran_path.intros SetIpcTimeout_tran1
  by auto

lemma SetIpcTimeout_rtran:"(SetIpcTimeout s gno t)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetIpcTimeout_tran rtran_tran
  by auto

lemma SetIpcTimeout_valid_vpage:"(SetIpcTimeout s gno t) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetIpcTimeout_direct_eq valid_page_def
  by auto

lemma SetIpcTimeout_valid_rpage:"(SetIpcTimeout s gno t)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetIpcTimeout_valid:"(SetIpcTimeout s gno t)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetIpcTimeout_valid_vpage apply simp
  using SetIpcTimeout_valid_rpage by simp

lemma SetIpcTimeout_NC_Perms:"\<forall>sp v_page. get_perms (SetIpcTimeout s gno t) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetIpcTimeout_def)

section\<open>SetThreadsIncomingDel\<close>
subsection\<open>user\<close>
lemma SetThreadsIncomingDel_NC_User:
"thread_pager (SetThreadsIncomingDel s t gno) = thread_pager s \<and>
 thread_handler (SetThreadsIncomingDel s t gno) = thread_handler s \<and>
 thread_message (SetThreadsIncomingDel s t gno) = thread_message s \<and>
 thread_rcvWindow (SetThreadsIncomingDel s t gno) = thread_rcvWindow s \<and>
 thread_error (SetThreadsIncomingDel s t gno) = thread_error s"
  by(auto simp add: SetThreadsIncomingDel_def)

subsection\<open>current\<close>
lemma SetThreadsIncomingDel_NC_Current:
"current_thread (SetThreadsIncomingDel s t gno) = current_thread s \<and>
 current_time (SetThreadsIncomingDel s t gno) = current_time s"
  by(auto simp add: SetThreadsIncomingDel_def)

subsection\<open>thread\<close>
lemma SetThreadsIncomingDel_NC_Thread:
"threads (SetThreadsIncomingDel s t gno) = threads s \<and>
 active_threads (SetThreadsIncomingDel s t gno) = active_threads s \<and>
 thread_space (SetThreadsIncomingDel s t gno) = thread_space s \<and>
 thread_state (SetThreadsIncomingDel s t gno) = thread_state s \<and>
 thread_scheduler (SetThreadsIncomingDel s t gno) = thread_scheduler s \<and>
 thread_priority (SetThreadsIncomingDel s t gno) = thread_priority s \<and>
 thread_total_quantum (SetThreadsIncomingDel s t gno) = thread_total_quantum s \<and>
 thread_timeslice_length (SetThreadsIncomingDel s t gno) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetThreadsIncomingDel s t gno) = thread_current_timeslice s"
  by(auto simp add: SetThreadsIncomingDel_def)

subsection\<open>space\<close>
lemma SetThreadsIncomingDel_NC_Space:
"spaces (SetThreadsIncomingDel s t gno) = spaces s \<and>
 initialised_spaces (SetThreadsIncomingDel s t gno) = initialised_spaces s \<and>
 space_threads (SetThreadsIncomingDel s t gno) = space_threads s \<and>
 space_mapping (SetThreadsIncomingDel s t gno) = space_mapping s"
  by(auto simp add: SetThreadsIncomingDel_def spaces_def)

subsection\<open>IPC\<close>
lemma SetThreadsIncomingDel_NC_IPC:
"thread_ipc_partner (SetThreadsIncomingDel s t gno) = thread_ipc_partner s \<and>
 thread_ipc_timeout (SetThreadsIncomingDel s t gno) = thread_ipc_timeout s"
  by(auto simp add: SetThreadsIncomingDel_def)

subsection\<open>scheduling\<close>
lemma SetThreadsIncomingDel_NC_Scheduling:
"wait_queuing (SetThreadsIncomingDel s t gno) = wait_queuing s \<and>
 ready_queuing (SetThreadsIncomingDel s t gno) = ready_queuing s \<and>
 current_timeslice (SetThreadsIncomingDel s t gno) = current_timeslice s"
  by(auto simp add: SetThreadsIncomingDel_def)

subsection\<open>memory\<close>
lemma SetThreadsIncomingDel_direct_eq:"(SetThreadsIncomingDel s t gno)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:SetThreadsIncomingDel_def direct_path_def)

lemma SetThreadsIncomingDel_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetThreadsIncomingDel s t gno)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetThreadsIncomingDel s t gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadsIncomingDel_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(SetThreadsIncomingDel s t gno)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetThreadsIncomingDel s t gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetThreadsIncomingDel_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetThreadsIncomingDel_tran:"(SetThreadsIncomingDel s t gno)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetThreadsIncomingDel_direct_eq tran_path.intros SetThreadsIncomingDel_tran1
  by auto

lemma SetThreadsIncomingDel_rtran:"(SetThreadsIncomingDel s t gno)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetThreadsIncomingDel_tran rtran_tran
  by auto

lemma SetThreadsIncomingDel_valid_vpage:"(SetThreadsIncomingDel s t gno) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetThreadsIncomingDel_direct_eq valid_page_def
  by auto

lemma SetThreadsIncomingDel_valid_rpage:"(SetThreadsIncomingDel s t gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetThreadsIncomingDel_valid:"(SetThreadsIncomingDel s t gno)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using SetThreadsIncomingDel_valid_vpage apply simp
  using SetThreadsIncomingDel_valid_rpage by simp

lemma SetThreadsIncomingDel_NC_Perms:"\<forall>sp v_page. get_perms (SetThreadsIncomingDel s t gno) sp v_page =
get_perms s sp v_page"
  by (auto simp add: get_perms_def SetThreadsIncomingDel_def)

section\<open>dequeue_ready\<close>
subsection\<open>user\<close>
lemma dequeue_ready_NC_User:
"thread_pager (dequeue_ready s gno) = thread_pager s \<and>
 thread_handler (dequeue_ready s gno) = thread_handler s \<and>
 thread_message (dequeue_ready s gno) = thread_message s \<and>
 thread_rcvWindow (dequeue_ready s gno) = thread_rcvWindow s \<and>
 thread_error (dequeue_ready s gno) = thread_error s"
  by(auto simp add:dequeue_ready_def)

subsection\<open>current\<close>
lemma dequeue_ready_NC_Current:
"current_thread (dequeue_ready s gno) = current_thread s \<and>
 current_time (dequeue_ready s gno) = current_time s"
  by(auto simp add:dequeue_ready_def)

subsection\<open>thread\<close>
lemma dequeue_ready_NC_Thread:
"threads (dequeue_ready s gno) = threads s \<and>
 active_threads (dequeue_ready s gno) = active_threads s \<and>
 thread_space (dequeue_ready s gno) = thread_space s \<and>
 thread_scheduler (dequeue_ready s gno) = thread_scheduler s \<and>
 thread_state (dequeue_ready s gno) = thread_state s \<and>
 thread_priority (dequeue_ready s gno) = thread_priority s \<and>
 thread_total_quantum (dequeue_ready s gno) = thread_total_quantum s \<and>
 thread_timeslice_length (dequeue_ready s gno) = thread_timeslice_length s \<and>
 thread_current_timeslice (dequeue_ready s gno) = thread_current_timeslice s"
  by(auto simp add:dequeue_ready_def)

subsection\<open>space\<close>
lemma dequeue_ready_NC_Space:
"spaces (dequeue_ready s gno) = spaces s \<and>
 initialised_spaces (dequeue_ready s gno) = initialised_spaces s \<and>
 space_threads (dequeue_ready s gno) = space_threads s \<and>
 space_mapping (dequeue_ready s gno) = space_mapping s"
  by(auto simp add:dequeue_ready_def spaces_def)

subsection\<open>IPC\<close>
lemma dequeue_ready_NC_IPC:
"thread_ipc_partner (dequeue_ready s gno) = thread_ipc_partner s \<and>
 thread_ipc_timeout (dequeue_ready s gno) = thread_ipc_timeout s \<and>
 thread_incoming (dequeue_ready s gno) =  thread_incoming s"
  by(auto simp add:dequeue_ready_def)

subsection\<open>scheduling\<close>
lemma dequeue_ready_NC_Scheduling:
"wait_queuing (dequeue_ready s gno) = wait_queuing s \<and>
 current_timeslice (dequeue_ready s gno) = current_timeslice s"
  by(auto simp add:dequeue_ready_def)

lemma dequeue_ready_NC_Scheduling1:
"set (ready_queuing (dequeue_ready s gno) i) \<subseteq> set(ready_queuing s i)"
  apply(auto simp add: dequeue_ready_def dequeue_ready_queuing_def Let_def)
  by (meson notin_set_remove1)

lemma dequeue_ready_C_Scheduling:
"(\<forall>prio. prio \<noteq> (GetThreadPriority s gno) \<longrightarrow> (ready_queuing (dequeue_ready s gno)) prio = (ready_queuing s) prio \<and>
         prio = (GetThreadPriority s gno) \<longrightarrow> (ready_queuing (dequeue_ready s gno)) prio = remove1 gno ((ready_queuing s) prio))"
  by(auto simp add:dequeue_ready_def)
  
subsection\<open>memory\<close>
lemma dequeue_ready_direct_eq:"(dequeue_ready s gno)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding dequeue_ready_def
  by(auto simp add:direct_path_def)

lemma dequeue_ready_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (dequeue_ready s gno)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(dequeue_ready s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using dequeue_ready_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(dequeue_ready s gno)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(dequeue_ready s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using dequeue_ready_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma dequeue_ready_tran:"(dequeue_ready s gno)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using dequeue_ready_direct_eq tran_path.intros dequeue_ready_tran1
  by auto

lemma dequeue_ready_rtran:"(dequeue_ready s gno)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using dequeue_ready_tran rtran_tran
  by auto

lemma dequeue_ready_valid_vpage:"(dequeue_ready s gno) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using dequeue_ready_direct_eq valid_page_def
  by auto

lemma dequeue_ready_valid_rpage:"(dequeue_ready s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma dequeue_ready_valid:"(dequeue_ready s gno)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using dequeue_ready_valid_vpage apply simp
  using dequeue_ready_valid_rpage by simp

section\<open>Unwind\<close>
subsection\<open>user\<close>
lemma Unwind_NC_User:
"thread_pager (Unwind s gno) = thread_pager s \<and>
 thread_handler (Unwind s gno) = thread_handler s \<and>
 thread_message (Unwind s gno) = thread_message s \<and>
 thread_rcvWindow (Unwind s gno) = thread_rcvWindow s \<and>
 thread_error (Unwind s gno) = thread_error s"
  by(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def)

subsection\<open>current\<close>
lemma Unwind_NC_Current:
"current_thread (Unwind s gno) = current_thread s \<and>
 current_time (Unwind s gno) = current_time s"
  by(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def )

subsection\<open>thread\<close>
lemma Unwind_NC_Thread:
"threads (Unwind s gno) = threads s \<and>
 active_threads (Unwind s gno) = active_threads s \<and>
 thread_space (Unwind s gno) = thread_space s \<and>
 thread_scheduler (Unwind s gno) = thread_scheduler s \<and>
 thread_state (Unwind s gno) = thread_state s \<and>
 thread_priority (Unwind s gno) = thread_priority s \<and>
 thread_total_quantum (Unwind s gno) = thread_total_quantum s \<and>
 thread_timeslice_length (Unwind s gno) = thread_timeslice_length s \<and>
 thread_current_timeslice (Unwind s gno) = thread_current_timeslice s"
  by(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def )

subsection\<open>space\<close>
lemma Unwind_NC_Space:
"spaces (Unwind s gno) = spaces s \<and>
 initialised_spaces (Unwind s gno) = initialised_spaces s \<and>
 space_threads (Unwind s gno) = space_threads s \<and>
 space_mapping (Unwind s gno) = space_mapping s"
  by(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def spaces_def)

subsection\<open>IPC\<close>
lemma Unwind_NC_IPC:
"thread_ipc_partner (Unwind s gno) = thread_ipc_partner s \<and>
 thread_ipc_timeout (Unwind s gno) = thread_ipc_timeout s"
  by(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def )

lemma Unwind_NC_IPC1:
"set(the (thread_incoming (Unwind s gno) t)) \<subseteq> set(the (thread_incoming s t))"
  apply(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def )
  by (meson notin_set_remove1)+

lemma Unwind_NC_IPC_Cond:
"gno \<notin> active_threads s \<Longrightarrow> 
thread_incoming (Unwind s gno) = thread_incoming s"
  unfolding Unwind_def by simp

lemma Unwind_NC_IPC_other:
"t \<noteq> TidToGno (GetIpcPartner s gno)\<Longrightarrow> 
thread_incoming (Unwind s gno) t = thread_incoming s t"
  unfolding Unwind_def Let_def SetThreadsIncomingDel_def dequeue_wait_def
  by auto

lemma Unwind_NC_IPC_Cond1:
"gno \<in> active_threads s \<and> \<not>(isPolling (GetThreadState s gno) \<and> 
GetIpcPartner s gno \<noteq> ANYTHREAD \<and> GetIpcPartner s gno \<noteq> NILTHREAD) \<Longrightarrow> 
thread_incoming (Unwind s gno) = thread_incoming s"
  unfolding Unwind_def Let_def dequeue_wait_def
  by auto

lemma Unwind_C_IPC:
"gno \<in> active_threads s \<and> isPolling (GetThreadState s gno) \<and> 
GetIpcPartner s gno \<noteq> ANYTHREAD \<and> GetIpcPartner s gno \<noteq> NILTHREAD \<Longrightarrow> 
thread_incoming (Unwind s gno) (TidToGno (GetIpcPartner s gno)) = 
Some (remove1 gno (the (thread_incoming s (TidToGno (GetIpcPartner s gno)))))"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def
  by auto

subsection\<open>scheduling\<close>
lemma Unwind_NC_Scheduling:
"ready_queuing (Unwind s gno) = ready_queuing s \<and>
 current_timeslice (Unwind s gno) = current_timeslice s"
  by(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def)

lemma Unwind_NC_Scheduling1:
"set (wait_queuing (Unwind s gno)) \<subseteq> set(wait_queuing s)"
  apply(auto simp add: Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def)
  by (meson notin_set_remove1)+

subsection\<open>memory\<close>
lemma Unwind_direct_eq:"(Unwind s gno)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  by(auto simp add:Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def direct_path_def)

lemma Unwind_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (Unwind s gno)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(Unwind s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using Unwind_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(Unwind s gno)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(Unwind s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using Unwind_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma Unwind_tran:"(Unwind s gno)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using Unwind_direct_eq tran_path.intros Unwind_tran1
  by auto

lemma Unwind_rtran:"(Unwind s gno)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using Unwind_tran rtran_tran
  by auto

lemma Unwind_valid_vpage:"(Unwind s gno) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using Unwind_direct_eq valid_page_def
  by auto

lemma Unwind_valid_rpage:"(Unwind s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma Unwind_valid:"(Unwind s gno)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using Unwind_valid_vpage apply simp
  using Unwind_valid_rpage by simp

lemma Unwind_NC_Perms:"\<forall>sp v_page. get_perms (Unwind s gno) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def Unwind_def dequeue_wait_def SetThreadsIncomingDel_def Let_def 
  by auto

section\<open>CreateThread\<close>
subsection\<open>user\<close>
lemma CreateThread_NC_User:
"\<not>(CreateThread_Cond SysConf s gno space scheduler) \<longrightarrow>
 thread_error (CreateThread SysConf s gno space scheduler) = thread_error s \<and>
 thread_pager (CreateThread SysConf s gno space scheduler) = thread_pager s \<and>
 thread_handler (CreateThread SysConf s gno space scheduler) = thread_handler s \<and>
 thread_message (CreateThread SysConf s gno space scheduler) = thread_message s \<and>
 thread_rcvWindow (CreateThread SysConf s gno space scheduler) = thread_rcvWindow s"
  unfolding CreateThread_def Let_def
  by(simp add:SetError_NC_User CreateAddressSpace_NC_User)

lemma CreateThread_NC_User_Other:
"g \<noteq> current_thread s \<longrightarrow>
  thread_error (CreateThread SysConf s gno space scheduler) g = thread_error s g"
  unfolding CreateThread_def Let_def CreateThread_Cond_def
  by(auto simp add:SetError_def SetThreadError_def
CreateAddressSpace_NC_User CreateAddressSpace_NC_Thread CreateAddressSpace_NC_Current)

lemma CreateThread_C_User:
"CreateThread_Cond SysConf s gno space scheduler \<longrightarrow>
  thread_pager (CreateThread SysConf s gno space scheduler) = thread_pager s \<and>
  thread_handler (CreateThread SysConf s gno space scheduler) = thread_handler s \<and>
  thread_message (CreateThread SysConf s gno space scheduler) = thread_message s \<and>
  thread_rcvWindow (CreateThread SysConf s gno space scheduler) = thread_rcvWindow s \<and>
  thread_error (CreateThread SysConf s gno space scheduler) (current_thread s) = Some eNoError"
  unfolding CreateThread_def Let_def CreateThread_Cond_def
  by(auto simp add:SetError_def SetThreadError_def
CreateAddressSpace_NC_User CreateAddressSpace_NC_Thread CreateAddressSpace_NC_Current)

subsection\<open>current\<close>
lemma CreateThread_NC_Current:
"current_thread (CreateThread SysConf s gno space scheduler) = current_thread s \<and>
 current_time (CreateThread SysConf s gno space scheduler) = current_time s"
  unfolding CreateThread_def Let_def
  by(simp add:SetError_NC_Current CreateAddressSpace_NC_Current)

subsection\<open>thread\<close>
lemma CreateThread_C_Thread:
"CreateThread_Cond SysConf s gno space scheduler \<longrightarrow>
  threads (CreateThread SysConf s gno space scheduler) = threads s \<union> {gno} \<and>
  thread_space (CreateThread SysConf s gno space scheduler) gno = Some space \<and>
  thread_scheduler (CreateThread SysConf s gno space scheduler) gno = Some scheduler \<and>
  thread_state (CreateThread SysConf s gno space scheduler) gno = Some tsAborted \<and>
  thread_priority (CreateThread SysConf s gno space scheduler) gno = Some DEFAULT_PRIORITY \<and>
  thread_total_quantum (CreateThread SysConf s gno space scheduler) gno = Some DEFAULT_TOTAL_QUANTUM \<and>
  thread_timeslice_length (CreateThread SysConf s gno space scheduler) gno = Some DEFAULT_TIMESLICE_LENGTH \<and>
  thread_current_timeslice (CreateThread SysConf s gno space scheduler) gno = Some DEFAULT_TIMESLICE_LENGTH"
  unfolding CreateThread_def Let_def
  by(auto simp add:SetError_NC_Thread CreateAddressSpace_NC_Thread)

lemma CreateThread_NC_Thread:
"\<not>(CreateThread_Cond SysConf s gno space scheduler) \<longrightarrow>
   threads (CreateThread SysConf s gno space scheduler) = threads s \<and>
   active_threads (CreateThread SysConf s gno space scheduler) = active_threads s \<and>
   thread_space (CreateThread SysConf s gno space scheduler) = thread_space s \<and>
   thread_scheduler (CreateThread SysConf s gno space scheduler) = thread_scheduler s \<and>
   thread_state (CreateThread SysConf s gno space scheduler) = thread_state s \<and>
   thread_priority (CreateThread SysConf s gno space scheduler) = thread_priority s \<and>
   thread_total_quantum (CreateThread SysConf s gno space scheduler) = thread_total_quantum s \<and>
   thread_timeslice_length (CreateThread SysConf s gno space scheduler) = thread_timeslice_length s \<and>
   thread_current_timeslice (CreateThread SysConf s gno space scheduler) = thread_current_timeslice s"
  by(simp add:CreateThread_def)

lemma CreateThread_NC_Thread_Other:
"g \<noteq> gno \<longrightarrow>
  thread_space (CreateThread SysConf s gno space scheduler) g = thread_space s g \<and>
  thread_scheduler (CreateThread SysConf s gno space scheduler) g = thread_scheduler s g \<and>
  thread_state (CreateThread SysConf s gno space scheduler) g = thread_state s g \<and>
  thread_priority (CreateThread SysConf s gno space scheduler) g = thread_priority s g \<and>
  thread_total_quantum (CreateThread SysConf s gno space scheduler) g = thread_total_quantum s g \<and>
  thread_timeslice_length (CreateThread SysConf s gno space scheduler) g = thread_timeslice_length s g \<and>
  thread_current_timeslice (CreateThread SysConf s gno space scheduler) g = thread_current_timeslice s g"
  unfolding CreateThread_def Let_def
  by(simp add: CreateAddressSpace_NC_Thread SetError_NC_Thread)

subsection\<open>space\<close>
lemma CreateTcb_NC_Space:
"spaces (CreateTcb s gno space scheduler) = spaces s"
  unfolding CreateTcb_def spaces_def by simp

lemma CreateThread_C_Space:
"(CreateThread_Cond SysConf s gno space scheduler) \<and> space \<notin> spaces s \<Longrightarrow>
  (spaces (CreateThread SysConf s gno space scheduler) = spaces s \<union> {space} \<and>
  (initialised_spaces (CreateThread SysConf s gno space scheduler) = initialised_spaces s) \<and>
  (space_threads (CreateThread SysConf s gno space scheduler) space = Some {gno}) \<and>
  (space_mapping (CreateThread SysConf s gno space scheduler) space = Some (\<lambda>vp. None)))"
  apply rule
  subgoal
    unfolding CreateThread_def Let_def
    apply simp
    apply(subst SetError_NC_Space)
    apply(simp add:spaces_def)
    by(auto simp add:CreateThread_Cond_def CreateAddressSpace_C_Space[unfolded spaces_def])
  apply rule
  subgoal
    unfolding CreateThread_def Let_def
    apply simp
    apply(subst SetError_NC_Space)
    apply simp
    using CreateAddressSpace_C_Space CreateThread_Cond_def
    by auto
  apply rule
  subgoal
    unfolding CreateThread_def Let_def
    apply simp
    apply(subst SetError_NC_Space)
    apply simp
    apply(simp add:spaces_def)
    by(auto simp add:CreateThread_Cond_def CreateAddressSpace_C_Space[unfolded spaces_def])
  unfolding CreateThread_def Let_def
  apply simp
  apply(subst SetError_NC_Space)
  apply simp
  by(auto simp add:CreateThread_Cond_def CreateAddressSpace_C_Space)

lemma CreateThread_C_Space':
"(CreateThread_Cond SysConf s gno space scheduler) \<and> space \<in> spaces s \<Longrightarrow>
  (spaces (CreateThread SysConf s gno space scheduler) = spaces s) \<and>
  (initialised_spaces (CreateThread SysConf s gno space scheduler) = initialised_spaces s) \<and>
  (space_threads (CreateThread SysConf s gno space scheduler) space = Some (the (space_threads s space) \<union> {gno})) \<and>
  (space_mapping (CreateThread SysConf s gno space scheduler) space = space_mapping s space)"
  apply rule
  subgoal
    unfolding CreateThread_def Let_def
    apply simp
    apply(subst SetError_NC_Space)
    by (auto simp add:spaces_def)
  apply rule
  subgoal
    unfolding CreateThread_def Let_def
    apply simp
    apply(subst SetError_NC_Space)
    by simp
  apply rule
  subgoal
    unfolding CreateThread_def Let_def
    apply simp
    apply(subst SetError_NC_Space)
    by simp
  unfolding CreateThread_def Let_def
  apply simp
  apply(subst SetError_NC_Space)
  by simp

lemma CreateThread_NC_Space_Other:
"sp \<noteq> space \<longrightarrow>
  (space_threads (CreateThread SysConf s gno space scheduler) sp = space_threads s sp) \<and>
  (space_mapping (CreateThread SysConf s gno space scheduler) sp = space_mapping s sp)"
  by(auto simp add:CreateThread_def Let_def SetError_NC_Space CreateAddressSpace_NC_Space_Other)

lemma CreateThread_NC_Space:
"\<not>(CreateThread_Cond SysConf s gno space scheduler) \<longrightarrow>
  (spaces (CreateThread SysConf s gno space scheduler) = spaces s \<and>
  (initialised_spaces (CreateThread SysConf s gno space scheduler) = initialised_spaces s) \<and>
  (space_threads (CreateThread SysConf s gno space scheduler) = space_threads s) \<and>
  (space_mapping (CreateThread SysConf s gno space scheduler) = space_mapping s))"
  by(auto simp add:CreateThread_def spaces_def)

subsection\<open>IPC\<close>
lemma CreateThread_NC_IPC:
"\<not>(CreateThread_Cond SysConf s gno space scheduler) \<longrightarrow>
  thread_ipc_partner (CreateThread SysConf s gno space scheduler) = thread_ipc_partner s \<and>
  thread_ipc_timeout (CreateThread SysConf s gno space scheduler) = thread_ipc_timeout s \<and>
  thread_incoming (CreateThread SysConf s gno space scheduler) =  thread_incoming s \<and>
  thread_recv_for (CreateThread SysConf s gno space scheduler) = thread_recv_for s \<and>
  thread_recv_timeout (CreateThread SysConf s gno space scheduler) = thread_recv_timeout s"
  by(simp add:CreateThread_def)

lemma CreateThread_NC_IPC_Other:
"g \<noteq> gno \<longrightarrow>
  thread_ipc_partner (CreateThread SysConf s gno space scheduler) g = thread_ipc_partner s g \<and>
  thread_ipc_timeout (CreateThread SysConf s gno space scheduler) g = thread_ipc_timeout s g \<and>
  thread_incoming (CreateThread SysConf s gno space scheduler) g =  thread_incoming s g"
  by(auto simp add:CreateThread_def Let_def SetError_NC_IPC CreateAddressSpace_NC_IPC)

lemma CreateThread_C_IPC:
"(CreateThread_Cond SysConf s gno space scheduler) \<longrightarrow>
  thread_ipc_partner (CreateThread SysConf s gno space scheduler) gno = Some NILTHREAD \<and>
  thread_ipc_timeout (CreateThread SysConf s gno space scheduler) gno = Some eInfiniteTimeout \<and>
  thread_incoming (CreateThread SysConf s gno space scheduler) gno = Some []"
  by(auto simp add:CreateThread_def Let_def CreateAddressSpace_NC_IPC SetError_NC_IPC)

subsection\<open>scheduling\<close>
lemma CreateThread_NC_Scheduling:
"wait_queuing (CreateThread SysConf s gno space scheduler) = wait_queuing s \<and>
 ready_queuing (CreateThread SysConf s gno space scheduler) = ready_queuing s \<and>
 current_timeslice (CreateThread SysConf s gno space scheduler) = current_timeslice s"
  unfolding CreateThread_def Let_def
  by(simp add:SetError_NC_Scheduling CreateAddressSpace_NC_Scheduling)

subsection\<open>memory\<close>
lemma CreateThread_direct_eq:"(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
proof-
  show "(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
    unfolding CreateThread_def
    apply(rule if_respect_eq)
     apply(rule let_respect_eq)
      defer 1
      apply(clarsimp simp: SetError_direct_eq)
    subgoal unfolding direct_path_def by simp
    apply simp
    using CreateAddressSpace_direct_eq by auto
qed

lemma CreateThread_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>+y"
proof-
  show " s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>+y"
  proof(induct rule:tran_path.induct)
    case (one_path x y)
    thm one_path.hyps
    then have "(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>1y"
      using CreateThread_direct_eq by simp
    then show ?case
      by(rule tran_path.intros)
  next
    case (tran_path x y z)
    then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
      have h3: "(CreateThread SysConf s gno space scheduler)\<turnstile>y\<leadsto>\<^sup>+z"
      by (simp add: tran_path.hyps(3))
    then have h21:"(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>1y"
      using CreateThread_direct_eq h2 by simp
    then show ?case
      using h3 tran_path.intros(2) by blast
  qed
qed
  
lemma CreateThread_tran:"(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
proof-
  show "(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
    apply(rule iffI)
     apply(induct rule: tran_path.induct)
    using CreateThread_direct_eq tran_path.intros CreateThread_tran1
    by auto
qed

lemma CreateThread_rtran:"(CreateThread SysConf s gno space scheduler)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using CreateThread_tran rtran_tran
  by auto

lemma CreateThread_valid_vpage:"
(CreateThread SysConf s gno space scheduler) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using CreateThread_direct_eq valid_page_def
  by auto

lemma CreateThread_valid_rpage:"(CreateThread SysConf s gno space scheduler)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma CreateThread_valid:"(CreateThread SysConf s gno space scheduler)\<turnstile> x = s\<turnstile>x"
  using CreateThread_valid_vpage CreateThread_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

section\<open>ActivateThread\<close>
subsection\<open>user\<close>
lemma ActivateThread_C_User:
"((current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and>
 (gno \<in> threads s) \<and> (gno \<notin> active_threads s) \<and> (pager \<in> threads s)) \<longrightarrow>
  thread_pager (ActivateThread SysConf s gno pager) gno = Some (Global pager) \<and>
  thread_handler (ActivateThread SysConf s gno pager) gno = Some NILTHREAD \<and>
  thread_message (ActivateThread SysConf s gno pager) gno = Some (UNTYPED 0) \<and>
  thread_rcvWindow (ActivateThread SysConf s gno pager) gno = Some (0,0,{}) \<and>
  thread_error (ActivateThread SysConf s gno pager) gno = Some eNoError"
  apply(subgoal_tac "(current_thread s \<in> active_threads s) \<Longrightarrow> (gno \<notin> active_threads s) \<Longrightarrow> current_thread s \<noteq> gno")
  by(auto simp add:ActivateThread_def SetError_NC_User_Other)

lemma ActivateThread_NC_User_Cond:
"\<not>((current_thread s \<in> active_threads s) \<and> (gno \<in> threads s) \<and> (gno \<notin> active_threads s) \<and>
    (pager \<in> threads s)) \<longrightarrow>
  thread_pager (ActivateThread SysConf s gno pager) = thread_pager s \<and>
  thread_handler (ActivateThread SysConf s gno pager) = thread_handler s \<and>
  thread_message (ActivateThread SysConf s gno pager) = thread_message s \<and>
  thread_rcvWindow (ActivateThread SysConf s gno pager) = thread_rcvWindow s \<and>
  thread_error (ActivateThread SysConf s gno pager) = thread_error s"
  by(simp add:ActivateThread_def)

lemma ActivateThread_NC_User_Other:
" g \<noteq> gno \<longrightarrow> 
 thread_pager (ActivateThread SysConf s gno pager) g = thread_pager s g \<and>
 thread_handler (ActivateThread SysConf s gno pager) g = thread_handler s g \<and>
 thread_message (ActivateThread SysConf s gno pager) g = thread_message s g \<and>
 thread_rcvWindow (ActivateThread SysConf s gno pager) g = thread_rcvWindow s g"
  unfolding ActivateThread_def Let_def SetError_def SetThreadError_def
  by auto

lemma ActivateThread_NC_User_Other1:
" (current_thread s \<in> active_threads s) \<and> (gno \<in> threads s) \<and> (gno \<notin> active_threads s) \<and>
    (pager \<in> threads s) \<and> g \<noteq> current_thread s \<and> g \<noteq> gno \<longrightarrow>
  thread_error (ActivateThread SysConf s gno pager) g = thread_error s g"
  by(auto simp add:ActivateThread_def SetError_NC_User_Other)
                                                              
subsection\<open>current\<close>
lemma ActivateThread_NC_Current:
"current_thread (ActivateThread SysConf s gno pager) = current_thread s \<and>
 current_time (ActivateThread SysConf s gno pager) = current_time s"
  unfolding ActivateThread_def Let_def
  by(simp add: SetError_NC_Current)

subsection \<open>thread\<close>
lemma ActivateThread_C_Thread:
"(current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and> (gno \<in> threads s) \<and> (gno \<notin> active_threads s) \<and>
    (pager \<in> threads s) \<longrightarrow>
 active_threads (ActivateThread SysConf s gno pager) = active_threads s \<union> {gno} \<and>
 thread_state (ActivateThread SysConf s gno pager) gno = Some tsWaitingForever"
  by (auto simp add:ActivateThread_def SetError_NC_Thread)

lemma ActivateThread_NC_Thread:
"threads (ActivateThread SysConf s gno pager) = threads s \<and>
 thread_space (ActivateThread SysConf s gno pager) = thread_space s \<and>
 thread_scheduler (ActivateThread SysConf s gno pager) = thread_scheduler s \<and>
 thread_priority (ActivateThread SysConf s gno pager) = thread_priority s \<and>
 thread_total_quantum (ActivateThread SysConf s gno pager) = thread_total_quantum s \<and>
 thread_timeslice_length (ActivateThread SysConf s gno pager) = thread_timeslice_length s \<and>
 thread_current_timeslice (ActivateThread SysConf s gno pager) = thread_current_timeslice s"
  unfolding ActivateThread_def Let_def
  by(simp add: SetError_NC_Thread)

subsection \<open>space\<close>
lemma ActivateThread_NC_Space:
"spaces (ActivateThread SysConf s gno pager) = spaces s \<and>
 initialised_spaces (ActivateThread SysConf s gno pager) = initialised_spaces s \<and>
 space_threads (ActivateThread SysConf s gno pager) = space_threads s \<and>
 space_mapping (ActivateThread SysConf s gno pager) = space_mapping s"
  unfolding ActivateThread_def Let_def
  by(simp add: SetError_NC_Space spaces_def)

subsection \<open>IPC\<close>
lemma ActivateThread_C_IPC:
"(current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and> (gno \<in> threads s) \<and> (gno \<notin> active_threads s) \<and>
    (pager \<in> threads s) \<longrightarrow>
 thread_ipc_partner (ActivateThread SysConf s gno pager) gno = Some (Global pager) \<and>
 thread_ipc_timeout (ActivateThread SysConf s gno pager) gno = Some eInfiniteTimeout"
  by(auto simp add:ActivateThread_def SetError_NC_IPC)

lemma ActivateThread_NC_IPC:
"thread_incoming (ActivateThread SysConf s gno pager) =  thread_incoming s"
  by(auto simp add: ActivateThread_def SetError_NC_IPC)

subsection \<open>Scheduling\<close>
lemma ActivateThread_NC_Scheduling:
"wait_queuing (ActivateThread SysConf s gno pager) = wait_queuing s \<and>
 ready_queuing (ActivateThread SysConf s gno pager) = ready_queuing s \<and>
 current_timeslice (ActivateThread SysConf s gno pager) = current_timeslice s"
  by(simp add:ActivateThread_def SetError_NC_Scheduling)

subsection \<open>memory\<close>
lemma ActivateThread_direct_eq:"(ActivateThread SysConf s gno pager)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding ActivateThread_def Let_def
  using SetError_direct_eq
  by(auto simp add:direct_path_def)

lemma ActivateThread_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (ActivateThread SysConf s gno pager)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(ActivateThread SysConf s gno pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using ActivateThread_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(ActivateThread SysConf s gno pager)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(ActivateThread SysConf s gno pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using ActivateThread_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed

lemma ActivateThread_tran:" (ActivateThread SysConf s gno pager)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
  apply(induct rule: tran_path.induct)
  using ActivateThread_direct_eq tran_path.intros ActivateThread_tran1
  by auto

lemma ActivateThread_rtran:"(ActivateThread SysConf s gno pager)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using ActivateThread_tran rtran_tran
  by auto

lemma ActivateThread_valid_vpage:"(ActivateThread SysConf s gno pager) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using ActivateThread_direct_eq valid_page_def
  by auto

lemma ActivateThread_valid_rpage:"(ActivateThread SysConf s gno pager)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma ActivateThread_valid:"(ActivateThread SysConf s gno pager)\<turnstile> x = s\<turnstile>x"
  using ActivateThread_valid_vpage ActivateThread_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma ActivateThread_NC_Perms:"\<forall>sp v_page. get_perms (ActivateThread SysConf s gno pager) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def ActivateThread_def SetThreadScheduler_def
SetError_def SetThreadError_def 
  by auto

section\<open>CreateActiveThread\<close>
subsection\<open>user\<close>
lemma CreateActiveThread_C_User:
"CreateActiveThread_Cond SysConf s gno space scheduler pager \<longrightarrow>
  thread_pager (CreateActiveThread SysConf s gno space scheduler pager) gno = Some (Global pager) \<and>
  thread_handler (CreateActiveThread SysConf s gno space scheduler pager) gno = Some NILTHREAD \<and>
  thread_message (CreateActiveThread SysConf s gno space scheduler pager) gno = Some (UNTYPED 0) \<and>
  thread_rcvWindow (CreateActiveThread SysConf s gno space scheduler pager) gno = Some (0,0,{}) \<and>
  thread_error (CreateActiveThread SysConf s gno space scheduler pager) gno = Some eNoError \<and>
  thread_error (CreateActiveThread SysConf s gno space scheduler pager) 
          (current_thread (CreateActiveThread SysConf s gno space scheduler pager)) = Some eNoError"
  by (auto simp add:CreateActiveThread_def CreateActiveThread_Cond_def SetError_def SetThreadError_def)

lemma CreateActiveThread_NC_User_Other:
"g \<noteq> gno \<longrightarrow>
 thread_pager (CreateActiveThread SysConf s gno space scheduler pager) g = thread_pager s g\<and>
 thread_handler (CreateActiveThread SysConf s gno space scheduler pager) g = thread_handler s g\<and>
 thread_message (CreateActiveThread SysConf s gno space scheduler pager) g = thread_message s g\<and>
 thread_rcvWindow (CreateActiveThread SysConf s gno space scheduler pager) g = thread_rcvWindow s g"
  by (auto simp add:CreateActiveThread_def Let_def SetError_def SetThreadError_def)

lemma CreateActiveThread_NC_User_Other1:
"CreateActiveThread_Cond SysConf s gno space scheduler pager \<and> g \<noteq> current_thread s \<and> g \<noteq> gno\<longrightarrow>
thread_error (CreateActiveThread SysConf s gno space scheduler pager) g = thread_error s g"
  by (auto simp add: CreateActiveThread_def CreateActiveThread_Cond_def SetError_NC_User_Other)

subsection\<open>current\<close>
lemma CreateActiveThread_NC_Current:
"current_thread (CreateActiveThread SysConf s gno space scheduler pager) = current_thread s \<and>
 current_time (CreateActiveThread SysConf s gno space scheduler pager) = current_time s"
  by(auto simp add:CreateActiveThread_def SetError_NC_Current)

subsection \<open>thread\<close>
lemma CreateActiveThread_C_Thread:
"CreateActiveThread_Cond SysConf s gno space scheduler pager \<longrightarrow>
 threads (CreateActiveThread SysConf s gno space scheduler pager) = threads s \<union> {gno} \<and>
 active_threads (CreateActiveThread SysConf s gno space scheduler pager) = active_threads s \<union> {gno} \<and>
 thread_space (CreateActiveThread SysConf s gno space scheduler pager) gno = Some space\<and>
 thread_scheduler (CreateActiveThread SysConf s gno space scheduler pager) gno = Some scheduler\<and>
 thread_state (CreateActiveThread SysConf s gno space scheduler pager) gno = Some tsWaitingForever \<and>
 thread_priority (CreateActiveThread SysConf s gno space scheduler pager) gno = Some DEFAULT_PRIORITY\<and>
 thread_total_quantum (CreateActiveThread SysConf s gno space scheduler pager) gno = Some DEFAULT_TOTAL_QUANTUM \<and>
 thread_timeslice_length (CreateActiveThread SysConf s gno space scheduler pager) gno = Some DEFAULT_TIMESLICE_LENGTH \<and>
 thread_current_timeslice (CreateActiveThread SysConf s gno space scheduler pager) gno = Some DEFAULT_TIMESLICE_LENGTH"
  by(auto simp add:CreateActiveThread_def SetError_NC_Thread)

lemma CreateActiveThread_NC_Thread_Cond:
"\<not>(CreateActiveThread_Cond SysConf s gno space scheduler pager) \<longrightarrow>
 threads (CreateActiveThread SysConf s gno space scheduler pager) = threads s \<and>
 active_threads (CreateActiveThread SysConf s gno space scheduler pager) = active_threads s \<and>
 thread_space (CreateActiveThread SysConf s gno space scheduler pager)  = thread_space s \<and>
 thread_scheduler (CreateActiveThread SysConf s gno space scheduler pager) = thread_scheduler s\<and>
 thread_state (CreateActiveThread SysConf s gno space scheduler pager) = thread_state s \<and>
 thread_priority (CreateActiveThread SysConf s gno space scheduler pager) = thread_priority s \<and>
 thread_total_quantum (CreateActiveThread SysConf s gno space scheduler pager) = thread_total_quantum s \<and>
 thread_timeslice_length (CreateActiveThread SysConf s gno space scheduler pager) = thread_timeslice_length s \<and>
 thread_current_timeslice (CreateActiveThread SysConf s gno space scheduler pager) = thread_current_timeslice s"
  by (simp add:CreateActiveThread_def)

lemma CreateActiveThread_NC_Thread_Other:
"g \<noteq> gno \<longrightarrow>
 thread_space (CreateActiveThread SysConf s gno space scheduler pager) g = thread_space s g \<and>
 thread_scheduler (CreateActiveThread SysConf s gno space scheduler pager) g = thread_scheduler s g \<and>
 thread_state (CreateActiveThread SysConf s gno space scheduler pager) g = thread_state s g \<and>
 thread_priority (CreateActiveThread SysConf s gno space scheduler pager) g = thread_priority s g \<and>
 thread_total_quantum (CreateActiveThread SysConf s gno space scheduler pager) g = thread_total_quantum s g \<and>
 thread_timeslice_length (CreateActiveThread SysConf s gno space scheduler pager) g = thread_timeslice_length s g \<and>
 thread_current_timeslice (CreateActiveThread SysConf s gno space scheduler pager) g = thread_current_timeslice s g"
  by(auto simp add:CreateActiveThread_def SetError_NC_Thread)

subsection \<open>space\<close>
lemma CreateActiveThread_NC_Space:
"spaces (CreateActiveThread SysConf s gno space scheduler pager) = spaces s \<and>
 initialised_spaces (CreateActiveThread SysConf s gno space scheduler pager) = initialised_spaces s \<and>
 space_mapping (CreateActiveThread SysConf s gno space scheduler pager) = space_mapping s"
  by (auto simp add:CreateActiveThread_def Let_def spaces_def SetError_NC_Space)
                                    
lemma CreateActiveThread_C_Space:"CreateActiveThread_Cond SysConf s gno space scheduler pager \<longrightarrow> 
space_threads (CreateActiveThread SysConf s gno space scheduler pager) space = Some (the (space_threads s space) \<union> {gno})"
  by (auto simp add:CreateActiveThread_def SetError_NC_Space)

lemma CreateActiveThread_NC_Space_Cond:"\<not>CreateActiveThread_Cond SysConf s gno space scheduler pager \<longrightarrow> 
space_threads (CreateActiveThread SysConf s gno space scheduler pager) space = space_threads s space"
  by (auto simp add:CreateActiveThread_def SetError_NC_Space)

lemma CreateActiveThread_NC_Space_Other:"sp \<noteq> space \<longrightarrow> 
space_threads (CreateActiveThread SysConf s gno space scheduler pager) sp = space_threads s sp"
  by (auto simp add:CreateActiveThread_def SetError_NC_Space)

subsection \<open>IPC\<close>
lemma CreateActiveThread_NC_IPC_Cond:
"\<not>(CreateActiveThread_Cond SysConf s gno space scheduler pager) \<longrightarrow>
 thread_ipc_partner (CreateActiveThread SysConf s gno space scheduler pager) = thread_ipc_partner s \<and>
 thread_ipc_timeout (CreateActiveThread SysConf s gno space scheduler pager) = thread_ipc_timeout s \<and>
 thread_incoming (CreateActiveThread SysConf s gno space scheduler pager) =  thread_incoming s"
  by(simp add:CreateActiveThread_def)

lemma CreateActiveThread_NC_IPC_Other:
"(CreateActiveThread_Cond SysConf s gno space scheduler pager) \<and> g \<noteq> gno \<longrightarrow>
 thread_ipc_partner (CreateActiveThread SysConf s gno space scheduler pager) g = thread_ipc_partner s g \<and>
 thread_ipc_timeout (CreateActiveThread SysConf s gno space scheduler pager) g = thread_ipc_timeout s g \<and>
 thread_incoming (CreateActiveThread SysConf s gno space scheduler pager) g = thread_incoming s g"
  by(auto simp add:CreateActiveThread_def SetError_NC_IPC)

lemma CreateActiveThread_C_IPC:
"(CreateActiveThread_Cond SysConf s gno space scheduler pager)  \<longrightarrow>
 thread_ipc_partner (CreateActiveThread SysConf s gno space scheduler pager) gno = Some (Global pager) \<and>
 thread_ipc_timeout (CreateActiveThread SysConf s gno space scheduler pager) gno = Some eInfiniteTimeout \<and>
 thread_incoming (CreateActiveThread SysConf s gno space scheduler pager) gno = Some []"
  by(auto simp add:CreateActiveThread_def SetError_NC_IPC)

subsection \<open>Scheduling\<close>
lemma CreateActiveThread_NC_Scheduling:
"wait_queuing (CreateActiveThread SysConf s gno space scheduler pager) = wait_queuing s \<and>
 ready_queuing (CreateActiveThread SysConf s gno space scheduler pager) = ready_queuing s \<and>
 current_timeslice (CreateActiveThread SysConf s gno space scheduler pager) = current_timeslice s"
  by(auto simp add:CreateActiveThread_def SetError_NC_Scheduling)

subsection \<open>memory\<close>
lemma CreateActiveThread_direct_eq:"(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_direct_eq)
  unfolding direct_path_def 
  by auto

lemma CreateActiveThread_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using CreateActiveThread_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using CreateActiveThread_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma CreateActiveThread_tran:"(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using CreateActiveThread_direct_eq tran_path.intros CreateActiveThread_tran1
  by auto

lemma CreateActiveThread_rtran:"(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using CreateActiveThread_tran rtran_tran
  by auto

lemma CreateActiveThread_valid_vpage:
"(CreateActiveThread SysConf s gno space scheduler pager) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using CreateActiveThread_direct_eq valid_page_def
  by auto

lemma CreateActiveThread_valid_rpage:"(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma CreateActiveThread_valid:"(CreateActiveThread SysConf s gno space scheduler pager)\<turnstile> x = s\<turnstile>x"
  using CreateActiveThread_valid_vpage CreateActiveThread_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

section\<open>DeleteThread\<close>

thm DeleteThread_def[no_vars]
definition "delete_temp1 s gno = (if gno \<in> active_threads s
               then let s1 = dequeue_ready s gno
                    in (if isSending (the (thread_state s gno)) \<or> 
                           isReceiving (the (thread_state s gno))
                        then Unwind s1 gno
                        else s1)
               else s)"

definition "delete_temp2 s2 gno =
(let space = the (thread_space s2 gno)
in
         (if the (space_threads s2 space) = {gno} 
          then DeleteAddressSpace s2 space
          else s2\<lparr>space_threads := space_threads s2(space \<mapsto>
                         the (space_threads s2 space) - {gno})\<rparr>))"

definition "delete_temp3 s4 gno = 
(s4\<lparr>threads := threads s4 - {gno}, active_threads := active_threads s4 - {gno},
               thread_space := (thread_space s4)(gno := None),
               thread_scheduler := (thread_scheduler s4)(gno := None),
               thread_state := (thread_state s4)(gno := None),
               thread_pager := (thread_pager s4)(gno := None),
               thread_handler := (thread_handler s4)(gno := None),
               thread_message := (thread_message s4)(gno := None),
               thread_rcvWindow := (thread_rcvWindow s4)(gno := None),
               thread_error := (thread_error s4)(gno := None),
               thread_priority := (thread_priority s4)(gno := None),
               thread_total_quantum := (thread_total_quantum s4)(gno := None),
               thread_timeslice_length := (thread_timeslice_length s4)(gno := None),
               thread_current_timeslice := (thread_current_timeslice s4)(gno := None),
               thread_ipc_partner := (thread_ipc_partner s4)(gno := None),
               thread_ipc_timeout := (thread_ipc_timeout s4)(gno := None),
               thread_incoming := (thread_incoming s4)(gno := None)\<rparr>)"

lemma DeleteThread_eq:"DeleteThread s gno = (if DeleteThread_Cond s gno 
 then SetError (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) 
(current_thread (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno)) eNoError
 else s)"
  unfolding DeleteThread_def Let_def delete_temp3_def delete_temp2_def delete_temp1_def
  by simp

subsection\<open>user\<close>
lemma DeleteThread_NC_User_Cond:
"\<not>DeleteThread_Cond s gno \<longrightarrow>
 thread_pager (DeleteThread s gno) = thread_pager s \<and>
 thread_handler (DeleteThread s gno) = thread_handler s \<and>
 thread_message (DeleteThread s gno) = thread_message s \<and>
 thread_rcvWindow (DeleteThread s gno) = thread_rcvWindow s"
  by(auto simp:DeleteThread_def)

lemma DeleteThread_NC_User_Other:
"gno1 \<noteq> gno \<longrightarrow>
 thread_pager (DeleteThread s gno) gno1 = thread_pager s gno1 \<and>
 thread_handler (DeleteThread s gno) gno1 = thread_handler s gno1 \<and>
 thread_message (DeleteThread s gno) gno1 = thread_message s gno1 \<and>
 thread_rcvWindow (DeleteThread s gno) gno1 = thread_rcvWindow s gno1"
  unfolding DeleteThread_def Let_def dequeue_ready_def SetError_def SetThreadError_def        
  using DeleteAddressSpace_NC_User Unwind_NC_User
  by auto

lemma DeleteThread_C_User:
"DeleteThread_Cond s gno \<longrightarrow>
 thread_pager (DeleteThread s gno) gno = None \<and>
 thread_handler (DeleteThread s gno) gno = None \<and>
 thread_message (DeleteThread s gno) gno = None \<and>
 thread_rcvWindow (DeleteThread s gno) gno = None \<and>
 thread_error (DeleteThread s gno) gno = None"
  unfolding DeleteThread_def Let_def dequeue_ready_def SetError_def SetThreadError_def        
  using DeleteAddressSpace_NC_User Unwind_NC_User
  by auto

subsection\<open>current\<close>
lemma DeleteThread_NC_Current:
"current_thread (DeleteThread s gno) = current_thread s \<and>
 current_time (DeleteThread s gno) = current_time s"
  unfolding DeleteThread_def dequeue_ready_def Let_def SetError_def SetThreadError_def        
  using DeleteAddressSpace_NC_Current Unwind_NC_Current
  by auto

subsection \<open>thread\<close>
section\<open>SetScheduler\<close>
subsection\<open>user\<close>
lemma SetScheduler_NC_User:
"thread_pager (SetScheduler s gno scheduler) = thread_pager s \<and>
 thread_handler (SetScheduler s gno scheduler) = thread_handler s \<and>
 thread_message (SetScheduler s gno scheduler) = thread_message s \<and>
 thread_rcvWindow (SetScheduler s gno scheduler) = thread_rcvWindow s"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def SetError_def SetThreadError_def
  by auto

subsection\<open>current\<close>
lemma SetScheduler_NC_Current:
"current_thread (SetScheduler s gno scheduler) = current_thread s \<and>
 current_time (SetScheduler s gno scheduler) = current_time s"
  by(auto simp add:SetScheduler_def SetThreadScheduler_def SetError_NC_Current)

subsection \<open>thread\<close>
lemma SetScheduler_NC_Thread:
"threads (SetScheduler s gno scheduler) = threads s \<and>
 active_threads (SetScheduler s gno scheduler) = active_threads s \<and>
 thread_space (SetScheduler s gno scheduler) = thread_space s \<and>
 thread_state (SetScheduler s gno scheduler) = thread_state s \<and>
 thread_priority (SetScheduler s gno scheduler) = thread_priority s \<and>
 thread_total_quantum (SetScheduler s gno scheduler) = thread_total_quantum s \<and>
 thread_timeslice_length (SetScheduler s gno scheduler) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetScheduler s gno scheduler) = thread_current_timeslice s"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  using SetError_NC_Thread
  by auto

subsection \<open>space\<close>
lemma SetScheduler_NC_Space:
"spaces (SetScheduler s gno scheduler) = spaces s \<and>
 initialised_spaces (SetScheduler s gno scheduler) = initialised_spaces s \<and>
 space_threads (SetScheduler s gno scheduler) = space_threads s \<and>
 space_mapping (SetScheduler s gno scheduler) = space_mapping s"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  using SetError_NC_Space
  by (auto simp add:spaces_def)

subsection \<open>IPC\<close>
lemma SetScheduler_NC_IPC:
"thread_ipc_partner (SetScheduler s gno scheduler) = thread_ipc_partner s \<and>
 thread_ipc_timeout (SetScheduler s gno scheduler) = thread_ipc_timeout s \<and>
 thread_incoming (SetScheduler s gno scheduler) =  thread_incoming s"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  using SetError_NC_IPC
  by auto

subsection \<open>Scheduling\<close>
lemma SetScheduler_NC_Scheduling:
"wait_queuing (SetScheduler s gno scheduler) = wait_queuing s \<and>
 ready_queuing (SetScheduler s gno scheduler) = ready_queuing s \<and>
 current_timeslice (SetScheduler s gno scheduler) = current_timeslice s"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  using SetError_NC_Scheduling
  by auto

subsection \<open>memory\<close>
lemma SetScheduler_direct_eq:"(SetScheduler s gno scheduler)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  using SetError_direct_eq
  by(auto simp add:direct_path_def)

lemma SetScheduler_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetScheduler s gno scheduler)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetScheduler s gno scheduler)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetScheduler_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(SetScheduler s gno scheduler)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetScheduler s gno scheduler)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetScheduler_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed

lemma SetScheduler_tran:"(SetScheduler s gno scheduler)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetScheduler_direct_eq tran_path.intros SetScheduler_tran1
  by auto

lemma SetScheduler_rtran:"(SetScheduler s gno scheduler)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetScheduler_tran rtran_tran
  by auto

lemma SetScheduler_valid_vpage:"(SetScheduler s gno scheduler) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetScheduler_direct_eq valid_page_def
  by auto

lemma SetScheduler_valid_rpage:"(SetScheduler s gno scheduler)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetScheduler_valid:"(SetScheduler s gno scheduler)\<turnstile> x = s\<turnstile>x"
  using SetScheduler_valid_vpage SetScheduler_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma SetScheduler_NC_Perms:"\<forall>sp v_page. get_perms (SetScheduler s gno scheduler) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def SetScheduler_def SetThreadScheduler_def
SetError_def SetThreadError_def 
  by auto

section\<open>SetPager\<close>
subsection\<open>user\<close>
lemma SetPager_NC_User:
"thread_handler (SetPager s gno pager) = thread_handler s \<and>
 thread_message (SetPager s gno pager) = thread_message s \<and>
 thread_rcvWindow (SetPager s gno pager) = thread_rcvWindow s"
  unfolding SetPager_def SetThreadPager_def Let_def SetError_def SetThreadError_def
  by auto

subsection\<open>current\<close>
lemma SetPager_NC_Current:
"current_thread (SetPager s gno pager) = current_thread s \<and>
 current_time (SetPager s gno pager) = current_time s"
  unfolding SetPager_def SetThreadPager_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>thread\<close>
lemma SetPager_NC_Thread:
"threads (SetPager s gno pager) = threads s \<and>
 active_threads (SetPager s gno pager) = active_threads s \<and>
 thread_space (SetPager s gno pager) = thread_space s \<and>
 thread_scheduler (SetPager s gno pager) = thread_scheduler s \<and>
 thread_state (SetPager s gno pager) = thread_state s \<and>
 thread_priority (SetPager s gno pager) = thread_priority s \<and>
 thread_total_quantum (SetPager s gno pager) = thread_total_quantum s \<and>
 thread_timeslice_length (SetPager s gno pager) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetPager s gno pager) = thread_current_timeslice s"
  unfolding SetPager_def SetThreadPager_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>space\<close>
lemma SetPager_NC_Space:
"spaces (SetPager s gno pager) = spaces s \<and>
 initialised_spaces (SetPager s gno pager) = initialised_spaces s \<and>
 space_threads (SetPager s gno pager) = space_threads s \<and>
 space_mapping (SetPager s gno pager) = space_mapping s"
  unfolding SetPager_def SetThreadPager_def Let_def SetError_def SetThreadError_def
  by (auto simp:spaces_def)

subsection \<open>IPC\<close>
lemma SetPager_NC_IPC:
"thread_ipc_partner (SetPager s gno pager) = thread_ipc_partner s \<and>
 thread_ipc_timeout (SetPager s gno pager) = thread_ipc_timeout s \<and>
 thread_incoming (SetPager s gno pager) =  thread_incoming s"
  unfolding SetPager_def SetThreadPager_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>Scheduling\<close>
lemma SetPager_NC_Scheduling:
"wait_queuing (SetPager s gno pager) = wait_queuing s \<and>
 ready_queuing (SetPager s gno pager) = ready_queuing s \<and>
 current_timeslice (SetPager s gno pager) = current_timeslice s"
  unfolding SetPager_def SetThreadPager_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>memory\<close>
lemma SetPager_direct_eq:"(SetPager s gno pager)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding SetPager_def SetThreadPager_def Let_def
  using SetError_direct_eq
  by(auto simp add:direct_path_def)

lemma SetPager_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetPager s gno pager)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetPager s gno pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetPager_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(SetPager s gno pager)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetPager s gno pager)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetPager_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetPager_tran:"(SetPager s gno pager)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetPager_direct_eq tran_path.intros SetPager_tran1
  by auto

lemma SetPager_rtran:"(SetPager s gno pager)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetPager_tran rtran_tran
  by auto

lemma SetPager_valid_vpage:"(SetPager s gno pager) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetPager_direct_eq valid_page_def
  by auto

lemma SetPager_valid_rpage:"(SetPager s gno pager)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetPager_valid:"(SetPager s gno pager)\<turnstile> x = s\<turnstile>x"
  using SetPager_valid_vpage SetPager_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma SetPager_NC_Perms:"\<forall>sp v_page. get_perms (SetPager s gno pager) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def SetPager_def SetThreadPager_def
    SetError_def SetThreadError_def 
  by auto

section\<open>SetState\<close>
subsection\<open>user\<close>
lemma SetState_NC_User:
"thread_pager (SetState s gno state) = thread_pager s \<and>
 thread_handler (SetState s gno state) = thread_handler s \<and>
 thread_message (SetState s gno state) = thread_message s \<and>
 thread_rcvWindow (SetState s gno state) = thread_rcvWindow s"
  unfolding SetState_def SetThreadState_def Let_def SetError_def SetThreadError_def
  by auto

subsection\<open>current\<close>
lemma SetState_NC_Current:
"current_thread (SetState s gno state) = current_thread s \<and>
 current_time (SetState s gno state) = current_time s"
  unfolding SetState_def SetThreadState_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>thread\<close>
lemma SetState_NC_Thread:
"threads (SetState s gno state) = threads s \<and>
 active_threads (SetState s gno state) = active_threads s \<and>
 thread_space (SetState s gno state) = thread_space s \<and>
 thread_scheduler (SetState s gno state) = thread_scheduler s \<and>
 thread_priority (SetState s gno state) = thread_priority s \<and>
 thread_total_quantum (SetState s gno state) = thread_total_quantum s \<and>
 thread_timeslice_length (SetState s gno state) = thread_timeslice_length s \<and>
 thread_current_timeslice (SetState s gno state) = thread_current_timeslice s"
  unfolding SetState_def SetThreadState_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>space\<close>
lemma SetState_NC_Space:
"spaces (SetState s gno state) = spaces s \<and>
 initialised_spaces (SetState s gno state) = initialised_spaces s \<and>
 space_threads (SetState s gno state) = space_threads s \<and>
 space_mapping (SetState s gno state) = space_mapping s"
  unfolding SetState_def SetThreadState_def Let_def SetError_def SetThreadError_def
  by (auto simp:spaces_def)

subsection \<open>IPC\<close>
lemma SetState_NC_IPC:
"thread_ipc_partner (SetState s gno state) = thread_ipc_partner s \<and>
 thread_ipc_timeout (SetState s gno state) = thread_ipc_timeout s \<and>
 thread_incoming (SetState s gno state) =  thread_incoming s"
  unfolding SetState_def SetThreadState_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>Scheduling\<close>
lemma SetState_NC_Scheduling:
"wait_queuing (SetState s gno state) = wait_queuing s \<and>
 ready_queuing (SetState s gno state) = ready_queuing s \<and>
 current_timeslice (SetState s gno state) = current_timeslice s"
  unfolding SetState_def SetThreadState_def Let_def SetError_def SetThreadError_def
  by auto

subsection \<open>memory\<close>
lemma SetState_direct_eq:"(SetState s gno state)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding SetState_def SetThreadState_def Let_def
  using SetError_direct_eq
  by(auto simp add:direct_path_def)

lemma SetState_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (SetState s gno state)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(SetState s gno state)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetState_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(SetState s gno state)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(SetState s gno state)\<turnstile>x\<leadsto>\<^sup>1y"
    using SetState_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma SetState_tran:"(SetState s gno state)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using SetState_direct_eq tran_path.intros SetState_tran1
  by auto

lemma SetState_rtran:"(SetState s gno state)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using SetState_tran rtran_tran
  by auto

lemma SetState_valid_vpage:"(SetState s gno state) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using SetState_direct_eq valid_page_def
  by auto

lemma SetState_valid_rpage:"(SetState s gno state)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma SetState_valid:"(SetState s gno state)\<turnstile> x = s\<turnstile>x"
  using SetState_valid_vpage SetState_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma SetState_NC_Perms:"\<forall>sp v_page. get_perms (SetState s gno state) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def SetState_def SetThreadState_def
SetError_def SetThreadError_def 
  by auto

section\<open>Migrate\<close>
subsection\<open>user\<close>
lemma Migrate_NC_User:
"thread_pager (Migrate SysConf s gno space) = thread_pager s \<and>
 thread_handler (Migrate SysConf s gno space) = thread_handler s \<and>
 thread_message (Migrate SysConf s gno space) = thread_message s \<and>
 thread_rcvWindow (Migrate SysConf s gno space) = thread_rcvWindow s"
  unfolding Migrate_def Let_def SetError_def SetThreadError_def
  using SetError_NC_User DeleteAddressSpace_NC_User
  by auto

subsection\<open>current\<close>
lemma Migrate_NC_Current:
"current_thread (Migrate SysConf s gno space) = current_thread s \<and>
 current_time (Migrate SysConf s gno space) = current_time s"
  unfolding Migrate_def Let_def
  using SetError_NC_Current DeleteAddressSpace_NC_Current
  by auto

subsection \<open>thread\<close>
lemma Migrate_NC_Thread:
"threads (Migrate SysConf s gno space) = threads s \<and>
 active_threads (Migrate SysConf s gno space) = active_threads s \<and>
 thread_scheduler (Migrate SysConf s gno space) = thread_scheduler s \<and>
 thread_state (Migrate SysConf s gno space) = thread_state s \<and>
 thread_priority (Migrate SysConf s gno space) = thread_priority s \<and>
 thread_total_quantum (Migrate SysConf s gno space) = thread_total_quantum s \<and>
 thread_timeslice_length (Migrate SysConf s gno space) = thread_timeslice_length s \<and>
 thread_current_timeslice (Migrate SysConf s gno space) = thread_current_timeslice s"
  unfolding Migrate_def Let_def
  using SetError_NC_Thread DeleteAddressSpace_NC_Thread
  by auto

lemma Migrate_C_Thread:
"Migrate_Cond SysConf s gno space \<and> the (space_threads s (the (thread_space s gno))) = {gno} \<Longrightarrow>
thread_space (Migrate SysConf s gno space) = thread_space s (gno \<mapsto> space)"
  unfolding Migrate_def
  apply simp
  unfolding Let_def
  apply simp
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_Current
    SetError_NC_Thread
  by auto

thm Migrate_def[no_vars]

subsection \<open>space\<close>
lemma Migrate_NC_Space:
"Migrate_Cond SysConf s gno space \<and> the (space_threads s (the (thread_space s gno))) \<noteq> {gno} \<Longrightarrow>
spaces (Migrate SysConf s gno space) = spaces s \<and>
initialised_spaces (Migrate SysConf s gno space) = initialised_spaces s \<and> 
space_mapping (Migrate SysConf s gno space) = space_mapping s"
  unfolding Migrate_def
  apply simp
  unfolding Let_def spaces_def
  apply simp
  using SetError_NC_Space[unfolded spaces_def]
  by auto

thm DeleteAddressSpace_C_Space[no_vars]
(*
lemma Migrate_C_Space11:
"Migrate_Cond SysConf s gno space \<and> the (space_threads s (the (thread_space s gno))) = {gno} \<Longrightarrow>
spaces (Migrate SysConf s gno space) = spaces s - {(the (thread_space s gno))} \<and> 
space_mapping (Migrate SysConf s gno space) (the (thread_space s gno)) = None \<and>
space_threads (Migrate SysConf s gno space) (the (thread_space s gno)) = None"
  unfolding Migrate_def Let_def
  apply (simp add:SetError_NC_Space)
  apply rule
  subgoal
    using Migrate_Cond_def by simp
  apply rule
  apply rule
  subgoal
    apply auto

    sorry
  sorry

lemma Migrate_C_Space12:
"Migrate_Cond SysConf s gno space \<and> the (space_threads s (the (thread_space s gno))) = {gno} \<Longrightarrow>
space_mapping (Migrate SysConf s gno space) space = space_mapping s space \<and>
space_threads (Migrate SysConf s gno space) space = Some (the (space_threads s space) \<union> {gno})"
  apply rule
  subgoal
    unfolding Migrate_def Let_def
    using SetError_NC_Space DeleteAddressSpace_NC_Space
    apply auto
    sorry
  sorry
*)
lemma Migrate_C_Space2:
"Migrate_Cond SysConf s gno space \<and> the (space_threads s (the (thread_space s gno))) \<noteq> {gno} \<Longrightarrow>
space_threads (Migrate SysConf s gno space) = 
space_threads s(space \<mapsto> the (space_threads s space) \<union> {gno}, 
                (the (thread_space s gno)) \<mapsto> the (space_threads s (the (thread_space s gno))) - {gno})"
  unfolding Migrate_def
  apply simp
  unfolding Let_def
  apply simp
  using SetError_NC_Space
  by auto

subsection \<open>IPC\<close>
lemma Migrate_NC_IPC:
"thread_ipc_partner (Migrate SysConf s gno space) = thread_ipc_partner s \<and>
 thread_ipc_timeout (Migrate SysConf s gno space) = thread_ipc_timeout s \<and>
 thread_incoming (Migrate SysConf s gno space) =  thread_incoming s"
  unfolding Migrate_def Let_def
  using SetError_NC_IPC DeleteAddressSpace_NC_IPC
  by auto

subsection \<open>Scheduling\<close>
lemma Migrate_NC_Scheduling:
"wait_queuing (Migrate SysConf s gno space) = wait_queuing s \<and>
 ready_queuing (Migrate SysConf s gno space) = ready_queuing s \<and>
 current_timeslice (Migrate SysConf s gno space) = current_timeslice s"
  unfolding Migrate_def Let_def
  using SetError_NC_Scheduling DeleteAddressSpace_NC_Scheduling
  by auto

section\<open>ActivateInterrupt\<close>
subsection\<open>user\<close>
lemma ActivateInterrupt_NC_User:
"thread_pager (ActivateInterrupt SysConf s gno handler) = thread_pager s \<and>
 thread_handler (ActivateInterrupt SysConf s gno handler) = thread_handler s \<and>
 thread_message (ActivateInterrupt SysConf s gno handler) = thread_message s \<and>
 thread_rcvWindow (ActivateInterrupt SysConf s gno handler) = thread_rcvWindow s"
  unfolding ActivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection\<open>current\<close>
lemma ActivateInterrupt_NC_Current:
"current_thread (ActivateInterrupt SysConf s gno handler) = current_thread s \<and>
 current_time (ActivateInterrupt SysConf s gno handler) = current_time s"
  unfolding ActivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection \<open>thread\<close>
lemma ActivateInterrupt_NC_Thread:
"threads (ActivateInterrupt SysConf s gno handler) = threads s \<and>
 active_threads (ActivateInterrupt SysConf s gno handler) = active_threads s \<and>
 thread_space (ActivateInterrupt SysConf s gno handler) = thread_space s \<and>
 thread_priority (ActivateInterrupt SysConf s gno handler) = thread_priority s \<and>
 thread_total_quantum (ActivateInterrupt SysConf s gno handler) = thread_total_quantum s \<and>
 thread_timeslice_length (ActivateInterrupt SysConf s gno handler) = thread_timeslice_length s \<and>
 thread_current_timeslice (ActivateInterrupt SysConf s gno handler) = thread_current_timeslice s"
  unfolding ActivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection \<open>space\<close>
lemma ActivateInterrupt_NC_Space:
"spaces (ActivateInterrupt SysConf s gno handler) = spaces s \<and>
 initialised_spaces (ActivateInterrupt SysConf s gno handler) = initialised_spaces s \<and>
 space_threads (ActivateInterrupt SysConf s gno handler) = space_threads s \<and>
 space_mapping (ActivateInterrupt SysConf s gno handler) = space_mapping s"
  unfolding ActivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by (auto simp:spaces_def)

subsection \<open>IPC\<close>
lemma ActivateInterrupt_NC_IPC:
"thread_ipc_partner (ActivateInterrupt SysConf s gno handler) = thread_ipc_partner s \<and>
 thread_ipc_timeout (ActivateInterrupt SysConf s gno handler) = thread_ipc_timeout s \<and>
 thread_incoming (ActivateInterrupt SysConf s gno handler) =  thread_incoming s"
  unfolding ActivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection \<open>Scheduling\<close>
lemma ActivateInterrupt_NC_Scheduling:
"wait_queuing (ActivateInterrupt SysConf s gno handler) = wait_queuing s \<and>
 ready_queuing (ActivateInterrupt SysConf s gno handler) = ready_queuing s \<and>
 current_timeslice (ActivateInterrupt SysConf s gno handler) = current_timeslice s"
  unfolding ActivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection\<open>memory\<close>
lemma ActivateInterrupt_direct_eq:"(ActivateInterrupt SysConf s gno handler)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  using SetError_direct_eq
  by(auto simp add:direct_path_def)

lemma ActivateInterrupt_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (ActivateInterrupt SysConf s gno handler)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(ActivateInterrupt SysConf s gno handler)\<turnstile>x\<leadsto>\<^sup>1y"
    using ActivateInterrupt_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(ActivateInterrupt SysConf s gno handler)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(ActivateInterrupt SysConf s gno handler)\<turnstile>x\<leadsto>\<^sup>1y"
    using ActivateInterrupt_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma ActivateInterrupt_tran:"(ActivateInterrupt SysConf s gno handler)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using ActivateInterrupt_direct_eq tran_path.intros ActivateInterrupt_tran1
  by auto

lemma ActivateInterrupt_rtran:"(ActivateInterrupt SysConf s gno handler)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using ActivateInterrupt_tran rtran_tran
  by auto

lemma ActivateInterrupt_valid_vpage:"(ActivateInterrupt SysConf s gno handler) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using ActivateInterrupt_direct_eq valid_page_def
  by auto

lemma ActivateInterrupt_valid_rpage:"(ActivateInterrupt SysConf s gno handler)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma ActivateInterrupt_valid:"(ActivateInterrupt SysConf s gno handler)\<turnstile> x = s\<turnstile>x"
  using ActivateInterrupt_valid_vpage ActivateInterrupt_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma ActivateInterrupt_NC_Perms:"\<forall>sp v_page. get_perms (ActivateInterrupt SysConf s gno handler) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def
SetError_def SetThreadError_def 
  by auto

section\<open>DeactivateInterrupt\<close>
subsection\<open>user\<close>
lemma DeactivateInterrupt_NC_User:
"thread_pager (DeactivateInterrupt s gno) = thread_pager s \<and>
 thread_handler (DeactivateInterrupt s gno) = thread_handler s \<and>
 thread_message (DeactivateInterrupt s gno) = thread_message s \<and>
 thread_rcvWindow (DeactivateInterrupt s gno) = thread_rcvWindow s"
  unfolding DeactivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection\<open>current\<close>
lemma DeactivateInterrupt_NC_Current:
"current_thread (DeactivateInterrupt s gno) = current_thread s \<and>
 current_time (DeactivateInterrupt s gno) = current_time s"
  unfolding DeactivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection \<open>thread\<close>
lemma DeactivateInterrupt_NC_Thread:
"threads (DeactivateInterrupt s gno) = threads s \<and>
 active_threads (DeactivateInterrupt s gno) = active_threads s \<and>
 thread_space (DeactivateInterrupt s gno) = thread_space s \<and>
 thread_priority (DeactivateInterrupt s gno) = thread_priority s \<and>
 thread_total_quantum (DeactivateInterrupt s gno) = thread_total_quantum s \<and>
 thread_timeslice_length (DeactivateInterrupt s gno) = thread_timeslice_length s \<and>
 thread_current_timeslice (DeactivateInterrupt s gno) = thread_current_timeslice s"
  unfolding DeactivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection \<open>space\<close>
lemma DeactivateInterrupt_NC_Space:
"spaces (DeactivateInterrupt s gno) = spaces s \<and>
 initialised_spaces (DeactivateInterrupt s gno) = initialised_spaces s \<and>
 space_threads (DeactivateInterrupt s gno) = space_threads s \<and>
 space_mapping (DeactivateInterrupt s gno) = space_mapping s"
  unfolding DeactivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by (auto simp:spaces_def)

subsection \<open>IPC\<close>
lemma DeactivateInterrupt_NC_IPC:
"thread_ipc_partner (DeactivateInterrupt s gno) = thread_ipc_partner s \<and>
 thread_ipc_timeout (DeactivateInterrupt s gno) = thread_ipc_timeout s \<and>
 thread_incoming (DeactivateInterrupt s gno) =  thread_incoming s"
  unfolding DeactivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection \<open>Scheduling\<close>
lemma DeactivateInterrupt_NC_Scheduling:
"wait_queuing (DeactivateInterrupt s gno) = wait_queuing s \<and>
 ready_queuing (DeactivateInterrupt s gno) = ready_queuing s \<and>
 current_timeslice (DeactivateInterrupt s gno) = current_timeslice s"
  unfolding DeactivateInterrupt_def Let_def SetError_def SetThreadError_def
    SetThreadScheduler_def SetThreadState_def
  by auto

subsection\<open>memory\<close>
lemma DeactivateInterrupt_direct_eq:"(DeactivateInterrupt s gno)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  using SetError_direct_eq
  by(auto simp add:direct_path_def)

lemma DeactivateInterrupt_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (DeactivateInterrupt s gno)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(DeactivateInterrupt s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using DeactivateInterrupt_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
    have h3: "(DeactivateInterrupt s gno)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(DeactivateInterrupt s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using DeactivateInterrupt_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma DeactivateInterrupt_tran:"(DeactivateInterrupt s gno)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using DeactivateInterrupt_direct_eq tran_path.intros DeactivateInterrupt_tran1
  by auto

lemma DeactivateInterrupt_rtran:"(DeactivateInterrupt s gno)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using DeactivateInterrupt_tran rtran_tran
  by auto

lemma DeactivateInterrupt_valid_vpage:"(DeactivateInterrupt s gno) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using DeactivateInterrupt_direct_eq valid_page_def
  by auto

lemma DeactivateInterrupt_valid_rpage:"(DeactivateInterrupt s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma DeactivateInterrupt_valid:"(DeactivateInterrupt s gno)\<turnstile> x = s\<turnstile>x"
  using DeactivateInterrupt_valid_vpage DeactivateInterrupt_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma DeactivateInterrupt_NC_Perms:"\<forall>sp v_page. get_perms (DeactivateInterrupt s gno) sp v_page =
get_perms s sp v_page"
  unfolding get_perms_def DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def
SetError_def SetThreadError_def 
  by auto

section\<open>inv\<close>

lemma SetThreadPriority_cons:"GetCurrentSpace (SetThreadPriority s t prio) = GetCurrentSpace s"
  unfolding SetThreadPriority_def
  by (auto simp add: GetCurrentSpace_def  GetThreadSpace_def)

lemma SetThreadPriority_mapping:"space_mapping (SetThreadPriority s t prio) = space_mapping s"
  unfolding SetThreadPriority_def
  by auto

lemma SetThreadPriority_threads:"space_threads (SetThreadPriority s t prio) = space_threads s"
  unfolding SetThreadPriority_def
  by auto

lemma SetThreadQuantum_cons:"GetCurrentSpace (SetThreadQuantum s t prio) = GetCurrentSpace s"
  unfolding SetThreadQuantum_def
  by (auto simp add: GetCurrentSpace_def  GetThreadSpace_def)

lemma SetThreadQuantum_mapping:"space_mapping (SetThreadQuantum s t prio) = space_mapping s"
  unfolding SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_threads:"space_threads (SetThreadQuantum s t prio) = space_threads s"
  unfolding SetThreadQuantum_def
  by auto

lemma SetThreadTimeslice_cons:"GetCurrentSpace (SetThreadTimeslice s t prio) = GetCurrentSpace s"
  unfolding SetThreadTimeslice_def
  by (auto simp add: GetCurrentSpace_def  GetThreadSpace_def)

lemma SetThreadTimeslice_mapping:"space_mapping (SetThreadTimeslice s t prio) = space_mapping s"
  unfolding SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_threads:"space_threads (SetThreadTimeslice s t prio) = space_threads s"
  unfolding SetThreadTimeslice_def
  by auto

  (*20*)
end