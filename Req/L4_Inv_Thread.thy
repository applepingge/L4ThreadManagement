theory L4_Inv_Thread
  imports L4_Inv_Space
begin

section\<open>SetThreadPager\<close>
subsection\<open>Current\<close>
lemma SetThreadPager_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetThreadPager s gno pager)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetThreadPager s gno pager)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetThreadPager s gno pager)"
  using SetThreadPager_Inv_Current_Thread_In_Active SetThreadPager_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetThreadPager_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetThreadPager s gno pager)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetThreadPager_tran)

lemma SetThreadPager_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetThreadPager s gno pager)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetThreadPager_rtran SetThreadPager_valid)

lemma SetThreadPager_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetThreadPager s gno pager)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetThreadPager_valid SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetThreadPager s gno pager)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  apply (auto simp:SetThreadPager_direct_eq)
  unfolding SetThreadPager_def
  by (simp add: subset_iff)

lemma SetThreadPager_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetThreadPager s gno pager)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetThreadPager_def spaces_def)

lemma SetThreadPager_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetThreadPager s gno pager)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetThreadPager_def spaces_def)

lemma SetThreadPager_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetThreadPager s gno pager)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetThreadPager_def spaces_def)

lemma SetThreadPager_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetThreadPager s gno pager)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetThreadPager_valid)

lemma SetThreadPager_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetThreadPager s gno pager)"
  unfolding Inv_Space_def
  using SetThreadPager_Inv_Space_HasNot_Loop SetThreadPager_Inv_Space_Valid_Has_Real
   SetThreadPager_Inv_Space_Perms_IsNot_Empty SetThreadPager_Inv_Space_Spaces_In_Config 
   SetThreadPager_Inv_Space_InitialSpaces_In_Spaces SetThreadPager_Inv_Space_Perms_Subset
   SetThreadPager_Inv_Space_Spaces_IsNot_None SetThreadPager_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetThreadPager_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetThreadPager s gno pager)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetThreadPager s gno pager)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetThreadPager s gno pager)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetThreadPager s gno pager)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetThreadPager s gno pager)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetThreadPager s gno pager)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetThreadPager s gno pager)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_NThreads_Is_None:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (SetThreadPager s gno pager)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p0
  by (auto simp add: SetThreadPager_def)

lemma SetThreadPager_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetThreadPager s gno pager)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetThreadPager_def)

lemma SetThreadPager_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetThreadPager s gno pager)"
  unfolding SetThreadPager_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetThreadPager_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetThreadPager s gno pager)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetThreadPager_def
  by (auto simp add:spaces_def)

lemma SetThreadPager_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetThreadPager s gno pager)"
  unfolding SetThreadPager_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetThreadPager_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetThreadPager s gno pager)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
      and p2:"gno \<in> active_threads s"
    shows "Inv_NActive_Utcb_Is_None (SetThreadPager s gno pager)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetThreadPager_def p2
  by auto

lemma SetThreadPager_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetThreadPager s gno pager)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
      and p2:"gno \<notin> kIntThreads"
    shows "Inv_IntThreads_Utcb_Is_None (SetThreadPager s gno pager)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def] SetThreadPager_def p2
  by auto

lemma SetThreadPager_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetThreadPager s gno pager)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetThreadPager s gno pager)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetThreadPager s gno pager)"
  using assms unfolding Inv_Sigma0_Space_def SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetThreadPager s gno pager)"
  using assms unfolding Inv_RootServer_Space_def SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetThreadPager s gno pager)"
  using assms unfolding Inv_IntThreads_Space_def SetThreadPager_def
  by auto

lemma SetThreadPager_Inv_Thread:
  assumes p1:"Inv_Thread s" 
    and p2:"gno \<in> active_threads s" 
    and p3:"gno \<notin> kIntThreads"
    and p4:"gno \<in> threads s"
  shows "Inv_Thread (SetThreadPager s gno pager)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p2 p3 p4
    SetThreadPager_Inv_Idle_NotIn_Threads SetThreadPager_Inv_Idle_Space_Is_KernelSpace
    SetThreadPager_Inv_Sigma0_In_Active SetThreadPager_Inv_RootServer_In_Active 
    SetThreadPager_Inv_IntThreads_In_Active 
    SetThreadPager_Inv_Threads_In_Config SetThreadPager_Inv_Active_In_Threads 
    SetThreadPager_Inv_NThreads_Is_None SetThreadPager_Inv_Threads_IsNot_None 
    SetThreadPager_Inv_Threads_Space_Dom
    SetThreadPager_Inv_Threads_Space_In_Spaces SetThreadPager_Inv_Threads_Eq_Space_Threads
    SetThreadPager_Inv_Threads_Sche_In_Threads 
    SetThreadPager_Inv_NActive_Utcb_Is_None SetThreadPager_Inv_Active_Utcb_IsNot_None
    SetThreadPager_Inv_IntThreads_Utcb_Is_None SetThreadPager_Inv_Sigma0_Space
    SetThreadPager_Inv_RootServer_Space SetThreadPager_Inv_IntThreads_Space
    SetThreadPager_Inv_Threads_Partner_In_Threads SetThreadPager_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetThreadPager_Inv:
  assumes p1:"Invariants s"
    and p2:"gno \<in> active_threads s" 
    and p3:"gno \<notin> kIntThreads"
    and p4:"gno \<in> threads s"
    shows "Invariants (SetThreadPager s gno pager)"  
  unfolding Invariants_def
  using p1 p2 p3 p4 Invariants_def SetThreadPager_Inv_Current SetThreadPager_Inv_Space 
    SetThreadPager_Inv_Thread
  by auto

section\<open>SetThreadState\<close>
subsection\<open>Current\<close>
lemma SetThreadState_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetThreadState s gno state)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetThreadState s gno state)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetThreadState s gno state)"
  using SetThreadState_Inv_Current_Thread_In_Active SetThreadState_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetThreadState_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetThreadState s gno state)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetThreadState_tran)

lemma SetThreadState_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetThreadState s gno state)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetThreadState_rtran SetThreadState_valid)

lemma SetThreadState_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetThreadState s gno state)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetThreadState_valid SetThreadState_def
  by auto

lemma SetThreadState_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetThreadState s gno state)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  by (auto simp: SetThreadState_direct_eq SetThreadState_NC_Space)

lemma SetThreadState_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetThreadState s gno state)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetThreadState_def spaces_def)

lemma SetThreadState_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetThreadState s gno state)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetThreadState_def spaces_def)

lemma SetThreadState_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetThreadState s gno state)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetThreadState_def spaces_def)

lemma SetThreadState_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetThreadState s gno state)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetThreadState_valid)

lemma SetThreadState_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetThreadState s gno state)"
  unfolding Inv_Space_def
  using SetThreadState_Inv_Space_HasNot_Loop SetThreadState_Inv_Space_Valid_Has_Real
   SetThreadState_Inv_Space_Perms_IsNot_Empty SetThreadState_Inv_Space_Spaces_In_Config 
   SetThreadState_Inv_Space_InitialSpaces_In_Spaces SetThreadState_Inv_Space_Perms_Subset
   SetThreadState_Inv_Space_Spaces_IsNot_None SetThreadState_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetThreadState_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetThreadState s gno state)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetThreadState s gno state)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetThreadState s gno state)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetThreadState s gno state)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetThreadState s gno state)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetThreadState s gno state)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetThreadState s gno state)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_NThreads_Is_None:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (SetThreadState s gno state)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p0
  by (auto simp add: SetThreadState_def)

lemma SetThreadState_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetThreadState s gno state)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetThreadState_def)

lemma SetThreadState_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetThreadState s gno val)"
  unfolding SetThreadState_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetThreadState_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetThreadState s gno state)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetThreadState_def
  by (auto simp add:spaces_def)

lemma SetThreadState_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetThreadState s gno state)"
  unfolding SetThreadState_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetThreadState_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetThreadState s gno state)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetThreadState s gno state)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetThreadState s gno state)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetThreadState s gno state)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetThreadState s gno state)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetThreadState s gno state)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetThreadState_def
  by auto

lemma SetThreadState_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetThreadState s gno state)"
  using assms unfolding Inv_Sigma0_Space_def SetThreadState_def
  by auto

lemma SetThreadState_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetThreadState s gno state)"
  using assms unfolding Inv_RootServer_Space_def SetThreadState_def
  by auto

lemma SetThreadState_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetThreadState s gno state)"
  using assms unfolding Inv_IntThreads_Space_def SetThreadState_def
  by auto

lemma SetThreadState_Inv_Thread:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_Thread s"
    shows "Inv_Thread (SetThreadState s gno state)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p0
    SetThreadState_Inv_Idle_NotIn_Threads SetThreadState_Inv_Idle_Space_Is_KernelSpace
    SetThreadState_Inv_Sigma0_In_Active SetThreadState_Inv_RootServer_In_Active 
    SetThreadState_Inv_IntThreads_In_Active 
    SetThreadState_Inv_Threads_In_Config SetThreadState_Inv_Active_In_Threads 
    SetThreadState_Inv_NThreads_Is_None SetThreadState_Inv_Threads_IsNot_None 
    SetThreadState_Inv_Threads_Space_Dom
    SetThreadState_Inv_Threads_Space_In_Spaces SetThreadState_Inv_Threads_Eq_Space_Threads
    SetThreadState_Inv_Threads_Sche_In_Threads 
    SetThreadState_Inv_NActive_Utcb_Is_None SetThreadState_Inv_Active_Utcb_IsNot_None
    SetThreadState_Inv_IntThreads_Utcb_Is_None SetThreadState_Inv_Sigma0_Space
    SetThreadState_Inv_RootServer_Space SetThreadState_Inv_IntThreads_Space
    SetThreadState_Inv_Threads_Partner_In_Threads SetThreadState_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetThreadState_Inv:
  assumes p0:"gno \<in> threads s"
      and p1:"Invariants s"
    shows "Invariants (SetThreadState s gno state)"  
  unfolding Invariants_def
  using p0 p1 Invariants_def SetThreadState_Inv_Current 
    SetThreadState_Inv_Space SetThreadState_Inv_Thread
  by auto

section\<open>SetIpcPartner\<close>
subsection\<open>Current\<close>
lemma SetIpcPartner_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetIpcPartner s gno pa)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetIpcPartner s gno pa)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetIpcPartner s gno pa)"
  using SetIpcPartner_Inv_Current_Thread_In_Active SetIpcPartner_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetIpcPartner_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetIpcPartner s gno pa)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetIpcPartner_tran)

lemma SetIpcPartner_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetIpcPartner s gno pa)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetIpcPartner_rtran SetIpcPartner_valid)

lemma SetIpcPartner_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetIpcPartner s gno pa)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetIpcPartner_valid SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetIpcPartner s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetIpcPartner_direct_eq SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetIpcPartner s gno pa)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetIpcPartner_def spaces_def)

lemma SetIpcPartner_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetIpcPartner s gno pa)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetIpcPartner_def spaces_def)

lemma SetIpcPartner_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetIpcPartner s gno pa)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetIpcPartner_def spaces_def)

lemma SetIpcPartner_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetIpcPartner s gno pa)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetIpcPartner_valid)

lemma SetIpcPartner_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetIpcPartner s gno pa)"
  unfolding Inv_Space_def
  using SetIpcPartner_Inv_Space_HasNot_Loop SetIpcPartner_Inv_Space_Valid_Has_Real
   SetIpcPartner_Inv_Space_Perms_IsNot_Empty SetIpcPartner_Inv_Space_Spaces_In_Config 
   SetIpcPartner_Inv_Space_InitialSpaces_In_Spaces SetIpcPartner_Inv_Space_Perms_Subset
   SetIpcPartner_Inv_Space_Spaces_IsNot_None SetIpcPartner_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetIpcPartner_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetIpcPartner s gno pa)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetIpcPartner s gno pa)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetIpcPartner s gno pa)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetIpcPartner s gno pa)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetIpcPartner s gno pa)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetIpcPartner s gno pa)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetIpcPartner s gno pa)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_NThreads_Is_None:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (SetIpcPartner s gno pa)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p0
  by (auto simp add: SetIpcPartner_def)

lemma SetIpcPartner_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetIpcPartner s gno pa)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetIpcPartner_def)

lemma SetIpcPartner_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetIpcPartner s gno val)"
  unfolding SetIpcPartner_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetIpcPartner_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetIpcPartner s gno pa)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetIpcPartner_def
  by (auto simp:spaces_def)

lemma SetIpcPartner_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetIpcPartner s gno pa)"
  unfolding SetIpcPartner_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetIpcPartner_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetIpcPartner s gno pa)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetIpcPartner s gno pa)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetIpcPartner s gno pa)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetIpcPartner s gno pa)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
      and p1:"(pa \<noteq> NILTHREAD \<and> pa \<noteq> ANYTHREAD \<longrightarrow> 
                              TidToGno pa \<in> threads s)"
    shows "Inv_Threads_Partner_In_Threads (SetIpcPartner s gno pa)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] p1 SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetIpcPartner s gno pa)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetIpcPartner s gno pa)"
  using assms unfolding Inv_Sigma0_Space_def SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetIpcPartner s gno pa)"
  using assms unfolding Inv_RootServer_Space_def SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetIpcPartner s gno pa)"
  using assms unfolding Inv_IntThreads_Space_def SetIpcPartner_def
  by auto

lemma SetIpcPartner_Inv_Thread:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_Thread s"
      and p2:"(pa \<noteq> NILTHREAD \<and> pa \<noteq> ANYTHREAD \<longrightarrow> 
                              TidToGno pa \<in> threads s)"
    shows "Inv_Thread (SetIpcPartner s gno pa)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p0 p2
    SetIpcPartner_Inv_Idle_NotIn_Threads SetIpcPartner_Inv_Idle_Space_Is_KernelSpace
    SetIpcPartner_Inv_Sigma0_In_Active SetIpcPartner_Inv_RootServer_In_Active 
    SetIpcPartner_Inv_IntThreads_In_Active 
    SetIpcPartner_Inv_Threads_In_Config SetIpcPartner_Inv_Active_In_Threads 
    SetIpcPartner_Inv_NThreads_Is_None SetIpcPartner_Inv_Threads_IsNot_None 
    SetIpcPartner_Inv_Threads_Space_Dom
    SetIpcPartner_Inv_Threads_Space_In_Spaces SetIpcPartner_Inv_Threads_Eq_Space_Threads
    SetIpcPartner_Inv_Threads_Sche_In_Threads 
    SetIpcPartner_Inv_NActive_Utcb_Is_None SetIpcPartner_Inv_Active_Utcb_IsNot_None
    SetIpcPartner_Inv_IntThreads_Utcb_Is_None SetIpcPartner_Inv_Sigma0_Space
    SetIpcPartner_Inv_RootServer_Space SetIpcPartner_Inv_IntThreads_Space
    SetIpcPartner_Inv_Threads_Partner_In_Threads SetIpcPartner_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetIpcPartner_Inv:
  assumes p0:"gno \<in> threads s"
      and p1:"Invariants s"
      and p2:"(pa \<noteq> NILTHREAD \<and> pa \<noteq> ANYTHREAD \<longrightarrow> 
                              TidToGno pa \<in> threads s)"
    shows "Invariants (SetIpcPartner s gno pa)"  
  unfolding Invariants_def
  using p0 p1 p2 Invariants_def SetIpcPartner_Inv_Current SetIpcPartner_Inv_Space SetIpcPartner_Inv_Thread
  by auto

section\<open>SetIpcTimeout\<close>
subsection\<open>Current\<close>
lemma SetIpcTimeout_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetIpcTimeout s gno t)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetIpcTimeout s gno t)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetIpcTimeout s gno t)"
  using SetIpcTimeout_Inv_Current_Thread_In_Active SetIpcTimeout_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetIpcTimeout_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetIpcTimeout s gno t)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetIpcTimeout_tran)

lemma SetIpcTimeout_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetIpcTimeout s gno t)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetIpcTimeout_rtran SetIpcTimeout_valid)

lemma SetIpcTimeout_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetIpcTimeout s gno t)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetIpcTimeout_valid SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetIpcTimeout s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetIpcTimeout_direct_eq SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetIpcTimeout s gno t)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetIpcTimeout_def spaces_def)

lemma SetIpcTimeout_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetIpcTimeout s gno t)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetIpcTimeout_def spaces_def)

lemma SetIpcTimeout_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetIpcTimeout s gno t)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetIpcTimeout_def spaces_def)

lemma SetIpcTimeout_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetIpcTimeout s gno t)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetIpcTimeout_valid)

lemma SetIpcTimeout_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetIpcTimeout s gno t)"
  unfolding Inv_Space_def
  using SetIpcTimeout_Inv_Space_HasNot_Loop SetIpcTimeout_Inv_Space_Valid_Has_Real
   SetIpcTimeout_Inv_Space_Perms_IsNot_Empty SetIpcTimeout_Inv_Space_Spaces_In_Config 
   SetIpcTimeout_Inv_Space_InitialSpaces_In_Spaces SetIpcTimeout_Inv_Space_Perms_Subset
   SetIpcTimeout_Inv_Space_Spaces_IsNot_None SetIpcTimeout_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetIpcTimeout_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetIpcTimeout s gno t)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetIpcTimeout s gno t)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetIpcTimeout s gno t)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetIpcTimeout s gno t)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetIpcTimeout s gno t)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetIpcTimeout s gno t)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetIpcTimeout s gno t)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_NThreads_Is_None:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (SetIpcTimeout s gno t)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p0
  by (auto simp add: SetIpcTimeout_def)

lemma SetIpcTimeout_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetIpcTimeout s gno t)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetIpcTimeout_def)

lemma SetIpcTimeout_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetIpcTimeout s gno val)"
  unfolding SetIpcTimeout_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetIpcTimeout_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetIpcTimeout s gno t)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetIpcTimeout_def
  by (auto simp:spaces_def)

lemma SetIpcTimeout_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetIpcTimeout s gno t)"
  unfolding SetIpcTimeout_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetIpcTimeout_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetIpcTimeout s gno t)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetIpcTimeout s gno t)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetIpcTimeout s gno t)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetIpcTimeout s gno t)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetIpcTimeout s gno t)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetIpcTimeout s gno t)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetIpcTimeout s gno pa)"
  using assms unfolding Inv_Sigma0_Space_def SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetIpcTimeout s gno pa)"
  using assms unfolding Inv_RootServer_Space_def SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetIpcTimeout s gno pa)"
  using assms unfolding Inv_IntThreads_Space_def SetIpcTimeout_def
  by auto

lemma SetIpcTimeout_Inv_Thread:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_Thread s"
    shows "Inv_Thread (SetIpcTimeout s gno t)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p0
    SetIpcTimeout_Inv_Idle_NotIn_Threads SetIpcTimeout_Inv_Idle_Space_Is_KernelSpace
    SetIpcTimeout_Inv_Sigma0_In_Active SetIpcTimeout_Inv_RootServer_In_Active 
    SetIpcTimeout_Inv_IntThreads_In_Active 
    SetIpcTimeout_Inv_Threads_In_Config SetIpcTimeout_Inv_Active_In_Threads 
    SetIpcTimeout_Inv_NThreads_Is_None SetIpcTimeout_Inv_Threads_IsNot_None 
    SetIpcTimeout_Inv_Threads_Space_Dom
    SetIpcTimeout_Inv_Threads_Space_In_Spaces SetIpcTimeout_Inv_Threads_Eq_Space_Threads
    SetIpcTimeout_Inv_Threads_Sche_In_Threads 
    SetIpcTimeout_Inv_NActive_Utcb_Is_None SetIpcTimeout_Inv_Active_Utcb_IsNot_None
    SetIpcTimeout_Inv_IntThreads_Utcb_Is_None SetIpcTimeout_Inv_Sigma0_Space
    SetIpcTimeout_Inv_RootServer_Space SetIpcTimeout_Inv_IntThreads_Space
    SetIpcTimeout_Inv_Threads_Partner_In_Threads SetIpcTimeout_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetIpcTimeout_Inv:
  assumes p0:"gno \<in> threads s"
      and p1:"Invariants s"
    shows "Invariants (SetIpcTimeout s gno t)"  
  unfolding Invariants_def
  using p0 p1 Invariants_def SetIpcTimeout_Inv_Current SetIpcTimeout_Inv_Space SetIpcTimeout_Inv_Thread
  by auto

section\<open>SetThreadsIncomingDel\<close>
subsection\<open>Current\<close>
lemma SetThreadsIncomingDel_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetThreadsIncomingDel s gno t)"
  using SetThreadsIncomingDel_Inv_Current_Thread_In_Active SetThreadsIncomingDel_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetThreadsIncomingDel_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetThreadsIncomingDel_tran)

lemma SetThreadsIncomingDel_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetThreadsIncomingDel_rtran SetThreadsIncomingDel_valid)

lemma SetThreadsIncomingDel_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetThreadsIncomingDel_valid SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetThreadsIncomingDel s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetThreadsIncomingDel_direct_eq SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetThreadsIncomingDel_def spaces_def)

lemma SetThreadsIncomingDel_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetThreadsIncomingDel_def spaces_def)

lemma SetThreadsIncomingDel_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetThreadsIncomingDel_def spaces_def)

lemma SetThreadsIncomingDel_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetThreadsIncomingDel_valid)

lemma SetThreadsIncomingDel_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Space_def
  using SetThreadsIncomingDel_Inv_Space_HasNot_Loop SetThreadsIncomingDel_Inv_Space_Valid_Has_Real
   SetThreadsIncomingDel_Inv_Space_Perms_IsNot_Empty SetThreadsIncomingDel_Inv_Space_Spaces_In_Config 
   SetThreadsIncomingDel_Inv_Space_InitialSpaces_In_Spaces SetThreadsIncomingDel_Inv_Space_Perms_Subset
   SetThreadsIncomingDel_Inv_Space_Spaces_IsNot_None SetThreadsIncomingDel_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetThreadsIncomingDel_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetThreadsIncomingDel s gno t)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetThreadsIncomingDel s gno t)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_NThreads_Is_None:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p0
  by (auto simp add: SetThreadsIncomingDel_def)

lemma SetThreadsIncomingDel_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetThreadsIncomingDel_def)

lemma SetThreadsIncomingDel_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetThreadsIncomingDel s gno val)"
  unfolding SetThreadsIncomingDel_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetThreadsIncomingDel_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetThreadsIncomingDel_def
  by (auto simp:spaces_def)

lemma SetThreadsIncomingDel_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetThreadsIncomingDel s gno t)"
  unfolding SetThreadsIncomingDel_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetThreadsIncomingDel_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetThreadsIncomingDel s gno t)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
      and p1:"gno \<in> threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetThreadsIncomingDel_def p1 apply simp
  using set_remove1_subset by fastforce

lemma SetThreadsIncomingDel_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetThreadsIncomingDel s gno pa)"
  using assms unfolding Inv_Sigma0_Space_def SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetThreadsIncomingDel s gno pa)"
  using assms unfolding Inv_RootServer_Space_def SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetThreadsIncomingDel s gno pa)"
  using assms unfolding Inv_IntThreads_Space_def SetThreadsIncomingDel_def
  by auto

lemma SetThreadsIncomingDel_Inv_Thread:
  assumes p0:"gno \<in> threads s" 
      and p1:"Inv_Thread s"
    shows "Inv_Thread (SetThreadsIncomingDel s gno t)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p0
    SetThreadsIncomingDel_Inv_Idle_NotIn_Threads SetThreadsIncomingDel_Inv_Idle_Space_Is_KernelSpace
    SetThreadsIncomingDel_Inv_Sigma0_In_Active SetThreadsIncomingDel_Inv_RootServer_In_Active 
    SetThreadsIncomingDel_Inv_IntThreads_In_Active 
    SetThreadsIncomingDel_Inv_Threads_In_Config SetThreadsIncomingDel_Inv_Active_In_Threads 
    SetThreadsIncomingDel_Inv_NThreads_Is_None SetThreadsIncomingDel_Inv_Threads_IsNot_None 
    SetThreadsIncomingDel_Inv_Threads_Space_In_Spaces SetThreadsIncomingDel_Inv_Threads_Space_Dom
    SetThreadsIncomingDel_Inv_Threads_Eq_Space_Threads SetThreadsIncomingDel_Inv_Threads_Sche_In_Threads 
    SetThreadsIncomingDel_Inv_NActive_Utcb_Is_None SetThreadsIncomingDel_Inv_Active_Utcb_IsNot_None
    SetThreadsIncomingDel_Inv_IntThreads_Utcb_Is_None SetThreadsIncomingDel_Inv_Sigma0_Space
    SetThreadsIncomingDel_Inv_RootServer_Space SetThreadsIncomingDel_Inv_IntThreads_Space
    SetThreadsIncomingDel_Inv_Threads_Partner_In_Threads SetThreadsIncomingDel_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetThreadsIncomingDel_Inv:
  assumes p0:"gno \<in> threads s"
      and p1:"Invariants s"
    shows "Invariants (SetThreadsIncomingDel s gno t)"  
  unfolding Invariants_def
  using p0 p1 Invariants_def SetThreadsIncomingDel_Inv_Current SetThreadsIncomingDel_Inv_Space SetThreadsIncomingDel_Inv_Thread
  by auto

section\<open>SetThreadPriority\<close>
subsection\<open>Current\<close>
lemma SetThreadPriority_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetThreadPriority s gno prio)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetThreadPriority s gno prio)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetThreadPriority s gno prio)"
  using SetThreadPriority_Inv_Current_Thread_In_Active SetThreadPriority_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetThreadPriority_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetThreadPriority s gno prio)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetThreadPriority_tran)

lemma SetThreadPriority_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetThreadPriority s gno prio)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetThreadPriority_rtran SetThreadPriority_valid)

lemma SetThreadPriority_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetThreadPriority s gno prio)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetThreadPriority_valid SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetThreadPriority s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetThreadPriority_direct_eq SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetThreadPriority s gno prio)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetThreadPriority_def spaces_def)

lemma SetThreadPriority_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetThreadPriority s gno prio)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetThreadPriority_def spaces_def)

lemma SetThreadPriority_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetThreadPriority s gno prio)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetThreadPriority_def spaces_def)

lemma SetThreadPriority_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetThreadPriority s gno prio)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetThreadPriority_valid)

lemma SetThreadPriority_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetThreadPriority s gno prio)"
  unfolding Inv_Space_def
  using SetThreadPriority_Inv_Space_HasNot_Loop SetThreadPriority_Inv_Space_Valid_Has_Real
   SetThreadPriority_Inv_Space_Perms_IsNot_Empty SetThreadPriority_Inv_Space_Spaces_In_Config 
   SetThreadPriority_Inv_Space_InitialSpaces_In_Spaces SetThreadPriority_Inv_Space_Perms_Subset
   SetThreadPriority_Inv_Space_Spaces_IsNot_None SetThreadPriority_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetThreadPriority_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetThreadPriority s gno prio)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetThreadPriority s gno prio)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetThreadPriority s gno prio)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetThreadPriority s gno prio)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetThreadPriority s gno prio)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetThreadPriority s gno prio)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetThreadPriority s gno prio)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
      and p2:"gno \<in> threads s"
    shows "Inv_NThreads_Is_None (SetThreadPriority s gno prio)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p2
  by (auto simp add: SetThreadPriority_def)

lemma SetThreadPriority_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetThreadPriority s gno prio)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetThreadPriority_def)

lemma SetThreadPriority_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetThreadPriority s gno val)"
  unfolding SetThreadPriority_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetThreadPriority_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetThreadPriority s gno prio)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetThreadPriority_def
  by (auto simp:spaces_def)

lemma SetThreadPriority_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetThreadPriority s gno prio)"
  unfolding SetThreadPriority_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetThreadPriority_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetThreadPriority s gno prio)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetThreadPriority s gno prio)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetThreadPriority s gno prio)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetThreadPriority s gno prio)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetThreadPriority s gno prio)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetThreadPriority_def 
  by auto

lemma SetThreadPriority_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetThreadPriority s gno prio)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetThreadPriority s gno prio)"
  using assms unfolding Inv_Sigma0_Space_def SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetThreadPriority s gno prio)"
  using assms unfolding Inv_RootServer_Space_def SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetThreadPriority s gno prio)"
  using assms unfolding Inv_IntThreads_Space_def SetThreadPriority_def
  by auto

lemma SetThreadPriority_Inv_Thread:
  assumes p1:"Inv_Thread s"
      and p2:"gno \<in> threads s"
    shows "Inv_Thread (SetThreadPriority s gno prio)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p2
    SetThreadPriority_Inv_Idle_NotIn_Threads SetThreadPriority_Inv_Idle_Space_Is_KernelSpace
    SetThreadPriority_Inv_Sigma0_In_Active SetThreadPriority_Inv_RootServer_In_Active 
    SetThreadPriority_Inv_IntThreads_In_Active 
    SetThreadPriority_Inv_Threads_In_Config SetThreadPriority_Inv_Active_In_Threads 
    SetThreadPriority_Inv_NThreads_Is_None SetThreadPriority_Inv_Threads_IsNot_None 
    SetThreadPriority_Inv_Threads_Space_Dom
    SetThreadPriority_Inv_Threads_Space_In_Spaces SetThreadPriority_Inv_Threads_Eq_Space_Threads
    SetThreadPriority_Inv_Threads_Sche_In_Threads 
    SetThreadPriority_Inv_NActive_Utcb_Is_None SetThreadPriority_Inv_Active_Utcb_IsNot_None
    SetThreadPriority_Inv_IntThreads_Utcb_Is_None SetThreadPriority_Inv_Sigma0_Space
    SetThreadPriority_Inv_RootServer_Space SetThreadPriority_Inv_IntThreads_Space
    SetThreadPriority_Inv_Threads_Partner_In_Threads SetThreadPriority_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetThreadPriority_Inv:
  assumes p1:"Invariants s"
      and p2:"gno \<in> threads s"
    shows "Invariants (SetThreadPriority s gno prio)"  
  unfolding Invariants_def
  using p1 p2 Invariants_def SetThreadPriority_Inv_Current SetThreadPriority_Inv_Space SetThreadPriority_Inv_Thread
  by auto

section\<open>SetThreadQuantum\<close>
subsection\<open>Current\<close>
lemma SetThreadQuantum_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetThreadQuantum s gno quan)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetThreadQuantum s gno quan)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetThreadQuantum s gno quan)"
  using SetThreadQuantum_Inv_Current_Thread_In_Active SetThreadQuantum_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetThreadQuantum_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetThreadQuantum_tran)

lemma SetThreadQuantum_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetThreadQuantum_rtran SetThreadQuantum_valid)

lemma SetThreadQuantum_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetThreadQuantum_valid SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetThreadQuantum s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetThreadQuantum_direct_eq SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetThreadQuantum_def spaces_def)

lemma SetThreadQuantum_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetThreadQuantum_def spaces_def)

lemma SetThreadQuantum_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetThreadQuantum_def spaces_def)

lemma SetThreadQuantum_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetThreadQuantum_valid)

lemma SetThreadQuantum_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetThreadQuantum s gno quan)"
  unfolding Inv_Space_def
  using SetThreadQuantum_Inv_Space_HasNot_Loop SetThreadQuantum_Inv_Space_Valid_Has_Real
   SetThreadQuantum_Inv_Space_Perms_IsNot_Empty SetThreadQuantum_Inv_Space_Spaces_In_Config 
   SetThreadQuantum_Inv_Space_InitialSpaces_In_Spaces SetThreadQuantum_Inv_Space_Perms_Subset
   SetThreadQuantum_Inv_Space_Spaces_IsNot_None SetThreadQuantum_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetThreadQuantum_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetThreadQuantum s gno quan)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetThreadQuantum s gno quan)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetThreadQuantum s gno quan)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetThreadQuantum s gno quan)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetThreadQuantum s gno quan)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetThreadQuantum s gno quan)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetThreadQuantum s gno quan)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
      and p2:"gno \<in> threads s"
    shows "Inv_NThreads_Is_None (SetThreadQuantum s gno quan)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p2
  by (auto simp add: SetThreadQuantum_def)

lemma SetThreadQuantum_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetThreadQuantum s gno quan)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetThreadQuantum_def)

lemma SetThreadQuantum_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetThreadQuantum s gno val)"
  unfolding SetThreadQuantum_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetThreadQuantum_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetThreadQuantum s gno quan)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetThreadQuantum_def
  by (auto simp:spaces_def)

lemma SetThreadQuantum_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetThreadQuantum s gno prio)"
  unfolding SetThreadQuantum_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetThreadQuantum_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetThreadQuantum s gno quan)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetThreadQuantum s gno quan)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetThreadQuantum s gno quan)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetThreadQuantum s gno quan)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetThreadQuantum s gno quan)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetThreadQuantum_def 
  by auto

lemma SetThreadQuantum_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetThreadQuantum s gno quan)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetThreadQuantum s gno prio)"
  using assms unfolding Inv_Sigma0_Space_def SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetThreadQuantum s gno prio)"
  using assms unfolding Inv_RootServer_Space_def SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetThreadQuantum s gno prio)"
  using assms unfolding Inv_IntThreads_Space_def SetThreadQuantum_def
  by auto

lemma SetThreadQuantum_Inv_Thread:
  assumes p1:"Inv_Thread s"
      and p2:"gno \<in> threads s"
    shows "Inv_Thread (SetThreadQuantum s gno quan)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p2
    SetThreadQuantum_Inv_Idle_NotIn_Threads SetThreadQuantum_Inv_Idle_Space_Is_KernelSpace
    SetThreadQuantum_Inv_Sigma0_In_Active SetThreadQuantum_Inv_RootServer_In_Active 
    SetThreadQuantum_Inv_IntThreads_In_Active 
    SetThreadQuantum_Inv_Threads_In_Config SetThreadQuantum_Inv_Active_In_Threads 
    SetThreadQuantum_Inv_NThreads_Is_None SetThreadQuantum_Inv_Threads_IsNot_None
    SetThreadQuantum_Inv_Threads_Space_Dom
    SetThreadQuantum_Inv_Threads_Space_In_Spaces SetThreadQuantum_Inv_Threads_Eq_Space_Threads
    SetThreadQuantum_Inv_Threads_Sche_In_Threads 
    SetThreadQuantum_Inv_NActive_Utcb_Is_None SetThreadQuantum_Inv_Active_Utcb_IsNot_None
    SetThreadQuantum_Inv_IntThreads_Utcb_Is_None SetThreadQuantum_Inv_Sigma0_Space
    SetThreadQuantum_Inv_RootServer_Space SetThreadQuantum_Inv_IntThreads_Space
    SetThreadQuantum_Inv_Threads_Partner_In_Threads SetThreadQuantum_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetThreadQuantum_Inv:  
  assumes p1:"Invariants s"
      and p2:"gno \<in> threads s"
    shows "Invariants (SetThreadQuantum s gno quan)"  
  unfolding Invariants_def
  using p1 p2 Invariants_def SetThreadQuantum_Inv_Current SetThreadQuantum_Inv_Space SetThreadQuantum_Inv_Thread
  by auto

section\<open>SetThreadTimeslice\<close>
subsection\<open>Current\<close>
lemma SetThreadTimeslice_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetThreadTimeslice s gno slice)"
  unfolding Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetThreadTimeslice s gno slice)"
  using SetThreadTimeslice_Inv_Current_Thread_In_Active SetThreadTimeslice_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetThreadTimeslice_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetThreadTimeslice_tran)

lemma SetThreadTimeslice_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetThreadTimeslice_rtran SetThreadTimeslice_valid)

lemma SetThreadTimeslice_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  using SetThreadTimeslice_valid SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetThreadTimeslice s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetThreadTimeslice_direct_eq SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetThreadTimeslice_def spaces_def)

lemma SetThreadTimeslice_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetThreadTimeslice_def spaces_def)

lemma SetThreadTimeslice_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetThreadTimeslice_def spaces_def)

lemma SetThreadTimeslice_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetThreadTimeslice_valid)

lemma SetThreadTimeslice_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetThreadTimeslice s gno slice)"
  unfolding Inv_Space_def
  using SetThreadTimeslice_Inv_Space_HasNot_Loop SetThreadTimeslice_Inv_Space_Valid_Has_Real
   SetThreadTimeslice_Inv_Space_Perms_IsNot_Empty SetThreadTimeslice_Inv_Space_Spaces_In_Config 
   SetThreadTimeslice_Inv_Space_InitialSpaces_In_Spaces SetThreadTimeslice_Inv_Space_Perms_Subset
   SetThreadTimeslice_Inv_Space_Spaces_IsNot_None SetThreadTimeslice_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetThreadTimeslice_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetThreadTimeslice s gno slice)"
  unfolding Inv_Idle_NotIn_Threads_def 
  using p1[unfolded Inv_Idle_NotIn_Threads_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetThreadTimeslice s gno slice)"
  unfolding Inv_Idle_Space_Is_KernelSpace_def 
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetThreadTimeslice s gno slice)"
  unfolding Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetThreadTimeslice s gno slice)"
  unfolding Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetThreadTimeslice s gno slice)"
  unfolding Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetThreadTimeslice s gno slice)"
  unfolding Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetThreadTimeslice s gno slice)"
  unfolding Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
      and p2:"gno \<in> threads s"
    shows "Inv_NThreads_Is_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p2
  by (auto simp add: SetThreadTimeslice_def)

lemma SetThreadTimeslice_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by (auto simp add: SetThreadTimeslice_def)

lemma SetThreadTimeslice_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetThreadTimeslice s gno val)"
  unfolding SetThreadTimeslice_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetThreadTimeslice_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetThreadTimeslice s gno slice)"
  unfolding Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] SetThreadTimeslice_def
  by (auto simp:spaces_def)

lemma SetThreadTimeslice_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetThreadTimeslice s gno prio)"
  unfolding SetThreadTimeslice_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma SetThreadTimeslice_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetThreadTimeslice s gno slice)"
  unfolding Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetThreadTimeslice s gno slice)"
  unfolding Inv_IntThreads_Utcb_Is_None_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetThreadTimeslice s gno slice)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def] SetThreadTimeslice_def 
  by auto

lemma SetThreadTimeslice_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetThreadTimeslice s gno slice)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetThreadTimeslice s gno prio)"
  using assms unfolding Inv_Sigma0_Space_def SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetThreadTimeslice s gno prio)"
  using assms unfolding Inv_RootServer_Space_def SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetThreadTimeslice s gno prio)"
  using assms unfolding Inv_IntThreads_Space_def SetThreadTimeslice_def
  by auto

lemma SetThreadTimeslice_Inv_Thread:
  assumes p1:"Inv_Thread s"
      and p2:"gno \<in> threads s"
    shows "Inv_Thread (SetThreadTimeslice s gno slice)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p2
    SetThreadTimeslice_Inv_Idle_NotIn_Threads SetThreadTimeslice_Inv_Idle_Space_Is_KernelSpace
    SetThreadTimeslice_Inv_Sigma0_In_Active SetThreadTimeslice_Inv_RootServer_In_Active 
    SetThreadTimeslice_Inv_IntThreads_In_Active 
    SetThreadTimeslice_Inv_Threads_In_Config SetThreadTimeslice_Inv_Active_In_Threads 
    SetThreadTimeslice_Inv_NThreads_Is_None SetThreadTimeslice_Inv_Threads_IsNot_None
    SetThreadTimeslice_Inv_Threads_Space_Dom
    SetThreadTimeslice_Inv_Threads_Space_In_Spaces SetThreadTimeslice_Inv_Threads_Eq_Space_Threads
    SetThreadTimeslice_Inv_Threads_Sche_In_Threads 
    SetThreadTimeslice_Inv_NActive_Utcb_Is_None SetThreadTimeslice_Inv_Active_Utcb_IsNot_None
    SetThreadTimeslice_Inv_IntThreads_Utcb_Is_None SetThreadTimeslice_Inv_Sigma0_Space
    SetThreadTimeslice_Inv_RootServer_Space SetThreadTimeslice_Inv_IntThreads_Space
    SetThreadTimeslice_Inv_Threads_Partner_In_Threads SetThreadTimeslice_Inv_Threads_Incoming_In_Threads
  by auto

lemma SetThreadTimeslice_Inv:
  assumes p1:"Invariants s"
      and p2:"gno \<in> threads s"
    shows "Invariants (SetThreadTimeslice s gno slice)"
  unfolding Invariants_def
  using p1 p2 Invariants_def SetThreadTimeslice_Inv_Current SetThreadTimeslice_Inv_Space SetThreadTimeslice_Inv_Thread 
  by auto

section\<open>Unwind\<close>
subsection\<open>Current\<close>
lemma Unwind_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (Unwind s gno)"
  unfolding Inv_Current_Thread_In_Active_def Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma Unwind_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma Unwind_Inv_Current_Isar:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (Unwind s gno)"
  using Unwind_Inv_Current_Thread_In_Active Unwind_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

lemma Unwind_Inv_Current:"\<forall> s. Inv_Current s \<longrightarrow> Inv_Current (Unwind s gno)"
  using Unwind_Inv_Current_Isar
  by simp

subsection\<open>Space\<close>
lemma Unwind_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (Unwind s gno)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst Unwind_tran)

lemma Unwind_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (Unwind s gno)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: Unwind_rtran Unwind_valid)

lemma Unwind_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (Unwind s gno)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: Unwind_valid Unwind_NC_Space)

lemma Unwind_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (Unwind s gno)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using Unwind_direct_eq Unwind_NC_Space
  by auto

lemma Unwind_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (Unwind s gno)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:Unwind_NC_Space)

lemma Unwind_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (Unwind s gno)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:Unwind_NC_Space)

lemma Unwind_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (Unwind s gno)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:Unwind_NC_Space)

lemma Unwind_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (Unwind s gno)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:Unwind_valid)

lemma Unwind_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (Unwind s gno)"
  unfolding Inv_Space_def
  using Unwind_Inv_Space_HasNot_Loop Unwind_Inv_Space_Valid_Has_Real
   Unwind_Inv_Space_Perms_IsNot_Empty Unwind_Inv_Space_Spaces_In_Config 
   Unwind_Inv_Space_InitialSpaces_In_Spaces Unwind_Inv_Space_Perms_Subset
   Unwind_Inv_Space_Spaces_IsNot_None Unwind_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma Unwind_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma Unwind_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma Unwind_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma Unwind_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma Unwind_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma Unwind_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma Unwind_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma Unwind_Inv_NThreads_Is_None:
  assumes p0:"Inv_Active_In_Threads s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_NThreads_Is_None (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_NThreads_Is_None_def 
  using p1[unfolded Inv_NThreads_Is_None_def] p0[unfolded Inv_Active_In_Threads_def]
        p2[unfolded Inv_Threads_Partner_In_Threads_def] GetIpcPartner_def
  by auto

lemma Unwind_Inv_Threads_IsNot_None:
  assumes p0:"Inv_Active_In_Threads s"
      and p1:"Inv_Threads_IsNot_None s"
      and p2:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_IsNot_None (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Threads_IsNot_None_def 
  using p1[unfolded Inv_Threads_IsNot_None_def] p0[unfolded Inv_Active_In_Threads_def]
        p2[unfolded Inv_Threads_Partner_In_Threads_def] GetIpcPartner_def
  by auto

lemma Unwind_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma Unwind_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def]
  by (auto simp:spaces_def)

lemma Unwind_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Threads_Eq_Space_Threads_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def]
  by (auto simp:spaces_def)

lemma Unwind_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma Unwind_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma Unwind_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (Unwind s gno)"
  unfolding Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma Unwind_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (Unwind s gno)"
  unfolding Inv_IntThreads_Utcb_Is_None_def Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def
  using p0[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma Unwind_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (Unwind s gno)"
  unfolding Inv_Threads_Partner_In_Threads_def Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def
  using p0[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma Unwind_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
      and p1:"Inv_Active_In_Threads s"
      and p2:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (Unwind s gno)"
  unfolding Inv_Threads_Incoming_In_Threads_def Unwind_def Let_def dequeue_wait_def SetThreadsIncomingDel_def GetIpcPartner_def
  using p0[unfolded Inv_Threads_Incoming_In_Threads_def] p1[unfolded Inv_Active_In_Threads_def]
        p2[unfolded Inv_Threads_Partner_In_Threads_def] apply simp
  by (metis notin_set_remove1 option.sel) 

lemma Unwind_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (Unwind s gno)"
  using assms unfolding Inv_Sigma0_Space_def Unwind_def
  Let_def dequeue_wait_def SetThreadsIncomingDel_def
  by auto

lemma Unwind_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (Unwind s gno)"
  using assms unfolding Inv_RootServer_Space_def Unwind_def
  Let_def dequeue_wait_def SetThreadsIncomingDel_def
  by auto

lemma Unwind_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (Unwind s gno)"
  using assms unfolding Inv_IntThreads_Space_def Unwind_def
  Let_def dequeue_wait_def SetThreadsIncomingDel_def
  by auto

lemma Unwind_Inv_Thread:
  assumes p0:"Inv_Thread s"
    shows "Inv_Thread (Unwind s gno)"
  unfolding Inv_Thread_def
  using p0[unfolded Inv_Thread_def] 
    Unwind_Inv_Idle_NotIn_Threads Unwind_Inv_Idle_Space_Is_KernelSpace
    Unwind_Inv_Sigma0_In_Active Unwind_Inv_RootServer_In_Active 
    Unwind_Inv_IntThreads_In_Active 
    Unwind_Inv_Threads_In_Config Unwind_Inv_Active_In_Threads 
    Unwind_Inv_NThreads_Is_None Unwind_Inv_Threads_IsNot_None
    Unwind_Inv_Threads_Space_Dom
    Unwind_Inv_Threads_Space_In_Spaces Unwind_Inv_Threads_Eq_Space_Threads
    Unwind_Inv_Threads_Sche_In_Threads 
    Unwind_Inv_NActive_Utcb_Is_None Unwind_Inv_Active_Utcb_IsNot_None
    Unwind_Inv_IntThreads_Utcb_Is_None Unwind_Inv_Sigma0_Space
    Unwind_Inv_RootServer_Space Unwind_Inv_IntThreads_Space
    Unwind_Inv_Threads_Partner_In_Threads Unwind_Inv_Threads_Incoming_In_Threads
  by auto

lemma Unwind_Inv:"\<forall>s. Invariants s \<longrightarrow> Invariants (Unwind s gno)"
  unfolding Invariants_def
  using Unwind_Inv_Current Unwind_Inv_Space Unwind_Inv_Thread
  by auto

section\<open>SetError\<close>
subsection\<open>Current\<close>
lemma SetError_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma SetError_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma SetError_Inv_Current_Isar:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetError s gno error)"
  using SetError_Inv_Current_Thread_In_Active SetError_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

lemma SetError_Inv_Current:"\<forall> s error. Inv_Current s \<longrightarrow> Inv_Current (SetError s gno error)"
  using SetError_Inv_Current_Isar
  by simp

subsection\<open>Space\<close>
lemma SetError_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetError s gno error)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetError_tran)

lemma SetError_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetError s gno error)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetError_rtran SetError_valid)

lemma SetError_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetError s gno error)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: SetError_valid SetError_NC_Space)

lemma SetError_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetError s gno error)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetError_direct_eq SetError_NC_Space
  by auto

lemma SetError_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetError s gno error)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetError_NC_Space spaces_def)

lemma SetError_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetError s gno error)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetError_NC_Space spaces_def)

lemma SetError_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetError s gno error)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetError_NC_Space spaces_def)

lemma SetError_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetError s gno error)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetError_valid)

lemma SetError_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetError s gno error)"
  unfolding Inv_Space_def
  using SetError_Inv_Space_HasNot_Loop SetError_Inv_Space_Valid_Has_Real
   SetError_Inv_Space_Perms_IsNot_Empty SetError_Inv_Space_Spaces_In_Config 
   SetError_Inv_Space_InitialSpaces_In_Spaces SetError_Inv_Space_Perms_Subset
   SetError_Inv_Space_Spaces_IsNot_None SetError_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetError_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma SetError_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma SetError_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma SetError_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma SetError_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto
  
lemma SetError_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma SetError_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma SetError_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def] p2[unfolded Inv_Active_In_Threads_def]
  by auto

lemma SetError_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma SetError_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetError s gno val)"
  unfolding SetError_def SetThreadError_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma SetError_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def]
  by (auto simp:spaces_def)

lemma SetError_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Threads_Eq_Space_Threads_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def]
  by (auto simp:spaces_def)

lemma SetError_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma SetError_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma SetError_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetError s gno error)"
  unfolding SetError_def SetThreadError_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma SetError_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetError s gno error)"
  unfolding Inv_IntThreads_Utcb_Is_None_def SetError_def SetThreadError_def
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma SetError_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetError s gno error)"
  unfolding Inv_Threads_Partner_In_Threads_def SetError_def SetThreadError_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma SetError_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetError s gno error)"
  unfolding Inv_Threads_Incoming_In_Threads_def SetError_def SetThreadError_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma SetError_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetError s gno error)"
  using assms unfolding Inv_Sigma0_Space_def SetError_def SetThreadError_def
  by auto

lemma SetError_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetError s gno error)"
  using assms unfolding Inv_RootServer_Space_def SetError_def SetThreadError_def
  by auto

lemma SetError_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetError s gno error)"
  using assms unfolding Inv_IntThreads_Space_def SetError_def SetThreadError_def
  by auto

lemma SetError_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (SetError s gno error)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] 
    SetError_Inv_Idle_NotIn_Threads SetError_Inv_Idle_Space_Is_KernelSpace
    SetError_Inv_Sigma0_In_Active SetError_Inv_RootServer_In_Active 
    SetError_Inv_IntThreads_In_Active 
    SetError_Inv_Threads_In_Config SetError_Inv_Active_In_Threads 
    SetError_Inv_NThreads_Is_None SetError_Inv_Threads_IsNot_None
    SetError_Inv_Threads_Space_Dom
    SetError_Inv_Threads_Space_In_Spaces SetError_Inv_Threads_Eq_Space_Threads
    SetError_Inv_Threads_Sche_In_Threads 
    SetError_Inv_NActive_Utcb_Is_None SetError_Inv_Active_Utcb_IsNot_None
    SetError_Inv_IntThreads_Utcb_Is_None SetError_Inv_Threads_Incoming_In_Threads 
    SetError_Inv_Threads_Partner_In_Threads SetError_Inv_Sigma0_Space
    SetError_Inv_RootServer_Space SetError_Inv_IntThreads_Space
  by auto

lemma SetError_Inv:"\<forall>s error. Invariants s \<longrightarrow> Invariants (SetError s gno error)"
  unfolding Invariants_def
  using SetError_Inv_Current SetError_Inv_Space SetError_Inv_Thread
  by auto

section\<open>CreateThread\<close>
subsection\<open>Current\<close>
lemma CreateThread_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
  shows "Inv_Current_Thread_In_Active (CreateThread SysConf s gno space scheduler)"
  unfolding CreateThread_def Let_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
    CreateAddressSpace_NC_Current CreateAddressSpace_NC_Thread
    SetError_NC_Current SetError_NC_Thread
  by auto

lemma CreateThread_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (CreateThread SysConf s gno space scheduler)"
  unfolding CreateThread_def Let_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
    CreateAddressSpace_NC_Current CreateAddressSpace_NC_Thread
    SetError_NC_Current SetError_NC_Thread
  by auto

lemma CreateThread_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (CreateThread SysConf s gno space scheduler)"
  using CreateThread_Inv_Current_Thread_In_Active CreateThread_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma CreateThread_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  apply(subst CreateThread_tran)
  by auto

lemma CreateThread_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: CreateThread_rtran CreateThread_valid)

lemma CreateThread_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_Perms_IsNot_Empty_def
  apply(subst CreateThread_valid)
  unfolding CreateThread_def Let_def
  apply(cases "CreateThread_Cond SysConf s gno space scheduler")
  subgoal
    apply(cases "space \<in> spaces s")
    subgoal
      using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
      unfolding CreateThread_def Let_def CreateThread_Cond_def CreateAddressSpace_def
      SetError_def SetThreadError_def get_perms_def
      by simp
    apply auto
    apply(case_tac "sp = space")
    subgoal
      by (simp add: Inv_Space_Valid_In_Spaces_lemma)
    using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
    unfolding CreateThread_Cond_def CreateAddressSpace_def
      SetError_def SetThreadError_def get_perms_def
    by simp
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def]
  by simp

lemma CreateTcb_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
  shows "Inv_Space_Perms_Subset (CreateTcb s gno space scheduler)"
  using p1 unfolding Inv_Space_Perms_Subset_def 
  CreateTcb_def direct_path_def get_perms_def
  by auto

lemma CreateThread_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and "Inv_Space_Valid_Has_Real s"
  shows "Inv_Space_Perms_Subset (CreateThread SysConf s gno space scheduler)"
  apply(subst CreateThread_eq)
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Perms_Subset)
    apply(rule CreateTcb_Inv_Space_Perms_Subset)
    apply(rule elim_if)
    using assms CreateAddressSpace_Inv_Space_Perms_Subset
    by auto
  using assms by simp

lemma CreateThread_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  unfolding CreateThread_def Let_def CreateThread_Cond_def CreateAddressSpace_def
    SetError_def SetThreadError_def spaces_def
  by auto

lemma CreateThread_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  using CreateThread_C_Space' CreateThread_C_Space
    CreateThread_NC_Space CreateThread_NC_Space_Other
  using Un_assoc subset_Un_eq by blast

lemma CreateThread_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (CreateThread SysConf s gno space scheduler)"
  apply(subst CreateThread_eq)
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Spaces_IsNot_None)
    apply(cases "space \<notin> spaces s")
     apply auto
    subgoal
      apply (auto simp add: CreateAddressSpace_def CreateThread_Cond_def CreateTcb_def)
      using assms unfolding Inv_Space_Spaces_IsNot_None_def spaces_def
      by auto
    unfolding CreateTcb_def
    using assms unfolding Inv_Space_Spaces_IsNot_None_def spaces_def
    by auto
  using assms by simp

lemma CreateThread_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:CreateThread_valid)


lemma CreateThread_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Space_def
  using CreateThread_Inv_Space_HasNot_Loop CreateThread_Inv_Space_Valid_Has_Real
   CreateThread_Inv_Space_Perms_IsNot_Empty CreateThread_Inv_Space_Spaces_In_Config 
   CreateThread_Inv_Space_InitialSpaces_In_Spaces CreateThread_Inv_Space_Perms_Subset
   CreateThread_Inv_Space_Spaces_IsNot_None CreateThread_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
text\<open>CreateTcb\<close>
lemma CreateTcb_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
      and p2:"gno \<noteq> idle"
    shows "Inv_Idle_NotIn_Threads (CreateTcb s gno space scheduler)"
  using p1 p2 Inv_Idle_NotIn_Threads_def CreateTcb_def
  by auto

lemma CreateTcb_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
      and p2:"gno \<noteq> idle"
    shows "Inv_Idle_Space_Is_KernelSpace (CreateTcb s gno space scheduler)"
  using p1 p2 Inv_Idle_Space_Is_KernelSpace_def CreateTcb_def
  by auto

lemma CreateTcb_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma CreateTcb_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma CreateTcb_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma CreateTcb_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
      and p2:"gno \<in> Threads_Gno SysConf"
    shows "Inv_Threads_In_Config (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def] p2
  by auto

lemma CreateTcb_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma CreateTcb_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma CreateTcb_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma CreateTcb_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
      and p2:"space \<in> spaces s"
    shows "Inv_Threads_Space_In_Spaces (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Threads_Space_In_Spaces_def
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] p2
  by (auto simp:spaces_def)

lemma CreateTcb_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
      and p2:"scheduler \<in> threads s"
    shows "Inv_Threads_Sche_In_Threads (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] p2
  by auto

lemma CreateTcb_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
      and p2:"Inv_NThreads_Is_None s"
      and p3:"gno \<in> Threads_Gno SysConf - threads s"
    shows "Inv_NActive_Utcb_Is_None (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
    p2[unfolded Inv_NThreads_Is_None_def] p3
  by auto

lemma CreateTcb_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma CreateTcb_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (CreateTcb s gno space scheduler)"
  unfolding Inv_IntThreads_Utcb_Is_None_def CreateTcb_def SetThreadError_def
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def]
  by auto

lemma CreateTcb_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma CreateTcb_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (CreateTcb s gno space scheduler)"
  unfolding CreateTcb_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma CreateTcb_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
    and "gno \<noteq> kSigma0"
  shows "Inv_Sigma0_Space (CreateTcb s gno space scheduler)"
  using assms unfolding Inv_Sigma0_Space_def CreateTcb_def
  by auto

lemma CreateTcb_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
    and "gno \<noteq> kRootServer"
  shows "Inv_RootServer_Space (CreateTcb s gno space scheduler)"
  using assms unfolding Inv_RootServer_Space_def CreateTcb_def
  by auto

lemma CreateTcb_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
    and "gno \<notin> kIntThreads"
  shows "Inv_IntThreads_Space (CreateTcb s gno space scheduler)"
  using assms unfolding Inv_IntThreads_Space_def CreateTcb_def
  by auto

text\<open>CreateThread\<close>
lemma CreateThread_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
    apply(subst CreateTcb_Inv_Idle_NotIn_Threads)
  using p1 CreateAddressSpace_Inv_Idle_NotIn_Threads CreateThread_Cond_def
  by auto

lemma CreateThread_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
    apply(subst CreateTcb_Inv_Idle_Space_Is_KernelSpace)
  using p1 CreateAddressSpace_Inv_Idle_Space_Is_KernelSpace CreateThread_Cond_def
  by auto

lemma CreateThread_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
    apply(subst CreateTcb_Inv_Sigma0_In_Active)
  using p1 CreateAddressSpace_Inv_Sigma0_In_Active
  by auto

lemma CreateThread_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
    apply(subst CreateTcb_Inv_RootServer_In_Active)
  using p1 CreateAddressSpace_Inv_RootServer_In_Active
  by auto

lemma CreateThread_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
    apply(subst CreateTcb_Inv_IntThreads_In_Active)
  using p1 CreateAddressSpace_Inv_IntThreads_In_Active
  by auto
  
lemma CreateThread_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
    apply(subst CreateTcb_Inv_Threads_In_Config)
  using p1 CreateAddressSpace_Inv_Threads_In_Config CreateThread_Cond_def
  by auto

lemma CreateThread_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
    apply(subst CreateTcb_Inv_Active_In_Threads)
  using p1 CreateAddressSpace_Inv_Active_In_Threads
  by auto

lemma CreateThread_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
   apply(subst CreateTcb_Inv_NThreads_Is_None)
  using p1 CreateAddressSpace_Inv_NThreads_Is_None apply auto[1]
    prefer 2
    apply(subst CreateTcb_Inv_Active_In_Threads)
  using p2 CreateAddressSpace_Inv_Active_In_Threads apply auto[1]
  using p1
  by auto

lemma CreateThread_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
    apply(subst CreateTcb_Inv_Threads_IsNot_None)
  using p1 CreateAddressSpace_Inv_Threads_IsNot_None
  by auto

lemma CreateThread_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  subgoal
    using assms unfolding Inv_Threads_Space_Dom_def
    by(auto simp add:CreateTcb_def CreateAddressSpace_def CreateThread_Cond_def)
  using assms by simp
    
lemma CreateThread_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)                      
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
    apply(subst CreateTcb_Inv_Threads_Space_In_Spaces)
  using p1 CreateAddressSpace_Inv_Threads_Space_In_Spaces CreateThread_Cond_def
    CreateAddressSpace_C_Space
  by auto

lemma CreateThread_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
      and p2:"Inv_NThreads_Is_None s"
      and p3:"Inv_Threads_Space_Dom s"
      and p4:"Inv_Threads_Space_In_Spaces s"
      and p5:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Threads_Eq_Space_Threads (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Eq_Space_Threads)
  apply auto
  subgoal
    apply(subgoal_tac "space \<in> Address_Space SysConf")
    subgoal
      unfolding Inv_Threads_Eq_Space_Threads_def
      apply rule
      apply rule
    proof-
      fix spacea
      assume a1:"CreateThread_Cond SysConf s gno space scheduler" and a2:"space \<notin> spaces s" and
          a3:"space \<in> Address_Space SysConf" and a4:"spacea \<in> spaces (CreateTcb (CreateAddressSpace SysConf s space) gno space scheduler)"
      have h01:"\<forall>t. thread_space s t = Some space \<longrightarrow> t \<noteq> idle"
      using a1[unfolded CreateThread_Cond_def] p5[unfolded Inv_Idle_Space_Is_KernelSpace_def] 
        by auto
      then have h02:"\<nexists>t. thread_space s t = Some space"
        using Thread_Exist p3 p4 a2 by auto
      show "the (space_threads (CreateTcb (CreateAddressSpace SysConf s space) gno space scheduler) spacea) =
       {t. thread_space (CreateTcb (CreateAddressSpace SysConf s space) gno space scheduler) t = Some spacea}"
      proof(cases "spacea = space")
        case True
        then show ?thesis
          unfolding CreateTcb_def CreateAddressSpace_def
          using a2 a3 h02
          by auto
      next
        case False
        then have h1:"spacea \<in> spaces s" using a4 CreateTcb_def CreateAddressSpace_NC_Space_Other
          by (auto simp:spaces_def)
        then have h11:"the (space_threads s spacea) = {t. thread_space s t = Some spacea}" 
          using p1 Inv_Threads_Eq_Space_Threads_def by simp
        then show ?thesis unfolding CreateTcb_def CreateAddressSpace_def
          using False a2 a1[unfolded CreateThread_Cond_def] p2[unfolded Inv_NThreads_Is_None_def]
          by auto
      qed
    qed
    using CreateThread_Cond_def by simp
  subgoal
    using assms unfolding Inv_Threads_Eq_Space_Threads_def CreateTcb_def
    by (auto simp add:spaces_def CreateThread_Cond_def Inv_NThreads_Is_None_def)
  using assms by simp

lemma CreateThread_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
    apply(subst CreateTcb_Inv_Threads_Sche_In_Threads)
  subgoal
    using CreateAddressSpace_Inv_Threads_Sche_In_Threads p1 by simp
  subgoal
    using CreateThread_Cond_def CreateAddressSpace_def
    by simp
  using p1 by auto

lemma CreateThread_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
      and p2:"Inv_NThreads_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
    apply(subst CreateTcb_Inv_NActive_Utcb_Is_None)
  subgoal
    using p1 CreateAddressSpace_Inv_NActive_Utcb_Is_None
    by simp
  subgoal
    using p2 CreateAddressSpace_Inv_NThreads_Is_None
    by simp
  subgoal
    using CreateThread_Cond_def CreateAddressSpace_def
    by auto
  using p1 by auto

lemma CreateThread_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
    apply(subst CreateTcb_Inv_Active_Utcb_IsNot_None)
  using p1 CreateAddressSpace_Inv_Active_Utcb_IsNot_None
  by auto

lemma CreateThread_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
    apply(subst CreateTcb_Inv_IntThreads_Utcb_Is_None)
  using p1 CreateAddressSpace_Inv_IntThreads_Utcb_Is_None CreateThread_Cond_def
  by auto

lemma CreateThread_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
    apply(subst CreateTcb_Inv_Threads_Partner_In_Threads)
  subgoal
    using CreateAddressSpace_Inv_Threads_Partner_In_Threads p1 by simp
  subgoal
    using CreateThread_Cond_def CreateAddressSpace_def
    by simp
  using p1 by auto

lemma CreateThread_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
    apply(subst CreateTcb_Inv_Threads_Incoming_In_Threads)
  subgoal
    using CreateAddressSpace_Inv_Threads_Incoming_In_Threads p1 by simp
  subgoal
    using CreateThread_Cond_def CreateAddressSpace_def
    by simp
  using p1 by auto

lemma CreateThread_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
    and "Inv_Active_In_Threads s"
    and "Inv_Sigma0_In_Active s"
  shows "Inv_Sigma0_Space (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_Space)
    apply(subst CreateTcb_Inv_Sigma0_Space)
  subgoal
    using CreateAddressSpace_Inv_Sigma0_Space assms by simp
  subgoal
    unfolding CreateThread_Cond_def
    using assms Inv_Active_In_Threads_def Inv_Sigma0_In_Active_def
    by blast
  using assms by auto

lemma CreateThread_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
    and "Inv_Active_In_Threads s"
    and "Inv_RootServer_In_Active s"
  shows "Inv_RootServer_Space (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_Space)
    apply(subst CreateTcb_Inv_RootServer_Space)
  subgoal
    using CreateAddressSpace_Inv_RootServer_Space assms by simp
  subgoal
    unfolding CreateThread_Cond_def
    using assms Inv_Active_In_Threads_def Inv_RootServer_In_Active_def
    by blast
  using assms by auto

lemma CreateThread_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
    and "Inv_Active_In_Threads s"
    and "Inv_IntThreads_In_Active s"
  shows "Inv_IntThreads_Space (CreateThread' SysConf s gno space scheduler)"
  unfolding CreateThread'_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Space)
    apply(subst CreateTcb_Inv_IntThreads_Space)
  subgoal
    using CreateAddressSpace_Inv_IntThreads_Space assms by simp
  subgoal
    unfolding CreateThread_Cond_def
    using assms Inv_Active_In_Threads_def Inv_IntThreads_In_Active_def
    by blast
  using assms by auto

lemma CreateThread_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (CreateThread SysConf s gno space scheduler)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] 
    CreateThread_Inv_Idle_NotIn_Threads CreateThread_Inv_Idle_Space_Is_KernelSpace
    CreateThread_Inv_Sigma0_In_Active CreateThread_Inv_RootServer_In_Active 
    CreateThread_Inv_IntThreads_In_Active 
    CreateThread_Inv_Threads_In_Config CreateThread_Inv_Active_In_Threads 
    CreateThread_Inv_NThreads_Is_None CreateThread_Inv_Threads_IsNot_None
    CreateThread_Inv_Threads_Space_Dom
    CreateThread_Inv_Threads_Space_In_Spaces CreateThread_Inv_Threads_Eq_Space_Threads
    CreateThread_Inv_Threads_Sche_In_Threads 
    CreateThread_Inv_NActive_Utcb_Is_None CreateThread_Inv_Active_Utcb_IsNot_None
    CreateThread_Inv_IntThreads_Utcb_Is_None CreateThread_Inv_Threads_Partner_In_Threads
    CreateThread_Inv_Threads_Incoming_In_Threads CreateThread_eq CreateThread_Inv_Sigma0_Space
    CreateThread_Inv_RootServer_Space CreateThread_Inv_IntThreads_Space
  by auto

lemma CreateThread_Inv:
  assumes "Invariants s"
  shows "Invariants (CreateThread SysConf s gno space scheduler)"
  using assms unfolding Invariants_def
  using CreateThread_Inv_Current CreateThread_Inv_Space CreateThread_Inv_Thread
  by auto

section\<open>ActivateThread\<close>
subsection\<open>Current\<close>
lemma ActivateThread_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma ActivateThread_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma ActivateThread_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (ActivateThread SysConf s gno pager)"
  using ActivateThread_Inv_Current_Thread_In_Active ActivateThread_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma ActivateThread_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst ActivateThread_tran)

lemma ActivateThread_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: ActivateThread_rtran ActivateThread_valid)

lemma ActivateThread_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: ActivateThread_valid ActivateThread_NC_Space)

lemma ActivateThread_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using ActivateThread_direct_eq ActivateThread_NC_Space
  by auto

lemma ActivateThread_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:ActivateThread_NC_Space)

lemma ActivateThread_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:ActivateThread_NC_Space)

lemma ActivateThread_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:ActivateThread_NC_Space)

lemma ActivateThread_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:ActivateThread_valid)

lemma ActivateThread_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (ActivateThread SysConf s gno pager)"
  unfolding Inv_Space_def
  using ActivateThread_Inv_Space_HasNot_Loop ActivateThread_Inv_Space_Valid_Has_Real
   ActivateThread_Inv_Space_Perms_IsNot_Empty ActivateThread_Inv_Space_Spaces_In_Config 
   ActivateThread_Inv_Space_InitialSpaces_In_Spaces ActivateThread_Inv_Space_Perms_Subset
   ActivateThread_Inv_Space_Spaces_IsNot_None ActivateThread_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma ActivateThread_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def
  by auto

lemma ActivateThread_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def
  by auto

lemma ActivateThread_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma ActivateThread_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma ActivateThread_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma ActivateThread_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def
  by auto

lemma ActivateThread_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma ActivateThread_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def Inv_Active_In_Threads_def
  by auto

lemma ActivateThread_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma ActivateThread_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  using assms Inv_Threads_Space_Dom_def
  by auto
  
lemma ActivateThread_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
  using p1 Inv_Threads_Space_In_Spaces_def
  by (auto simp:spaces_def)

lemma ActivateThread_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Eq_Space_Threads)
  using p1 Inv_Threads_Eq_Space_Threads_def
  by (auto simp:spaces_def)

lemma ActivateThread_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def
  by auto

lemma ActivateThread_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma ActivateThread_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma ActivateThread_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
      and p2:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_Utcb_Is_None (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 p2 Inv_IntThreads_Utcb_Is_None_def Inv_IntThreads_In_Active_def
  by auto

lemma ActivateThread_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def
  by auto

lemma ActivateThread_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def
  by auto

lemma ActivateThread_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_Space)
  using assms Inv_Sigma0_Space_def
  by auto

lemma ActivateThread_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_Space)
  using assms Inv_RootServer_Space_def
  by auto

lemma ActivateThread_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (ActivateThread SysConf s gno pager)"
  unfolding ActivateThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Space)
  using assms Inv_IntThreads_Space_def
  by auto

lemma ActivateThread_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (ActivateThread SysConf s gno pager)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] 
    ActivateThread_Inv_Idle_NotIn_Threads ActivateThread_Inv_Idle_Space_Is_KernelSpace
    ActivateThread_Inv_Sigma0_In_Active ActivateThread_Inv_RootServer_In_Active 
    ActivateThread_Inv_IntThreads_In_Active 
    ActivateThread_Inv_Threads_In_Config ActivateThread_Inv_Active_In_Threads 
    ActivateThread_Inv_NThreads_Is_None ActivateThread_Inv_Threads_IsNot_None
    ActivateThread_Inv_Threads_Space_Dom ActivateThread_Inv_Threads_Eq_Space_Threads
    ActivateThread_Inv_Threads_Space_In_Spaces ActivateThread_Inv_Threads_Sche_In_Threads 
    ActivateThread_Inv_NActive_Utcb_Is_None ActivateThread_Inv_Active_Utcb_IsNot_None
    ActivateThread_Inv_IntThreads_Utcb_Is_None ActivateThread_Inv_Threads_Partner_In_Threads
    ActivateThread_Inv_Threads_Incoming_In_Threads ActivateThread_Inv_Sigma0_Space
    ActivateThread_Inv_RootServer_Space ActivateThread_Inv_IntThreads_Space
  by auto

lemma ActivateThread_Inv:
  assumes "Invariants s"
  shows "Invariants (ActivateThread SysConf s gno pager)"
  using assms unfolding Invariants_def
  using ActivateThread_Inv_Current ActivateThread_Inv_Space ActivateThread_Inv_Thread
  by auto

section\<open>CreateActiveThread\<close>
subsection\<open>Current\<close>
lemma CreateActiveThread_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma CreateActiveThread_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma CreateActiveThread_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (CreateActiveThread SysConf s gno space scheduler pager)"
  using CreateActiveThread_Inv_Current_Thread_In_Active CreateActiveThread_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma CreateActiveThread_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst CreateActiveThread_tran)

lemma CreateActiveThread_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: CreateActiveThread_rtran CreateActiveThread_valid)

lemma CreateActiveThread_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: CreateActiveThread_valid CreateActiveThread_NC_Space)

lemma CreateActiveThread_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using CreateActiveThread_direct_eq CreateActiveThread_NC_Space
  by auto

lemma CreateActiveThread_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:CreateActiveThread_NC_Space)

lemma CreateActiveThread_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:CreateActiveThread_NC_Space)

lemma CreateActiveThread_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
      and p2:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_Spaces_IsNot_None (CreateActiveThread SysConf s gno space scheduler pager)"
proof-
  have "space \<in> initialised_spaces s \<Longrightarrow> space_threads s space \<noteq> None"
    using p1 p2 Inv_Space_InitialSpaces_In_Spaces_def Inv_Space_Spaces_IsNot_None_def by auto
  then have "dom(space_threads (CreateActiveThread SysConf s gno space scheduler pager)) = dom (space_threads s)"
    by (auto simp add:CreateActiveThread_def CreateActiveThread_Cond_def Let_def spaces_def SetError_NC_Space)
  then show ?thesis
    using p1 Inv_Space_Spaces_IsNot_None_def CreateActiveThread_NC_Space 
    by auto
qed

lemma CreateActiveThread_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:CreateActiveThread_valid)

lemma CreateActiveThread_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Space_def
  using CreateActiveThread_Inv_Space_HasNot_Loop CreateActiveThread_Inv_Space_Valid_Has_Real
   CreateActiveThread_Inv_Space_Perms_IsNot_Empty CreateActiveThread_Inv_Space_Spaces_In_Config 
   CreateActiveThread_Inv_Space_InitialSpaces_In_Spaces CreateActiveThread_Inv_Space_Perms_Subset
   CreateActiveThread_Inv_Space_Spaces_IsNot_None CreateActiveThread_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma CreateActiveThread_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma CreateActiveThread_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma CreateActiveThread_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma CreateActiveThread_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma CreateActiveThread_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def 
    Inv_Active_In_Threads_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma CreateActiveThread_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  using assms unfolding Inv_Threads_Space_Dom_def CreateActiveThread_Cond_def
  by auto
  
lemma CreateActiveThread_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
      and p2:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(rule SetError_Inv_Threads_Space_In_Spaces)
  using p1 p2 Inv_Threads_Space_In_Spaces_def Inv_Space_InitialSpaces_In_Spaces_def
     CreateActiveThread_Cond_def
  by (auto simp:spaces_def)

lemma CreateActiveThread_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
      and p2:"Inv_NThreads_Is_None s"  
    shows "Inv_Threads_Eq_Space_Threads (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Eq_Space_Threads)
  using assms unfolding Inv_Threads_Eq_Space_Threads_def CreateActiveThread_Cond_def
    Inv_NThreads_Is_None_def
  by (auto simp:spaces_def)

lemma CreateActiveThread_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 p2 Inv_Threads_Sche_In_Threads_def Inv_Active_In_Threads_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma CreateActiveThread_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma CreateActiveThread_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
      and p2:"Inv_IntThreads_In_Active s"
      and p3:"Inv_Active_In_Threads s"
    shows "Inv_IntThreads_Utcb_Is_None (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 p2 p3 Inv_IntThreads_Utcb_Is_None_def Inv_IntThreads_In_Active_def
    Inv_Active_In_Threads_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def CreateActiveThread_Cond_def
  by auto

lemma CreateActiveThread_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
      and "Inv_Sigma0_In_Active s"
      and "Inv_Active_In_Threads s"
  shows "Inv_Sigma0_Space (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def 
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_Space)
  subgoal
    unfolding CreateActiveThread_Cond_def
    using assms Inv_Sigma0_In_Active_def Inv_Active_In_Threads_def Inv_Sigma0_Space_def
    by auto
  using assms by auto

lemma CreateActiveThread_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
      and "Inv_RootServer_In_Active s"
      and "Inv_Active_In_Threads s"
  shows "Inv_RootServer_Space (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def 
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_Space)
  subgoal
    unfolding CreateActiveThread_Cond_def
    using assms Inv_RootServer_In_Active_def Inv_Active_In_Threads_def Inv_RootServer_Space_def
    by auto
  using assms by auto

lemma CreateActiveThread_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
      and "Inv_IntThreads_In_Active s"
      and "Inv_Active_In_Threads s"
  shows "Inv_IntThreads_Space (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding CreateActiveThread_def Let_def 
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Space)
  subgoal
    unfolding CreateActiveThread_Cond_def
    using assms Inv_IntThreads_In_Active_def Inv_Active_In_Threads_def Inv_IntThreads_Space_def
    by auto
  using assms by auto

lemma CreateActiveThread_Inv_Thread:
  assumes p1:"Inv_Thread s"
      and p2:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Thread (CreateActiveThread SysConf s gno space scheduler pager)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p2 
    CreateActiveThread_Inv_Idle_NotIn_Threads CreateActiveThread_Inv_Idle_Space_Is_KernelSpace
    CreateActiveThread_Inv_Sigma0_In_Active CreateActiveThread_Inv_RootServer_In_Active 
    CreateActiveThread_Inv_IntThreads_In_Active 
    CreateActiveThread_Inv_Threads_In_Config CreateActiveThread_Inv_Active_In_Threads 
    CreateActiveThread_Inv_NThreads_Is_None CreateActiveThread_Inv_Threads_IsNot_None
    CreateActiveThread_Inv_Threads_Space_Dom CreateActiveThread_Inv_Threads_Eq_Space_Threads
    CreateActiveThread_Inv_Threads_Space_In_Spaces CreateActiveThread_Inv_Threads_Sche_In_Threads 
    CreateActiveThread_Inv_NActive_Utcb_Is_None CreateActiveThread_Inv_Active_Utcb_IsNot_None
    CreateActiveThread_Inv_IntThreads_Utcb_Is_None CreateActiveThread_Inv_Threads_Partner_In_Threads
    CreateActiveThread_Inv_Threads_Incoming_In_Threads CreateActiveThread_Inv_Sigma0_Space
    CreateActiveThread_Inv_RootServer_Space CreateActiveThread_Inv_IntThreads_Space
  by auto

lemma CreateActiveThread_Inv:
  assumes  "Invariants s"
  shows "Invariants (CreateActiveThread SysConf s gno space scheduler pager)"
  using assms Invariants_def Inv_Space_def
   CreateActiveThread_Inv_Current CreateActiveThread_Inv_Space CreateActiveThread_Inv_Thread
  by auto

section\<open>DeleteThread\<close>

subsubsection\<open>delete_temp1\<close>
lemma delete_temp1_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (delete_temp1 s gno)"
  unfolding Inv_Current_Thread_In_Active_def Let_def delete_temp1_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] Unwind_NC_Current
    Unwind_NC_Thread dequeue_ready_NC_Current dequeue_ready_NC_Thread
  by auto

lemma delete_temp1_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (delete_temp1 s gno)"
  unfolding Inv_Current_Space_IsNot_None_def Let_def delete_temp1_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] Unwind_NC_Current
    Unwind_NC_Thread dequeue_ready_NC_Current dequeue_ready_NC_Thread
  by auto

lemma delete_temp1_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (delete_temp1 s gno)"
  using delete_temp1_Inv_Current_Thread_In_Active delete_temp1_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

lemma delete_temp1_direct_eq:"(delete_temp1 s gno) \<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding delete_temp1_def
  using dequeue_ready_NC_Space Unwind_NC_Space
    direct_path_def
  by smt

lemma delete_temp1_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (delete_temp1 s gno)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(delete_temp1 s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using delete_temp1_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(delete_temp1 s gno)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(delete_temp1 s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using delete_temp1_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma delete_temp1_tran:"(delete_temp1 s gno)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using delete_temp1_direct_eq tran_path.intros delete_temp1_tran1
  by auto

lemma delete_temp1_rtran:"(delete_temp1 s gno)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using delete_temp1_tran rtran_tran
  by auto

lemma delete_temp1_valid_vpage:"(delete_temp1 s gno) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using delete_temp1_direct_eq valid_page_def
  by auto

lemma delete_temp1_valid_rpage:"(delete_temp1 s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma delete_temp1_valid:"(delete_temp1 s gno)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using delete_temp1_valid_vpage apply simp
  using delete_temp1_valid_rpage by simp

lemma delete_temp1_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (delete_temp1 s gno)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst delete_temp1_tran)

lemma delete_temp1_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (delete_temp1 s gno)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: delete_temp1_rtran delete_temp1_valid)

lemma delete_temp1_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (delete_temp1 s gno)"
  unfolding Inv_Space_Perms_IsNot_Empty_def delete_temp1_def Let_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def] 
  using delete_temp1_valid Unwind_valid dequeue_ready_valid 
    Unwind_NC_Space dequeue_ready_NC_Space
  by auto

lemma delete_temp1_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (delete_temp1 s gno)"
  unfolding Inv_Space_Perms_Subset_def delete_temp1_def Let_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using delete_temp1_valid Unwind_direct_eq dequeue_ready_direct_eq
    Unwind_NC_Space dequeue_ready_NC_Space
  by auto

lemma delete_temp1_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (delete_temp1 s gno)"
  unfolding Inv_Space_Spaces_In_Config_def delete_temp1_def Let_def get_perms_def
  using p1[unfolded Inv_Space_Spaces_In_Config_def] Unwind_NC_Space dequeue_ready_NC_Space
  by auto

lemma delete_temp1_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (delete_temp1 s gno)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def delete_temp1_def Let_def get_perms_def
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def] Unwind_NC_Space dequeue_ready_NC_Space
  by auto

lemma delete_temp1_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (delete_temp1 s gno)"
  unfolding Inv_Space_Spaces_IsNot_None_def delete_temp1_def Let_def get_perms_def
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def] Unwind_NC_Space dequeue_ready_NC_Space
  by auto

lemma delete_temp1_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (delete_temp1 s gno)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:delete_temp1_valid)

lemma delete_temp1_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (delete_temp1 s gno)"
  unfolding Inv_Space_def
  using delete_temp1_Inv_Space_HasNot_Loop delete_temp1_Inv_Space_Valid_Has_Real
   delete_temp1_Inv_Space_Perms_IsNot_Empty delete_temp1_Inv_Space_Spaces_In_Config 
   delete_temp1_Inv_Space_InitialSpaces_In_Spaces delete_temp1_Inv_Space_Perms_Subset
   delete_temp1_Inv_Space_Spaces_IsNot_None delete_temp1_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

lemma delete_temp1_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (delete_temp1 s gno)"
  using assms unfolding Inv_Idle_NotIn_Threads_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (delete_temp1 s gno)"
  using assms unfolding Inv_Idle_Space_Is_KernelSpace_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (delete_temp1 s gno)"
  using assms unfolding Inv_Sigma0_In_Active_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (delete_temp1 s gno)"
  using assms unfolding Inv_RootServer_In_Active_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (delete_temp1 s gno)"
  using assms unfolding Inv_IntThreads_In_Active_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (delete_temp1 s gno)"
  using assms unfolding Inv_Threads_In_Config_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (delete_temp1 s gno)"
  using assms unfolding Inv_Active_In_Threads_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
      and "Inv_Active_In_Threads s"
      and "Inv_Threads_Partner_In_Threads s"
    shows "Inv_NThreads_Is_None (delete_temp1 s gno)"
  unfolding delete_temp1_def Let_def
  apply(rule elim_if)
  subgoal
    apply(rule elim_if)
    subgoal
      apply(rule Unwind_Inv_NThreads_Is_None)
      using assms dequeue_ready_def Inv_Active_In_Threads_def
        Inv_NThreads_Is_None_def Inv_Threads_Partner_In_Threads_def
      by auto
    using assms Inv_NThreads_Is_None_def dequeue_ready_def
    by auto
  using assms by simp

lemma delete_temp1_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
      and "Inv_Active_In_Threads s"
      and "Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_IsNot_None (delete_temp1 s gno)"
  unfolding delete_temp1_def Let_def
  apply(rule elim_if)
  subgoal
    apply(rule elim_if)
    subgoal
      apply(rule Unwind_Inv_Threads_IsNot_None)
      using assms dequeue_ready_def Inv_Active_In_Threads_def
        Inv_Threads_IsNot_None_def Inv_Threads_Partner_In_Threads_def
      by auto
    using assms Inv_Threads_IsNot_None_def dequeue_ready_def
    by auto
  using assms by simp

lemma delete_temp1_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (delete_temp1 s gno)"
  using assms unfolding Inv_Threads_Space_Dom_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread dequeue_ready_NC_Space Unwind_NC_Thread Unwind_NC_Space
  by auto

thm Unwind_Inv_Threads_IsNot_None
lemma delete_temp1_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (delete_temp1 s gno)"
  using assms unfolding Inv_Threads_Space_In_Spaces_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread dequeue_ready_NC_Space Unwind_NC_Thread Unwind_NC_Space
  by auto

lemma delete_temp1_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (delete_temp1 s gno)"
  using assms unfolding Inv_Threads_Sche_In_Threads_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (delete_temp1 s gno)"
  using assms unfolding Inv_NActive_Utcb_Is_None_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread dequeue_ready_NC_User dequeue_ready_NC_IPC
    Unwind_NC_Thread Unwind_NC_User Unwind_NC_IPC
  by auto

lemma delete_temp1_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (delete_temp1 s gno)"
  using assms unfolding Inv_Active_Utcb_IsNot_None_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread dequeue_ready_NC_User dequeue_ready_NC_IPC
    Unwind_NC_Thread Unwind_NC_User Unwind_NC_IPC
  by auto

lemma delete_temp1_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (delete_temp1 s gno)"
  using assms unfolding Inv_IntThreads_Utcb_Is_None_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread dequeue_ready_NC_User dequeue_ready_NC_IPC
    Unwind_NC_Thread Unwind_NC_User Unwind_NC_IPC
  by auto

lemma delete_temp1_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (delete_temp1 s gno)"
  using assms unfolding Inv_Threads_Partner_In_Threads_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread dequeue_ready_NC_User dequeue_ready_NC_IPC
    Unwind_NC_Thread Unwind_NC_User Unwind_NC_IPC
  by auto

lemma delete_temp1_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
      and "Inv_Active_In_Threads s"
      and "Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (delete_temp1 s gno)"
  unfolding delete_temp1_def Let_def
  apply(rule elim_if)
  subgoal
    apply(rule elim_if)
    subgoal
      apply(rule Unwind_Inv_Threads_Incoming_In_Threads)
      using assms dequeue_ready_def Inv_Active_In_Threads_def
        Inv_Threads_Incoming_In_Threads_def Inv_Threads_Partner_In_Threads_def
      by auto
    using assms Inv_Threads_Incoming_In_Threads_def dequeue_ready_def
    by auto
  using assms by simp

lemma delete_temp1_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (delete_temp1 s gno)"
  using assms unfolding Inv_Sigma0_Space_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (delete_temp1 s gno)"
  using assms unfolding Inv_RootServer_Space_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

lemma delete_temp1_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (delete_temp1 s gno)"
  using assms unfolding Inv_IntThreads_Space_def delete_temp1_def Let_def
  using dequeue_ready_NC_Thread Unwind_NC_Thread
  by auto

subsubsection\<open>delete_temp2\<close>
lemma delete_temp2_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (delete_temp2 s gno)"
  using assms unfolding Inv_Current_Thread_In_Active_def Let_def delete_temp2_def
  using DeleteAddressSpace_NC_Current DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (delete_temp2 s gno)"
  using assms unfolding Inv_Current_Space_IsNot_None_def Let_def delete_temp2_def
  using DeleteAddressSpace_NC_Current DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (delete_temp2 s gno)"
  using delete_temp2_Inv_Current_Thread_In_Active delete_temp2_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

lemma delete_temp2_direct_eq:"(delete_temp2 s gno)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding delete_temp2_def Let_def
  apply(cases "the (space_threads s (the (thread_space s gno))) = {gno}")
  subgoal
    using DeleteAddressSpace_direct_eq
    by simp
  unfolding direct_path_def
  by simp

lemma delete_temp2_tran:"(delete_temp2 s gno)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(induct rule: tran_path.induct)
  using delete_temp2_direct_eq tran_path.intros
  by blast+

lemma delete_temp2_rtran:"(delete_temp2 s gno)\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>*y"
  using delete_temp2_tran rtran_tran
  by auto

lemma delete_temp2_valid_vpage:"(delete_temp2 s gno) \<turnstile> (Virtual sp1 v_page) \<Longrightarrow> s \<turnstile> (Virtual sp1 v_page)"
  using delete_temp2_direct_eq ValidVpageHasSon by blast

lemma delete_temp2_valid_rpage:"(delete_temp2 s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma delete_temp2_valid:"(delete_temp2 s gno)\<turnstile> x \<Longrightarrow> s\<turnstile>x"
  apply (case_tac x)
  using delete_temp2_valid_vpage apply simp
  using delete_temp2_valid_rpage by simp

lemma delete_temp2_branch1_direct_eq:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding direct_path_def
  by simp

lemma delete_temp2_branch1_tran1:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>x\<leadsto>\<^sup>1y"
    using delete_temp2_branch1_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>x\<leadsto>\<^sup>1y"
    using delete_temp2_branch1_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed

lemma delete_temp2_branch1_tran:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
  apply(induct rule: tran_path.induct)
  using delete_temp2_branch1_direct_eq tran_path.intros delete_temp2_branch1_tran1
  by blast+

lemma delete_temp2_branch1_rtran:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using delete_temp2_branch1_tran rtran_tran
  by metis

lemma delete_temp2_branch1_valid_vpage:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using delete_temp2_branch1_direct_eq ValidVpageHasSon by blast

lemma delete_temp2_branch1_valid_rpage:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma delete_temp2_branch1_valid:"(s\<lparr>space_threads := space_threads s(space \<mapsto>
                         the (space_threads s space) - {gno})\<rparr>)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using delete_temp2_branch1_valid_vpage apply simp
  using delete_temp2_branch1_valid_rpage by simp


lemma delete_temp2_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (delete_temp2 s gno)"
  using assms unfolding Inv_Space_HasNot_Loop_def
  using delete_temp2_tran
  by metis

lemma delete_temp2_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
      and "Inv_Space_Perms_Subset s"
      and "Inv_Space_HasNot_Loop s "
      and "Inv_Space_Vpage_Range s"
  shows "Inv_Space_Valid_Has_Real (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def
  apply(rule elim_if)
  subgoal
    using assms DeleteAddressSpace_Inv_Space_Valid_Has_Real
    by simp
  using p1 unfolding Inv_Space_Valid_Has_Real_def
  apply(subst delete_temp2_branch1_valid)
  apply(subst delete_temp2_branch1_rtran)
  by auto

lemma delete_temp2_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def
  apply(rule elim_if)
  subgoal
    using assms DeleteAddressSpace_Inv_Space_Perms_IsNot_Empty
    by simp
  using p1 unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  apply(subst delete_temp2_branch1_valid)
  by auto

lemma delete_temp2_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and "Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s \<and> Inv_Space_Vpage_Range s"
  shows "Inv_Space_Perms_Subset (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def
  apply(rule elim_if)
  subgoal
    using assms DeleteAddressSpace_Inv_Space_Perms_Subset
    by simp
  using p1 unfolding Inv_Space_Perms_Subset_def get_perms_def
  apply(subst delete_temp2_branch1_direct_eq)
  by auto

lemma delete_temp2_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def
  apply(rule elim_if)
  subgoal
    using assms DeleteAddressSpace_Inv_Space_Spaces_In_Config
    by simp
  using p1 unfolding Inv_Space_Spaces_In_Config_def spaces_def
  by auto

lemma delete_temp2_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def
  apply(rule elim_if)
  subgoal
    using assms DeleteAddressSpace_Inv_Space_InitialSpaces_In_Spaces
    by simp
  using p1 unfolding Inv_Space_InitialSpaces_In_Spaces_def spaces_def
  by auto

lemma delete_temp2_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
      and "Inv_Threads_Space_In_Spaces s"
      and "gno \<in> threads s"
    shows "Inv_Space_Spaces_IsNot_None (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def
  apply(rule elim_if)
  subgoal
    using assms DeleteAddressSpace_Inv_Space_Spaces_IsNot_None
    by simp
  using assms unfolding Inv_Space_Spaces_IsNot_None_def spaces_def
    Inv_Threads_Space_In_Spaces_def
  by auto

lemma delete_temp2_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (delete_temp2 s gno)"
  using assms unfolding Inv_Space_Vpage_Range_def 
  using delete_temp2_valid
  by blast

lemma delete_temp2_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (delete_temp2 s gno)"
  using assms unfolding Inv_Idle_NotIn_Threads_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (delete_temp2 s gno)"
  using assms unfolding Inv_Idle_Space_Is_KernelSpace_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (delete_temp2 s gno)"
  using assms unfolding Inv_Sigma0_In_Active_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (delete_temp2 s gno)"
  using assms unfolding Inv_RootServer_In_Active_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (delete_temp2 s gno)"
  using assms unfolding Inv_IntThreads_In_Active_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (delete_temp2 s gno)"
  using assms unfolding Inv_Threads_In_Config_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (delete_temp2 s gno)"
  using assms unfolding Inv_Active_In_Threads_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp2_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (delete_temp2 s gno)"
  using assms unfolding Inv_NThreads_Is_None_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (delete_temp2 s gno)"
  using assms unfolding Inv_Threads_IsNot_None_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (delete_temp2 s gno)"
  using assms unfolding Inv_Threads_Space_Dom_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User
  by auto

lemma delete_temp2_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (delete_temp2 s gno)"
  using assms unfolding Inv_Threads_Sche_In_Threads_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (delete_temp2 s gno)"
  using assms unfolding Inv_NActive_Utcb_Is_None_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (delete_temp2 s gno)"
  using assms unfolding Inv_Active_Utcb_IsNot_None_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (delete_temp2 s gno)"
  using assms unfolding Inv_IntThreads_Utcb_Is_None_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (delete_temp2 s gno)"
  using assms unfolding Inv_Threads_Partner_In_Threads_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (delete_temp2 s gno)"
  using assms unfolding Inv_Threads_Incoming_In_Threads_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (delete_temp2 s gno)"
  using assms unfolding Inv_Sigma0_Space_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (delete_temp2 s gno)"
  using assms unfolding Inv_RootServer_Space_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

lemma delete_temp2_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (delete_temp2 s gno)"
  using assms unfolding Inv_IntThreads_Space_def delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_User DeleteAddressSpace_NC_IPC
  by auto

subsubsection\<open>delete_temp3\<close>
lemma delete_temp3_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    and p2:"gno \<noteq> current_thread s"
    shows "Inv_Current_Thread_In_Active (delete_temp3 s gno)"
  using assms unfolding Inv_Current_Thread_In_Active_def Let_def delete_temp3_def
  by auto

lemma delete_temp3_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    and   p2:"gno \<noteq> current_thread s"
    shows "Inv_Current_Space_IsNot_None (delete_temp3 s gno)"
  using assms unfolding Inv_Current_Space_IsNot_None_def Let_def delete_temp3_def
  by auto

lemma delete_temp3_Inv_Current:
  assumes p1:"Inv_Current s"
    and   p2:"gno \<noteq> current_thread s"
    shows "Inv_Current (delete_temp3 s gno)"
  using delete_temp3_Inv_Current_Thread_In_Active delete_temp3_Inv_Current_Space_IsNot_None
    Inv_Current_def p1 p2
  by auto

lemma delete_temp3_direct_eq:"(delete_temp3 s gno) \<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding delete_temp3_def direct_path_def
  by simp

lemma delete_temp3_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (delete_temp3 s gno)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(delete_temp3 s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using delete_temp3_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(delete_temp3 s gno)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(delete_temp3 s gno)\<turnstile>x\<leadsto>\<^sup>1y"
    using delete_temp3_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma delete_temp3_tran:"(delete_temp3 s gno)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using delete_temp3_direct_eq tran_path.intros delete_temp3_tran1
  by auto

lemma delete_temp3_rtran:"(delete_temp3 s gno)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using delete_temp3_tran rtran_tran
  by auto

lemma delete_temp3_valid_vpage:"(delete_temp3 s gno) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using delete_temp3_direct_eq ValidVpageHasSon by blast

lemma delete_temp3_valid_rpage:"(delete_temp3 s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma delete_temp3_valid:"(delete_temp3 s gno)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using delete_temp3_valid_vpage apply simp
  using delete_temp3_valid_rpage by simp

lemma delete_temp3_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (delete_temp3 s gno)"
  using assms unfolding Inv_Space_HasNot_Loop_def
  using delete_temp3_tran
  by metis

lemma delete_temp3_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
  shows "Inv_Space_Valid_Has_Real (delete_temp3 s gno)"
  using assms unfolding Inv_Space_Valid_Has_Real_def
  using delete_temp3_rtran delete_temp3_valid
  by auto

lemma delete_temp3_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (delete_temp3 s gno)"
  using assms unfolding Inv_Space_Perms_IsNot_Empty_def
  apply(auto simp: delete_temp3_valid)
  unfolding get_perms_def delete_temp3_def
  by auto

lemma delete_temp3_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (delete_temp3 s gno)"
  using assms unfolding Inv_Space_Perms_Subset_def
  apply(auto simp add: delete_temp3_direct_eq)
  apply(subgoal_tac "space_mapping (delete_temp3 s gno) = space_mapping s")
  subgoal
    unfolding get_perms_def
    by (simp add: subset_iff)
  unfolding delete_temp3_def by simp

lemma delete_temp3_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (delete_temp3 s gno)"
  using assms unfolding Inv_Space_Spaces_In_Config_def
  by (auto simp:delete_temp3_def spaces_def)

lemma delete_temp3_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (delete_temp3 s gno)"
  using assms unfolding Inv_Space_InitialSpaces_In_Spaces_def
  by (auto simp:delete_temp3_def spaces_def)

lemma delete_temp3_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (delete_temp3 s gno)"
  using assms unfolding Inv_Space_Spaces_IsNot_None_def
  by (auto simp:delete_temp3_def spaces_def)

lemma delete_temp3_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (delete_temp3 s gno)"
  using assms unfolding Inv_Space_Vpage_Range_def 
  using delete_temp3_valid
  by blast

lemma delete_temp3_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (delete_temp3 s gno)"
  unfolding Inv_Space_def
  using delete_temp3_Inv_Space_HasNot_Loop delete_temp3_Inv_Space_Valid_Has_Real
   delete_temp3_Inv_Space_Perms_IsNot_Empty delete_temp3_Inv_Space_Spaces_In_Config 
   delete_temp3_Inv_Space_InitialSpaces_In_Spaces delete_temp3_Inv_Space_Perms_Subset
   delete_temp3_Inv_Space_Spaces_IsNot_None delete_temp3_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

lemma delete_temp3_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (delete_temp3 s gno)"
  using assms unfolding Inv_Idle_NotIn_Threads_def delete_temp3_def Let_def
  using DeleteAddressSpace_NC_Thread
  by auto

lemma delete_temp3_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    and "gno \<noteq> idle"
    shows "Inv_Idle_Space_Is_KernelSpace (delete_temp3 s gno)"
  using assms unfolding Inv_Idle_Space_Is_KernelSpace_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    and "gno \<noteq> kSigma0"
      shows "Inv_Sigma0_In_Active (delete_temp3 s gno)"
  using assms unfolding Inv_Sigma0_In_Active_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    and "gno \<noteq> kRootServer"
    shows "Inv_RootServer_In_Active (delete_temp3 s gno)"
  using assms unfolding Inv_RootServer_In_Active_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
      and "gno \<notin> kIntThreads"
    shows "Inv_IntThreads_In_Active (delete_temp3 s gno)"
  using assms unfolding Inv_IntThreads_In_Active_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_In_Config_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (delete_temp3 s gno)"
  using assms unfolding Inv_Active_In_Threads_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (delete_temp3 s gno)"
  using assms unfolding Inv_NThreads_Is_None_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_IsNot_None_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_Space_Dom_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_Space_In_Spaces_def spaces_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
     and "\<forall>t. t \<in> threads s \<longrightarrow> thread_scheduler s t \<noteq> Some gno"
     (*\<nexists>t. t \<in> threads s \<and> thread_scheduler s t = Some gno*)
    shows "Inv_Threads_Sche_In_Threads (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_Sche_In_Threads_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (delete_temp3 s gno)"
  using assms unfolding Inv_NActive_Utcb_Is_None_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (delete_temp3 s gno)"
  using assms unfolding Inv_Active_Utcb_IsNot_None_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (delete_temp3 s gno)"
  using assms unfolding Inv_IntThreads_Utcb_Is_None_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Threads_Partner_In_Threads:
  assumes p0:"Inv_Threads_Partner_In_Threads s"
    and "\<forall>t. t \<in> threads s \<longrightarrow> thread_ipc_partner s t \<noteq> Some (GnoToTid gno)"
    shows "Inv_Threads_Partner_In_Threads (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_Partner_In_Threads_def delete_temp3_def Let_def
    GnoToTid_def
  apply auto
  using threadid_t.exhaust_sel by force

lemma delete_temp3_Inv_Threads_Incoming_In_Threads:
  assumes p0:"Inv_Threads_Incoming_In_Threads s"
    and "\<forall>t. t \<in> threads s \<longrightarrow> (gno \<notin> set (the (thread_incoming s t)))"
    shows "Inv_Threads_Incoming_In_Threads (delete_temp3 s gno)"
  using assms unfolding Inv_Threads_Incoming_In_Threads_def delete_temp3_def Let_def
  by fastforce

lemma delete_temp3_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
      and "gno \<noteq> kSigma0"
  shows "Inv_Sigma0_Space (delete_temp3 s gno)"
  using assms unfolding Inv_Sigma0_Space_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
      and "gno \<noteq> kRootServer"
  shows "Inv_RootServer_Space (delete_temp3 s gno)"
  using assms unfolding Inv_RootServer_Space_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
      and "gno \<notin> kIntThreads"
  shows "Inv_IntThreads_Space (delete_temp3 s gno)"
  using assms unfolding Inv_IntThreads_Space_def delete_temp3_def Let_def
  by auto

lemma delete_temp3_Inv_Thread:
  assumes p1:"Inv_Thread s"
      and "gno \<noteq> kSigma0 \<and> gno \<noteq> kRootServer \<and> gno \<notin> kIntThreads"
    shows "Inv_Thread (delete_temp3 s gno)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] p1
    delete_temp3_Inv_Idle_NotIn_Threads delete_temp3_Inv_Idle_Space_Is_KernelSpace
    delete_temp3_Inv_Sigma0_In_Active delete_temp3_Inv_RootServer_In_Active 
    delete_temp3_Inv_IntThreads_In_Active 
    delete_temp3_Inv_Threads_In_Config delete_temp3_Inv_Active_In_Threads 
    delete_temp3_Inv_NThreads_Is_None delete_temp3_Inv_Threads_IsNot_None 
    delete_temp3_Inv_Threads_Space_In_Spaces delete_temp3_Inv_Threads_Sche_In_Threads 
    delete_temp3_Inv_NActive_Utcb_Is_None delete_temp3_Inv_Active_Utcb_IsNot_None
    delete_temp3_Inv_IntThreads_Utcb_Is_None delete_temp3_Inv_Sigma0_Space
    delete_temp3_Inv_RootServer_Space delete_temp3_Inv_IntThreads_Space
    delete_temp3_Inv_Threads_Partner_In_Threads delete_temp3_Inv_Threads_Incoming_In_Threads
  oops

subsection\<open>Current\<close>
lemma DeleteThread_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
  shows "Inv_Current_Thread_In_Active (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Current_Thread_In_Active)
    apply(rule delete_temp3_Inv_Current_Thread_In_Active)
    apply(rule delete_temp2_Inv_Current_Thread_In_Active)
    apply(rule delete_temp1_Inv_Current_Thread_In_Active)
    using assms apply simp
    unfolding DeleteThread_Cond_def delete_temp2_def delete_temp1_def Let_def
    using DeleteAddressSpace_NC_Current Unwind_NC_Current dequeue_ready_NC_Current
    by auto
  using assms by simp

lemma DeleteThread_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Current_Space_IsNot_None)
    apply(rule delete_temp3_Inv_Current_Space_IsNot_None)
    apply(rule delete_temp2_Inv_Current_Space_IsNot_None)
    apply(rule delete_temp1_Inv_Current_Space_IsNot_None)
    using assms apply simp
    unfolding DeleteThread_Cond_def delete_temp2_def delete_temp1_def Let_def
    using DeleteAddressSpace_NC_Current Unwind_NC_Current dequeue_ready_NC_Current
    by auto
  using assms by simp

lemma DeleteThread_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (DeleteThread s gno)"
  using DeleteThread_Inv_Current_Thread_In_Active DeleteThread_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma DeleteThread_direct_eq:"(DeleteThread s gno)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  apply(simp add: DeleteThread_eq)
  using SetError_direct_eq delete_temp1_direct_eq delete_temp2_direct_eq delete_temp3_direct_eq
  by (metis (full_types))
  
lemma DeleteThread_tran:"(DeleteThread s gno)\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(induct rule: tran_path.induct)
  using DeleteThread_direct_eq tran_path.intros
  by blast+

lemma DeleteThread_rtran:"(DeleteThread s gno)\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>*y"
  using DeleteThread_tran rtran_tran
  by auto

lemma DeleteThread_valid_vpage:
"(DeleteThread s gno) \<turnstile> (Virtual sp1 v_page) \<Longrightarrow> s \<turnstile> (Virtual sp1 v_page)"
  using DeleteThread_direct_eq valid_page_def
  by (meson ValidVpageHasSon)

lemma DeleteThread_valid_rpage:"(DeleteThread s gno)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma DeleteThread_valid:"(DeleteThread s gno)\<turnstile> x \<Longrightarrow> s\<turnstile>x"
  using DeleteThread_valid_vpage DeleteThread_valid_rpage FatherIsVirtual ValidExSon
  by fastforce

lemma DeleteThread_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (DeleteThread s gno)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def] DeleteThread_tran
  by blast

lemma DeleteThread_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
      and "Inv_Space_Perms_Subset s"
      and "Inv_Space_HasNot_Loop s "
      and "Inv_Space_Vpage_Range s"
    shows "Inv_Space_Valid_Has_Real (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Valid_Has_Real)
    apply(rule delete_temp3_Inv_Space_Valid_Has_Real)
    apply(rule delete_temp2_Inv_Space_Valid_Has_Real)
    apply(rule delete_temp1_Inv_Space_Valid_Has_Real)
    using assms apply simp
      apply(rule delete_temp1_Inv_Space_Perms_Subset)
    using assms apply simp
     apply(rule delete_temp1_Inv_Space_HasNot_Loop)
    using assms apply simp
    apply(rule delete_temp1_Inv_Space_Vpage_Range)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Perms_IsNot_Empty)
    apply(rule delete_temp3_Inv_Space_Perms_IsNot_Empty)
    apply(rule delete_temp2_Inv_Space_Perms_IsNot_Empty)
    apply(rule delete_temp1_Inv_Space_Perms_IsNot_Empty)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and "Inv_Space_HasNot_Loop s "
      and "Inv_Space_Vpage_Range s"
      and "Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Perms_Subset (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Perms_Subset)
    apply(rule delete_temp3_Inv_Space_Perms_Subset)
    apply(rule delete_temp2_Inv_Space_Perms_Subset)
    apply(rule delete_temp1_Inv_Space_Perms_Subset)
    using assms apply auto
      apply(rule delete_temp1_Inv_Space_HasNot_Loop)
      apply simp
     apply(rule delete_temp1_Inv_Space_Valid_Has_Real)
     apply simp
    apply(rule delete_temp1_Inv_Space_Vpage_Range)
    by simp
  using assms by simp

lemma DeleteThread_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Spaces_In_Config)
    apply(rule delete_temp3_Inv_Space_Spaces_In_Config)
    apply(rule delete_temp2_Inv_Space_Spaces_In_Config)
    apply(rule delete_temp1_Inv_Space_Spaces_In_Config)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_InitialSpaces_In_Spaces)
    apply(rule delete_temp3_Inv_Space_InitialSpaces_In_Spaces)
    apply(rule delete_temp2_Inv_Space_InitialSpaces_In_Spaces)
    apply(rule delete_temp1_Inv_Space_InitialSpaces_In_Spaces)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
      and "Inv_Threads_Space_In_Spaces s"
    shows "Inv_Space_Spaces_IsNot_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Spaces_IsNot_None)
    apply(rule delete_temp3_Inv_Space_Spaces_IsNot_None)
    apply(rule delete_temp2_Inv_Space_Spaces_IsNot_None)
    apply(rule delete_temp1_Inv_Space_Spaces_IsNot_None)
    using assms apply auto
     apply(rule delete_temp1_Inv_Threads_Space_In_Spaces)
     apply simp
    unfolding delete_temp1_def dequeue_ready_def Let_def DeleteThread_Cond_def
    using Unwind_NC_Thread
    by auto
  using assms by simp

lemma DeleteThread_Inv_Space_Vpage_Range:
  assumes "Inv_Space_Vpage_Range s"
  shows "Inv_Space_Vpage_Range (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Vpage_Range)
    apply(rule delete_temp3_Inv_Space_Vpage_Range)
    apply(rule delete_temp2_Inv_Space_Vpage_Range)
    apply(rule delete_temp1_Inv_Space_Vpage_Range)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Space:
  assumes p1:"Inv_Space s"
      and "Inv_Threads_Space_In_Spaces s"
    shows "Inv_Space (DeleteThread s gno)"
  using assms unfolding Inv_Space_def
  using DeleteThread_Inv_Space_HasNot_Loop DeleteThread_Inv_Space_Valid_Has_Real
    DeleteThread_Inv_Space_Perms_IsNot_Empty DeleteThread_Inv_Space_Spaces_In_Config
    DeleteThread_Inv_Space_InitialSpaces_In_Spaces DeleteThread_Inv_Space_Perms_Subset
    DeleteThread_Inv_Space_Spaces_IsNot_None DeleteThread_Inv_Space_Vpage_Range
  by auto

subsection\<open>Thread\<close>
lemma DeleteThread_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (DeleteThread s gno)"
   apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Idle_NotIn_Threads)
    apply(rule delete_temp3_Inv_Idle_NotIn_Threads)
    apply(rule delete_temp2_Inv_Idle_NotIn_Threads)
    apply(rule delete_temp1_Inv_Idle_NotIn_Threads)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (DeleteThread s gno)"
   apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Idle_Space_Is_KernelSpace)
    apply(rule delete_temp3_Inv_Idle_Space_Is_KernelSpace)
    apply(rule delete_temp2_Inv_Idle_Space_Is_KernelSpace)
    apply(rule delete_temp1_Inv_Idle_Space_Is_KernelSpace)
    using assms apply simp
    using assms unfolding Inv_Idle_Space_Is_KernelSpace_def DeleteThread_Cond_def 
    by metis
  using assms by simp

lemma DeleteThread_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      and "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_In_Active (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Sigma0_In_Active)
    apply(rule delete_temp3_Inv_Sigma0_In_Active)
    apply(rule delete_temp2_Inv_Sigma0_In_Active)
    apply(rule delete_temp1_Inv_Sigma0_In_Active)
    using assms apply auto
    unfolding DeleteThread_Cond_def Inv_Sigma0_Space_def
    by simp
  using assms by simp

lemma DeleteThread_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
      and "Inv_RootServer_Space s"
    shows "Inv_RootServer_In_Active (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_RootServer_In_Active)
    apply(rule delete_temp3_Inv_RootServer_In_Active)
    apply(rule delete_temp2_Inv_RootServer_In_Active)
    apply(rule delete_temp1_Inv_RootServer_In_Active)
    using assms apply auto
    unfolding DeleteThread_Cond_def Inv_RootServer_Space_def
    by simp
  using assms by simp

lemma DeleteThread_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
      and "Inv_IntThreads_Space s"
    shows "Inv_IntThreads_In_Active (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_IntThreads_In_Active)
    apply(rule delete_temp3_Inv_IntThreads_In_Active)
    apply(rule delete_temp2_Inv_IntThreads_In_Active)
    apply(rule delete_temp1_Inv_IntThreads_In_Active)
    using assms apply auto
    unfolding DeleteThread_Cond_def Inv_IntThreads_Space_def
    by simp
  using assms by simp

lemma DeleteThread_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_In_Config)
    apply(rule delete_temp3_Inv_Threads_In_Config)
    apply(rule delete_temp2_Inv_Threads_In_Config)
    apply(rule delete_temp1_Inv_Threads_In_Config)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Active_In_Threads)
    apply(rule delete_temp3_Inv_Active_In_Threads)
    apply(rule delete_temp2_Inv_Active_In_Threads)
    apply(rule delete_temp1_Inv_Active_In_Threads)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
      and p3:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_NThreads_Is_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_NThreads_Is_None)
    apply(rule delete_temp3_Inv_NThreads_Is_None)
    apply(rule delete_temp2_Inv_NThreads_Is_None)
    apply(rule delete_temp1_Inv_NThreads_Is_None)
    using assms apply auto 
    by (simp add: delete_temp1_Inv_Active_In_Threads delete_temp2_Inv_Active_In_Threads delete_temp3_Inv_Active_In_Threads)
  using assms by simp

lemma DeleteThread_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
      and "Inv_Active_In_Threads s"
      and "Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_IsNot_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_IsNot_None)
    apply(rule delete_temp3_Inv_Threads_IsNot_None)
    apply(rule delete_temp2_Inv_Threads_IsNot_None)
    apply(rule delete_temp1_Inv_Threads_IsNot_None)
    using assms by auto 
  using assms by simp

lemma delete_temp1_NC_Space:
"spaces (delete_temp1 s gno) = spaces s \<and>
 space_threads (delete_temp1 s gno) = space_threads s"
  unfolding delete_temp1_def Let_def
  using Unwind_NC_Space dequeue_ready_NC_Space by simp

lemma delete_temp1_NC_Thread:
"threads (delete_temp1 s gno) = threads s \<and>
 thread_space (delete_temp1 s gno) = thread_space s"
  unfolding delete_temp1_def Let_def
  using Unwind_NC_Thread dequeue_ready_NC_Thread by simp

lemma DeleteAddressSpace_NC_Space_Pre:
"space \<in> spaces (DeleteAddressSpace s sp) \<Longrightarrow> space \<in> spaces s"
  unfolding DeleteAddressSpace_def Let_def
  apply(cases "sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp")
   apply(auto simp:spaces_def)
  using Unmap_fpage_NC_Space
   apply blast
  by (smt domD domIff)

lemma delete_temp2_NC_Space_Pre:
"space \<in> spaces (delete_temp2 s gno) \<Longrightarrow> space \<in> spaces s"
  unfolding delete_temp2_def Let_def
  apply (cases "the (space_threads s (the (thread_space s gno))) = {gno}")
  by (auto simp:DeleteAddressSpace_NC_Space_Pre[unfolded spaces_def] spaces_def)

lemma delete_temp2_C_Space:
"the (space_threads s (the (thread_space s gno))) = {gno} \<Longrightarrow> 
the (thread_space s gno) \<in> spaces s \<Longrightarrow> \<not>dIsPrivilegedSpace(the (thread_space s gno)) \<Longrightarrow> 
  the (thread_space s gno) \<notin> spaces (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def spaces_def DeleteAddressSpace_def
  by simp

lemma delete_temp2_NC_Space_Other:
"the (space_threads s (the (thread_space s gno))) = {gno} \<Longrightarrow>
space \<in> spaces s \<Longrightarrow> space \<noteq> the (thread_space s gno) \<Longrightarrow>
space \<in> spaces (delete_temp2 s gno)"
  unfolding delete_temp2_def Let_def DeleteAddressSpace_def spaces_def
  using Unmap_fpage_NC_Space2
  by(auto simp:spaces_def)

lemma delete_temp2_NC_Space_Threads_Other:
"the (thread_space s gno) \<noteq> space \<Longrightarrow>
space_threads (delete_temp2 s gno) space = space_threads s space"
  unfolding delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Space_Other
  by auto

lemma delete_temp2_NC_Space:
"the (space_threads s (the (thread_space s gno))) \<noteq> {gno} \<Longrightarrow>
spaces (delete_temp2 s gno) = spaces s"
  unfolding delete_temp2_def Let_def spaces_def
  by simp

lemma delete_temp2_NC_Thread:
"threads (delete_temp2 s gno) = threads s \<and>
 thread_space (delete_temp2 s gno) = thread_space s"
  unfolding delete_temp2_def Let_def
  using DeleteAddressSpace_NC_Thread by simp

lemma delete_temp3_NC_Space:
"spaces (delete_temp3 s gno) = spaces s \<and>
 space_threads (delete_temp3 s gno) = space_threads s"
  unfolding delete_temp3_def Let_def spaces_def
  by simp

lemma delete_temp3_NC_Thread_Other:
"x \<noteq> gno \<Longrightarrow> thread_space (delete_temp3 s gno) x = thread_space s x"
  unfolding delete_temp3_def Let_def
  by simp

lemma DeleteThread_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
  shows "Inv_Threads_Space_Dom (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Space_Dom)
    apply(rule delete_temp3_Inv_Threads_Space_Dom)
    apply(rule delete_temp2_Inv_Threads_Space_Dom)
    apply(rule delete_temp1_Inv_Threads_Space_Dom)
    using assms by simp
  using assms by simp

lemma DeleteThread_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
      and p2:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Space_In_Spaces (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Space_In_Spaces)
    unfolding Inv_Threads_Space_In_Spaces_def
    apply rule apply rule
  proof-
    fix t
    assume a1:"DeleteThread_Cond s gno" and 
      a2:"t \<in> threads (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno)"
    then have h1:"t \<noteq> gno"
      unfolding delete_temp3_def by auto
    have h2:"t \<in> threads (delete_temp2 (delete_temp1 s gno) gno)"
      using a2[unfolded delete_temp3_def] by auto
    then have h21:"t \<in> threads (delete_temp1 s gno)" using delete_temp2_NC_Thread by auto
    then have h22:"t \<in> threads s" using delete_temp1_NC_Thread by simp
    then have h3:"\<exists>space. space \<in> spaces s \<and> thread_space s t = Some space"
      using p1[unfolded Inv_Threads_Space_In_Spaces_def] by simp
    then obtain space where h31:"space \<in> spaces s \<and> thread_space s t = Some space"
      by auto
    then have h32:"space \<in> spaces (delete_temp1 s gno) \<and> thread_space (delete_temp1 s gno) t = Some space"
      using delete_temp1_NC_Space delete_temp1_NC_Thread by simp
    have h33:"the (space_threads (delete_temp1 s gno) (the (thread_space (delete_temp1 s gno) gno))) = {gno} \<Longrightarrow>
        space \<noteq> the (thread_space (delete_temp1 s gno) gno)"
      apply(auto simp: delete_temp1_NC_Space delete_temp1_NC_Thread)
      using p2[unfolded Inv_Threads_Eq_Space_Threads_def] h1 h31 by auto
    then have h34:"space \<in> spaces (delete_temp2 (delete_temp1 s gno) gno)"
      using h32 delete_temp2_NC_Space_Other delete_temp2_NC_Space by blast
    have h35:"thread_space (delete_temp2 (delete_temp1 s gno) gno) t = Some space"
      using h32 delete_temp2_NC_Thread by simp
    have h41:"space \<in> spaces (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno)"
      using h34 delete_temp3_NC_Space by auto
    have h42:"thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space"
      using h35 h1
      by (simp add: delete_temp3_NC_Thread_Other)
    then show "\<exists>space.
            space \<in> spaces (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) \<and>
            thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space"
      using h41 by simp
  qed
  using assms by simp

lemma DeleteThread_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
      and p2:"Inv_Threads_Space_In_Spaces s"
  shows "Inv_Threads_Eq_Space_Threads (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Eq_Space_Threads)
    unfolding Inv_Threads_Eq_Space_Threads_def
    apply rule apply rule
  proof-
    fix space
    assume a1:"DeleteThread_Cond s gno" 
      and a2:"space \<in> spaces (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno)"
    then have h1:"space \<in> spaces s \<and> space \<in> spaces (delete_temp2 (delete_temp1 s gno) gno)" 
      using delete_temp3_NC_Space delete_temp2_NC_Space_Pre delete_temp1_NC_Space by blast
    then have h11:"the (space_threads s space) = {t. thread_space s t = Some space}"
      using p1[unfolded Inv_Threads_Eq_Space_Threads_def] by simp
    have h2:"the (thread_space s gno) \<in> spaces s" using a1[unfolded DeleteThread_Cond_def]
        p2[unfolded Inv_Threads_Space_In_Spaces_def] by auto
    have h3:"\<not>dIsPrivilegedSpace (the (thread_space s gno))" unfolding dIsPrivilegedSpace_def
      is_kSigma0Space_def is_kRootServerSpace_def using a1[unfolded DeleteThread_Cond_def]
      p2[unfolded Inv_Threads_Space_In_Spaces_def] by auto
    then have h4:"the (thread_space s gno) = space \<Longrightarrow> the (space_threads s (the (thread_space s gno))) \<noteq> {gno}"
      using delete_temp2_C_Space h2 h3 delete_temp1_NC_Space h1 delete_temp1_NC_Thread by metis
    then have h5:"the (thread_space s gno) = space \<Longrightarrow> the (space_threads s space) - {gno} = 
        the (space_threads (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) space)"
      apply(simp add: delete_temp3_NC_Space)
      unfolding delete_temp2_def Let_def using delete_temp1_NC_Space delete_temp1_NC_Thread
      Thread_AtLeast_One_In_Space p1 p2 a1[unfolded DeleteThread_Cond_def] by auto
    from h4 have h6:"the (thread_space s gno) = space \<Longrightarrow> {t. thread_space s t = Some space} - {gno} = 
      {t. thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space}"
      unfolding delete_temp3_def 
      by (auto simp add:delete_temp2_NC_Thread delete_temp1_NC_Thread)
    then have h7:"the (thread_space s gno) = space \<Longrightarrow> the (space_threads (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) space) =
       {t. thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space}"
      using h5 h6 h11 by simp
    have h8:"the (thread_space s gno) \<noteq> space \<Longrightarrow> the (space_threads s space) = 
        the (space_threads (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) space)"
      apply(simp add:delete_temp3_NC_Space)
      apply(subst delete_temp2_NC_Space_Threads_Other)
      using delete_temp1_NC_Thread delete_temp1_NC_Space by auto
    have h9:"the (thread_space s gno) \<noteq> space \<Longrightarrow> {t. thread_space s t = Some space} = 
      {t. thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space}"
      unfolding delete_temp3_def 
      by (auto simp add:delete_temp2_NC_Thread delete_temp1_NC_Thread)
    then have "the (thread_space s gno) \<noteq> space \<Longrightarrow> the (space_threads (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) space) =
       {t. thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space}"
      using h11 h8 h9 by simp
    then show "the (space_threads (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) space) =
       {t. thread_space (delete_temp3 (delete_temp2 (delete_temp1 s gno) gno) gno) t = Some space}"
      using h7 by auto                     
  qed
  using assms by simp

lemma DeleteThread_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Sche_In_Threads)
    apply(rule delete_temp3_Inv_Threads_Sche_In_Threads)
    apply(rule delete_temp2_Inv_Threads_Sche_In_Threads)
    apply(rule delete_temp1_Inv_Threads_Sche_In_Threads)
    using assms
    unfolding DeleteThread_Cond_def delete_temp2_def Let_def
      delete_temp1_def
    using DeleteAddressSpace_NC_Thread
      Unwind_NC_Thread dequeue_ready_NC_Thread
    by auto
  using assms by simp

lemma DeleteThread_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_NActive_Utcb_Is_None)
    apply(rule delete_temp3_Inv_NActive_Utcb_Is_None)
    apply(rule delete_temp2_Inv_NActive_Utcb_Is_None)
    apply(rule delete_temp1_Inv_NActive_Utcb_Is_None)
    using assms by simp 
  using assms by simp

lemma DeleteThread_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Active_Utcb_IsNot_None)
    apply(rule delete_temp3_Inv_Active_Utcb_IsNot_None)
    apply(rule delete_temp2_Inv_Active_Utcb_IsNot_None)
    apply(rule delete_temp1_Inv_Active_Utcb_IsNot_None)
    using assms by simp 
  using assms by simp

lemma DeleteThread_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_IntThreads_Utcb_Is_None)
    apply(rule delete_temp3_Inv_IntThreads_Utcb_Is_None)
    apply(rule delete_temp2_Inv_IntThreads_Utcb_Is_None)
    apply(rule delete_temp1_Inv_IntThreads_Utcb_Is_None)
    using assms by simp 
  using assms by simp

lemma DeleteThread_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Partner_In_Threads)
    apply(rule delete_temp3_Inv_Threads_Partner_In_Threads)
    apply(rule delete_temp2_Inv_Threads_Partner_In_Threads)
     apply(rule delete_temp1_Inv_Threads_Partner_In_Threads)
    using assms apply simp
    sorry
  using assms by simp

lemma DeleteThread_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
      and p2:"Inv_Active_In_Threads s"
      and p3:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Incoming_In_Threads)
    apply(rule delete_temp3_Inv_Threads_Incoming_In_Threads)
    apply(rule delete_temp2_Inv_Threads_Incoming_In_Threads)
     apply(rule delete_temp1_Inv_Threads_Incoming_In_Threads)
     apply (auto simp add: assms DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_IPC
      Unwind_NC_Thread dequeue_ready_NC_Thread Unwind_NC_IPC dequeue_ready_NC_IPC
        delete_temp2_def delete_temp1_def Let_def DeleteThread_Cond_def)
    using Unwind_NC_IPC1 dequeue_ready_NC_IPC
    by (metis in_mono)+
  using p1 by simp

lemma DeleteThread_Inv_Sigma0_Space:
  assumes p1:"Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Sigma0_Space)
    apply(rule delete_temp3_Inv_Sigma0_Space)
    apply(rule delete_temp2_Inv_Sigma0_Space)
    apply(rule delete_temp1_Inv_Sigma0_Space)
    using assms apply auto
    unfolding DeleteThread_Cond_def Inv_Sigma0_Space_def by simp 
  using assms by simp

lemma DeleteThread_Inv_IntThreads_Space:
  assumes p1:"Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_IntThreads_Space)
    apply(rule delete_temp3_Inv_IntThreads_Space)
    apply(rule delete_temp2_Inv_IntThreads_Space)
    apply(rule delete_temp1_Inv_IntThreads_Space)
    using assms apply auto
    unfolding DeleteThread_Cond_def Inv_IntThreads_Space_def by simp
  using assms by simp

lemma DeleteThread_Inv_RootServer_Space:
  assumes p1:"Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (DeleteThread s gno)"
  apply(subst DeleteThread_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_RootServer_Space)
    apply(rule delete_temp3_Inv_RootServer_Space)
    apply(rule delete_temp2_Inv_RootServer_Space)
    apply(rule delete_temp1_Inv_RootServer_Space)
    using assms apply auto
    unfolding DeleteThread_Cond_def Inv_RootServer_Space_def by simp
  using assms by simp

lemma DeleteThread_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (DeleteThread s gno)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] 
    DeleteThread_Inv_Idle_NotIn_Threads DeleteThread_Inv_Idle_Space_Is_KernelSpace
    DeleteThread_Inv_Sigma0_In_Active DeleteThread_Inv_Sigma0_Space
    DeleteThread_Inv_IntThreads_Space DeleteThread_Inv_RootServer_In_Active
    DeleteThread_Inv_RootServer_Space DeleteThread_Inv_IntThreads_In_Active
    DeleteThread_Inv_Threads_In_Config DeleteThread_Inv_Active_In_Threads
    DeleteThread_Inv_NThreads_Is_None DeleteThread_Inv_Threads_IsNot_None
    DeleteThread_Inv_Threads_Space_Dom DeleteThread_Inv_Threads_Space_In_Spaces 
    DeleteThread_Inv_Threads_Eq_Space_Threads DeleteThread_Inv_Threads_Sche_In_Threads
    DeleteThread_Inv_NActive_Utcb_Is_None DeleteThread_Inv_Active_Utcb_IsNot_None
    DeleteThread_Inv_IntThreads_Utcb_Is_None DeleteThread_Inv_Threads_Partner_In_Threads 
    DeleteThread_Inv_Threads_Incoming_In_Threads
  by auto

lemma DeleteThread_Inv:
  assumes "Invariants s"
  shows "Invariants (DeleteThread s gno)"
  using assms unfolding Invariants_def
  using DeleteThread_Inv_Current DeleteThread_Inv_Space DeleteThread_Inv_Thread
  by (auto simp:Inv_Thread_def)


section\<open>SetScheduler\<close>
subsection\<open>Current\<close>
lemma SetScheduler_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma SetScheduler_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma SetScheduler_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetScheduler s gno scheduler)"
  using SetScheduler_Inv_Current_Thread_In_Active SetScheduler_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetScheduler_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetScheduler s gno scheduler)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetScheduler_tran)

lemma SetScheduler_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetScheduler s gno scheduler)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetScheduler_rtran SetScheduler_valid)

lemma SetScheduler_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetScheduler s gno scheduler)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: SetScheduler_valid SetScheduler_NC_Space)

lemma SetScheduler_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetScheduler s gno scheduler)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetScheduler_direct_eq SetScheduler_NC_Space
  by auto

lemma SetScheduler_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetScheduler s gno scheduler)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetScheduler_NC_Space)

lemma SetScheduler_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetScheduler s gno scheduler)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetScheduler_NC_Space)

lemma SetScheduler_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetScheduler s gno scheduler)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetScheduler_NC_Space)

lemma SetScheduler_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetScheduler s gno scheduler)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetScheduler_valid)

lemma SetScheduler_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetScheduler s gno scheduler)"
  unfolding Inv_Space_def
  using SetScheduler_Inv_Space_HasNot_Loop SetScheduler_Inv_Space_Valid_Has_Real
   SetScheduler_Inv_Space_Perms_IsNot_Empty SetScheduler_Inv_Space_Spaces_In_Config 
   SetScheduler_Inv_Space_InitialSpaces_In_Spaces SetScheduler_Inv_Space_Perms_Subset
   SetScheduler_Inv_Space_Spaces_IsNot_None SetScheduler_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetScheduler_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def
  by auto

lemma SetScheduler_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def
  by auto

lemma SetScheduler_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma SetScheduler_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma SetScheduler_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma SetScheduler_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def
  by auto

lemma SetScheduler_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma SetScheduler_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def Inv_Active_In_Threads_def
  by auto

lemma SetScheduler_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma SetScheduler_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  using assms unfolding Inv_Threads_Space_Dom_def
  by auto
  
lemma SetScheduler_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
  using p1 Inv_Threads_Space_In_Spaces_def
  by (auto simp:spaces_def)

lemma SetScheduler_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Eq_Space_Threads)
  using p1 Inv_Threads_Eq_Space_Threads_def
  by (auto simp:spaces_def)

lemma SetScheduler_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def
  by auto

lemma SetScheduler_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma SetScheduler_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma SetScheduler_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 Inv_IntThreads_Utcb_Is_None_def
  by auto

lemma SetScheduler_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def
  by auto

lemma SetScheduler_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetScheduler s gno scheduler)"
  unfolding SetScheduler_def SetThreadScheduler_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def
  by auto

lemma SetScheduler_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetScheduler s gno scheduler)"
  using assms unfolding Inv_Sigma0_Space_def SetScheduler_def
    SetThreadScheduler_def SetError_def SetThreadError_def
  by auto

lemma SetScheduler_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetScheduler s gno scheduler)"
  using assms unfolding Inv_RootServer_Space_def SetScheduler_def
    SetThreadScheduler_def SetError_def SetThreadError_def
  by auto

lemma SetScheduler_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetScheduler s gno scheduler)"
  using assms unfolding Inv_IntThreads_Space_def SetScheduler_def
    SetThreadScheduler_def SetError_def SetThreadError_def
  by auto

lemma SetScheduler_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (SetScheduler s gno scheduler)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] SetScheduler_Inv_Idle_Space_Is_KernelSpace
    SetScheduler_Inv_Idle_NotIn_Threads 
    SetScheduler_Inv_Sigma0_In_Active SetScheduler_Inv_RootServer_In_Active 
    SetScheduler_Inv_IntThreads_In_Active 
    SetScheduler_Inv_Threads_In_Config SetScheduler_Inv_Active_In_Threads 
    SetScheduler_Inv_NThreads_Is_None SetScheduler_Inv_Threads_IsNot_None
    SetScheduler_Inv_Threads_Space_Dom
    SetScheduler_Inv_Threads_Space_In_Spaces SetScheduler_Inv_Threads_Eq_Space_Threads
    SetScheduler_Inv_Threads_Sche_In_Threads 
    SetScheduler_Inv_NActive_Utcb_Is_None SetScheduler_Inv_Active_Utcb_IsNot_None
    SetScheduler_Inv_IntThreads_Utcb_Is_None SetScheduler_Inv_Threads_Partner_In_Threads
    SetScheduler_Inv_Threads_Incoming_In_Threads SetScheduler_Inv_Sigma0_Space
    SetScheduler_Inv_RootServer_Space SetScheduler_Inv_IntThreads_Space
  by auto

lemma SetScheduler_Inv:
  assumes "Invariants s"
  shows "Invariants (SetScheduler s gno scheduler)"
  using assms unfolding Invariants_def
  using SetScheduler_Inv_Current SetScheduler_Inv_Space SetScheduler_Inv_Thread
  by auto

section\<open>SetPager\<close>
subsection\<open>Current\<close>
lemma SetPager_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma SetPager_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma SetPager_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetPager s gno pager)"
  using SetPager_Inv_Current_Thread_In_Active SetPager_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma SetPager_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetPager s gno pager)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetPager_tran)

lemma SetPager_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetPager s gno pager)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetPager_rtran SetPager_valid)

lemma SetPager_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetPager s gno pager)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: SetPager_valid SetPager_NC_Space)

lemma SetPager_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetPager s gno pager)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetPager_direct_eq SetPager_NC_Space
  by auto

lemma SetPager_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetPager s gno pager)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetPager_NC_Space)

lemma SetPager_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetPager s gno pager)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetPager_NC_Space)

lemma SetPager_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetPager s gno pager)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetPager_NC_Space)

lemma SetPager_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetPager s gno pager)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetPager_valid)

lemma SetPager_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetPager s gno pager)"
  unfolding Inv_Space_def
  using SetPager_Inv_Space_HasNot_Loop SetPager_Inv_Space_Valid_Has_Real
   SetPager_Inv_Space_Perms_IsNot_Empty SetPager_Inv_Space_Spaces_In_Config 
   SetPager_Inv_Space_InitialSpaces_In_Spaces SetPager_Inv_Space_Perms_Subset
   SetPager_Inv_Space_Spaces_IsNot_None SetPager_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma SetPager_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def
  by auto

lemma SetPager_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def
  by auto

lemma SetPager_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma SetPager_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma SetPager_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma SetPager_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def
  by auto

lemma SetPager_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma SetPager_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def Inv_Active_In_Threads_def
  by auto

lemma SetPager_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma SetPager_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  using assms unfolding Inv_Threads_Space_Dom_def
  by auto
  
lemma SetPager_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
  using p1 Inv_Threads_Space_In_Spaces_def
  by (auto simp:spaces_def)

lemma SetPager_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetPager s gno pager)"
  unfolding SetPager_def Let_def
  using assms SetError_Inv_Threads_Eq_Space_Threads SetThreadPager_Inv_Threads_Eq_Space_Threads
  by auto

lemma SetPager_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def
  by auto

lemma SetPager_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma SetPager_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma SetPager_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 Inv_IntThreads_Utcb_Is_None_def
  by auto

lemma SetPager_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def
  by auto

lemma SetPager_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetPager s gno pager)"
  unfolding SetPager_def SetThreadPager_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def
  by auto

lemma SetPager_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetPager s gno pager)"
  using assms unfolding Inv_Sigma0_Space_def
    SetPager_def SetThreadPager_def SetError_def SetThreadError_def
  by auto

lemma SetPager_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetPager s gno pager)"
  using assms unfolding Inv_RootServer_Space_def 
    SetPager_def SetThreadPager_def SetError_def SetThreadError_def
  by auto

lemma SetPager_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetPager s gno pager)"
  using assms unfolding Inv_IntThreads_Space_def
    SetPager_def SetThreadPager_def SetError_def SetThreadError_def
  by auto

lemma SetPager_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (SetPager s gno pager)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] SetPager_Inv_Idle_Space_Is_KernelSpace
    SetPager_Inv_Idle_NotIn_Threads 
    SetPager_Inv_Sigma0_In_Active SetPager_Inv_RootServer_In_Active 
    SetPager_Inv_IntThreads_In_Active 
    SetPager_Inv_Threads_In_Config SetPager_Inv_Active_In_Threads 
    SetPager_Inv_NThreads_Is_None SetPager_Inv_Threads_IsNot_None
    SetPager_Inv_Threads_Space_Dom
    SetPager_Inv_Threads_Space_In_Spaces SetPager_Inv_Threads_Eq_Space_Threads
    SetPager_Inv_Threads_Sche_In_Threads 
    SetPager_Inv_NActive_Utcb_Is_None SetPager_Inv_Active_Utcb_IsNot_None
    SetPager_Inv_IntThreads_Utcb_Is_None SetPager_Inv_Threads_Partner_In_Threads
    SetPager_Inv_Threads_Incoming_In_Threads SetPager_Inv_Sigma0_Space
    SetPager_Inv_RootServer_Space SetPager_Inv_IntThreads_Space
  by auto

lemma SetPager_Inv:
  assumes "Invariants s"
  shows "Invariants (SetPager s gno pager)"
  using assms unfolding Invariants_def
  using SetPager_Inv_Current SetPager_Inv_Space SetPager_Inv_Thread
  by auto

section\<open>SetState\<close>
subsection\<open>Current\<close>
lemma SetState_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma SetState_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma SetState_Inv_Current_Isar:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (SetState s gno state)"
  using SetState_Inv_Current_Thread_In_Active SetState_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

lemma SetState_Inv_Current:"\<forall> s. Inv_Current s \<longrightarrow> Inv_Current (SetState s gno state)"
  using SetState_Inv_Current_Isar
  by simp

subsection\<open>Space\<close>
lemma SetState_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (SetState s gno state)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst SetState_tran)

lemma SetState_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (SetState s gno state)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: SetState_rtran SetState_valid)

lemma SetState_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (SetState s gno state)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: SetState_valid SetState_NC_Space)

lemma SetState_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (SetState s gno state)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using SetState_direct_eq SetState_NC_Space
  by auto

lemma SetState_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (SetState s gno state)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:SetState_NC_Space)

lemma SetState_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (SetState s gno state)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:SetState_NC_Space)

lemma SetState_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (SetState s gno state)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:SetState_NC_Space)

lemma SetState_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (SetState s gno state)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:SetState_valid)

lemma SetState_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (SetState s gno state)"
  unfolding Inv_Space_def
  using SetState_Inv_Space_HasNot_Loop SetState_Inv_Space_Valid_Has_Real
   SetState_Inv_Space_Perms_IsNot_Empty SetState_Inv_Space_Spaces_In_Config 
   SetState_Inv_Space_InitialSpaces_In_Spaces SetState_Inv_Space_Perms_Subset
   SetState_Inv_Space_Spaces_IsNot_None SetState_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto


subsection\<open>Thread\<close>
lemma SetState_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def
  by auto

lemma SetState_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def
  by auto

lemma SetState_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma SetState_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma SetState_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma SetState_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def
  by auto

lemma SetState_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma SetState_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def Inv_Active_In_Threads_def
  by auto

lemma SetState_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma SetState_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (SetState s gno val)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  using assms Inv_Threads_Space_Dom_def
  by auto
  
lemma SetState_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
  using p1 Inv_Threads_Space_In_Spaces_def
  by (auto simp:spaces_def)

lemma SetState_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (SetState s gno error)"
  unfolding SetState_def Let_def
  using assms SetError_Inv_Threads_Eq_Space_Threads SetThreadState_Inv_Threads_Eq_Space_Threads
  by auto

lemma SetState_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def
  by auto

lemma SetState_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma SetState_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma SetState_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 Inv_IntThreads_Utcb_Is_None_def
  by auto

lemma SetState_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def
  by auto

lemma SetState_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (SetState s gno state)"
  unfolding SetState_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def
  by auto

lemma SetState_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (SetState s gno pager)"
  using assms unfolding Inv_Sigma0_Space_def SetState_def
    SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma SetState_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (SetState s gno pager)"
  using assms unfolding Inv_RootServer_Space_def SetState_def
    SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma SetState_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (SetState s gno pager)"
  using assms unfolding Inv_IntThreads_Space_def SetState_def
    SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma SetState_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (SetState s gno state)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] SetState_Inv_Idle_Space_Is_KernelSpace
    SetState_Inv_Idle_NotIn_Threads 
    SetState_Inv_Sigma0_In_Active SetState_Inv_RootServer_In_Active 
    SetState_Inv_IntThreads_In_Active 
    SetState_Inv_Threads_In_Config SetState_Inv_Active_In_Threads 
    SetState_Inv_NThreads_Is_None SetState_Inv_Threads_IsNot_None 
    SetState_Inv_Threads_Space_Dom
    SetState_Inv_Threads_Space_In_Spaces SetState_Inv_Threads_Eq_Space_Threads
    SetState_Inv_Threads_Sche_In_Threads 
    SetState_Inv_NActive_Utcb_Is_None SetState_Inv_Active_Utcb_IsNot_None
    SetState_Inv_IntThreads_Utcb_Is_None SetState_Inv_Threads_Partner_In_Threads
    SetState_Inv_Threads_Incoming_In_Threads SetState_Inv_Sigma0_Space
    SetState_Inv_RootServer_Space SetState_Inv_IntThreads_Space
  by auto

lemma SetState_Inv:
  assumes "Invariants s"
  shows "Invariants (SetState s gno state)"
  using assms unfolding Invariants_def
  using SetState_Inv_Current SetState_Inv_Space SetState_Inv_Thread 
  by auto

section\<open>Migrate\<close>
thm Migrate_def[no_vars]
definition "Migrate_branch1 s gno space \<equiv> 
s\<lparr>thread_space := 
    ((thread_space s)(gno := Some space)),
      space_threads := (space_threads s)
          (space:= Some (the (space_threads s space) \<union> {gno}))\<rparr>"

definition "Migrate_branch2 s gno space \<equiv> 
s\<lparr>thread_space := ((thread_space s)(gno := Some space)),
  space_threads := (space_threads s)
       (space:= Some (the (space_threads s space) \<union> {gno}),
       (the (thread_space s gno)):= 
            Some (the (space_threads s (the (thread_space s gno))) - {gno}))\<rparr>"

lemma Migrate_eq:"Migrate SysConf s gno space = 
(if Migrate_Cond SysConf s gno space
 then SetError (if (the (space_threads s (the (thread_space s gno)))) = {gno}
      then Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno space
      else Migrate_branch2 s gno space) (current_thread (if (the (space_threads s (the (thread_space s gno)))) = {gno}
      then Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno space
      else Migrate_branch2 s gno space)) eNoError
 else s)"
  unfolding Migrate_def Let_def Migrate_branch1_def Migrate_branch2_def
  by simp

lemma Migrate_branch1_direct_eq:"(Migrate_branch1 s gno space) \<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding Migrate_branch1_def direct_path_def
  by auto

lemma Migrate_branch1_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (Migrate_branch1 s gno space)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(Migrate_branch1 s gno space)\<turnstile>x\<leadsto>\<^sup>1y"
    using Migrate_branch1_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(Migrate_branch1 s gno space)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(Migrate_branch1 s gno space)\<turnstile>x\<leadsto>\<^sup>1y"
    using Migrate_branch1_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma Migrate_branch1_tran:"(Migrate_branch1 s gno space)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using Migrate_branch1_direct_eq tran_path.intros Migrate_branch1_tran1
  by auto

lemma Migrate_branch1_rtran:"(Migrate_branch1 s gno space)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using Migrate_branch1_tran rtran_tran
  by auto

lemma Migrate_branch1_valid_vpage:"(Migrate_branch1 s gno space) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using Migrate_branch1_direct_eq valid_page_def
  by auto

lemma Migrate_branch1_valid_rpage:"(Migrate_branch1 s gno space)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma Migrate_branch1_valid:"(Migrate_branch1 s gno space)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using Migrate_branch1_valid_vpage apply simp
  using Migrate_branch1_valid_rpage by simp

lemma Migrate_branch1_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (Migrate_branch1 s gno space)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst Migrate_branch1_tran)

lemma Migrate_branch1_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (Migrate_branch1 s gno space)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: Migrate_branch1_rtran Migrate_branch1_valid)

lemma Migrate_branch1_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (Migrate_branch1 s gno space)"
  using assms unfolding Inv_Space_Perms_IsNot_Empty_def
  using Migrate_branch1_valid
  apply auto
  unfolding get_perms_def Migrate_branch1_def
  by auto

lemma Migrate_branch1_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (Migrate_branch1 s gno space)"
  using assms unfolding Inv_Space_Perms_Subset_def
  apply(auto simp add: Migrate_branch1_direct_eq)
  apply(subgoal_tac "space_mapping (Migrate_branch1 s gno space) = space_mapping s")
  subgoal
    unfolding get_perms_def
    by (simp add: subset_iff)
  unfolding Migrate_branch1_def by simp

lemma Migrate_branch1_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (Migrate_branch1 s gno space)"
  using assms unfolding Inv_Space_Spaces_In_Config_def
  by (auto simp:Migrate_branch1_def spaces_def)

lemma Migrate_branch1_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (Migrate_branch1 s gno space)"
  using assms unfolding Inv_Space_InitialSpaces_In_Spaces_def
  by (auto simp:Migrate_branch1_def spaces_def)

lemma Migrate_branch1_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
      and "space \<in> spaces s"
    shows "Inv_Space_Spaces_IsNot_None (Migrate_branch1 s gno space)"
  using assms unfolding Inv_Space_Spaces_IsNot_None_def spaces_def
  by (auto simp:Migrate_branch1_def)

lemma Migrate_branch1_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (Migrate_branch1 s gno space)"
  using assms unfolding Inv_Space_Vpage_Range_def 
  using Migrate_branch1_valid
  by blast

lemma Migrate_branch2_direct_eq:"(Migrate_branch2 s gno space) \<turnstile>x\<leadsto>\<^sup>1y = s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding Migrate_branch2_def direct_path_def
  by auto

lemma Migrate_branch2_tran1:" s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> (Migrate_branch2 s gno space)\<turnstile>x\<leadsto>\<^sup>+y"
proof(induct rule:tran_path.induct)
  case (one_path x y)
  thm one_path.hyps
  then have "(Migrate_branch2 s gno space)\<turnstile>x\<leadsto>\<^sup>1y"
    using Migrate_branch2_direct_eq by simp
  then show ?case
    by(rule tran_path.intros)
next
  case (tran_path x y z)
  then have h2:"s\<turnstile>x\<leadsto>\<^sup>1y \<and> s\<turnstile>y\<leadsto>\<^sup>+z" by simp
  have h3: "(Migrate_branch2 s gno space)\<turnstile>y\<leadsto>\<^sup>+z"
    by (simp add: tran_path.hyps(3))
  then have h21:"(Migrate_branch2 s gno space)\<turnstile>x\<leadsto>\<^sup>1y"
    using Migrate_branch2_direct_eq h2 by simp
  then show ?case
    using h3 tran_path.intros(2) by blast
qed
  
lemma Migrate_branch2_tran:"(Migrate_branch2 s gno space)\<turnstile>x\<leadsto>\<^sup>+y = s\<turnstile>x\<leadsto>\<^sup>+y"
  apply(rule iffI)
   apply(induct rule: tran_path.induct)
  using Migrate_branch2_direct_eq tran_path.intros Migrate_branch2_tran1
  by auto

lemma Migrate_branch2_rtran:"(Migrate_branch2 s gno space)\<turnstile>x\<leadsto>\<^sup>*y = s\<turnstile>x\<leadsto>\<^sup>*y"
  using Migrate_branch2_tran rtran_tran
  by auto

lemma Migrate_branch2_valid_vpage:"(Migrate_branch2 s gno space) \<turnstile> (Virtual sp1 v_page) = s \<turnstile> (Virtual sp1 v_page)"
  using Migrate_branch2_direct_eq valid_page_def
  by auto

lemma Migrate_branch2_valid_rpage:"(Migrate_branch2 s gno space)\<turnstile> (Real r) = s\<turnstile>(Real r)"
  using valid_page_def
  by simp

lemma Migrate_branch2_valid:"(Migrate_branch2 s gno space)\<turnstile> x = s\<turnstile>x"
  apply (case_tac x)
  using Migrate_branch2_valid_vpage apply simp
  using Migrate_branch2_valid_rpage by simp

lemma Migrate_branch2_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (Migrate_branch2 s gno space)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst Migrate_branch2_tran)

lemma Migrate_branch2_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (Migrate_branch2 s gno space)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: Migrate_branch2_rtran Migrate_branch2_valid)

lemma Migrate_branch2_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (Migrate_branch2 s gno space)"
  using assms unfolding Inv_Space_Perms_IsNot_Empty_def
  using Migrate_branch2_valid
  apply auto
  unfolding get_perms_def Migrate_branch2_def
  by auto

lemma Migrate_branch2_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (Migrate_branch2 s gno space)"
  using assms unfolding Inv_Space_Perms_Subset_def
  apply(auto simp add: Migrate_branch2_direct_eq)
  apply(subgoal_tac "space_mapping (Migrate_branch2 s gno space) = space_mapping s")
  subgoal
    unfolding get_perms_def
    by (simp add: subset_iff)
  unfolding Migrate_branch2_def by simp

lemma Migrate_branch2_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (Migrate_branch2 s gno space)"
  using assms unfolding Inv_Space_Spaces_In_Config_def
  by (auto simp:Migrate_branch2_def spaces_def)

lemma Migrate_branch2_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (Migrate_branch2 s gno space)"
  using assms unfolding Inv_Space_InitialSpaces_In_Spaces_def
  by (auto simp:Migrate_branch2_def spaces_def)

lemma Migrate_branch2_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
      and p2:"Inv_Threads_Space_In_Spaces s"
      and p3:"gno \<in> threads s"
      and p4:"space \<in> spaces s"
    shows "Inv_Space_Spaces_IsNot_None (Migrate_branch2 s gno space)"
  using p1 p2 p3 p4 unfolding Inv_Space_Spaces_IsNot_None_def spaces_def
    Inv_Threads_Space_In_Spaces_def
  by (auto simp:Migrate_branch2_def)

lemma Migrate_branch2_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (Migrate_branch2 s gno space)"
  using assms unfolding Inv_Space_Vpage_Range_def 
  using Migrate_branch2_valid
  by blast

subsection\<open>Current\<close>
lemma Migrate_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def DeleteAddressSpace_Inv_Current_Thread_In_Active
  by auto

lemma Migrate_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def DeleteAddressSpace_Inv_Current_Space_IsNot_None
  by auto

lemma Migrate_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (Migrate SysConf s gno sp)"
  using Migrate_Inv_Current_Thread_In_Active Migrate_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma Migrate_direct_eq:"(Migrate SysConf s gno sp)\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y"
  unfolding Migrate_def Let_def
  apply(cases "Migrate_Cond SysConf s gno sp")
  subgoal
    apply (simp add:SetError_direct_eq)
    apply(cases "the (space_threads s (the (thread_space s gno))) = {gno}")
    subgoal
      apply (simp add:direct_path_def)
      using DeleteAddressSpace_direct_eq[unfolded direct_path_def]
      by simp
    by (simp add:direct_path_def)
  by simp

lemma Migrate_tran:"(Migrate SysConf s gno sp)\<turnstile> x \<leadsto>\<^sup>+ y \<Longrightarrow> s\<turnstile> x \<leadsto>\<^sup>+ y"
  apply(induct rule: tran_path.induct)
  using Migrate_direct_eq tran_path.intros
  by blast+

lemma Migrate_rtran:"(Migrate SysConf s gno sp)\<turnstile>x\<leadsto>\<^sup>*y \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>*y"
  using Migrate_tran rtran_tran
  by auto

lemma Migrate_valid_vpage:"(Migrate SysConf s gno sp)\<turnstile>(Virtual sp1 v_page) \<Longrightarrow>
s\<turnstile>(Virtual sp1 v_page)"
  unfolding valid_page_def
  using Migrate_direct_eq
  by fastforce

lemma Migrate_valid_rpage:"(Migrate SysConf s gno sp)\<turnstile>(Real r) = s \<turnstile>(Real r)"
  unfolding valid_page_def
  by auto

lemma Migrate_valid:"(Migrate SysConf s gno sp) \<turnstile> x \<Longrightarrow> s \<turnstile> x"
  using Migrate_valid_vpage Migrate_valid_rpage
    FatherIsVirtual ValidExSon
  by fastforce

lemma Migrate_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (Migrate SysConf s gno sp)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def] Migrate_tran
  by metis

lemma Migrate_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s \<and> Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Vpage_Range s"
  shows "Inv_Space_Valid_Has_Real (Migrate SysConf s gno sp)"
  apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Valid_Has_Real)
    apply(rule elim_if)
    subgoal
      apply(rule Migrate_branch1_Inv_Space_Valid_Has_Real)
      apply(rule DeleteAddressSpace_Inv_Space_Valid_Has_Real)
      using assms by simp
    apply(rule Migrate_branch2_Inv_Space_Valid_Has_Real)
    using assms by simp
  using assms by simp

lemma Migrate_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (Migrate SysConf s gno sp)"
  apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Perms_IsNot_Empty)
    apply(rule elim_if)
    subgoal
      apply(rule Migrate_branch1_Inv_Space_Perms_IsNot_Empty)
      apply(rule DeleteAddressSpace_Inv_Space_Perms_IsNot_Empty)
      using assms by simp
    apply(rule Migrate_branch2_Inv_Space_Perms_IsNot_Empty)
    using assms by simp
  using assms by simp

lemma Migrate_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s \<and> Inv_Space_Vpage_Range s"
  shows "Inv_Space_Perms_Subset (Migrate SysConf s gno sp)"
 apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Perms_Subset)
    apply(rule elim_if)
    subgoal
      apply(rule Migrate_branch1_Inv_Space_Perms_Subset)
      apply(rule DeleteAddressSpace_Inv_Space_Perms_Subset)
      using assms by simp
    apply(rule Migrate_branch2_Inv_Space_Perms_Subset)
    using assms by simp
  using assms by simp


lemma Migrate_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (Migrate SysConf s gno sp)"
 apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Spaces_In_Config)
    apply(rule elim_if)
    subgoal
      apply(rule Migrate_branch1_Inv_Space_Spaces_In_Config)
      apply(rule DeleteAddressSpace_Inv_Space_Spaces_In_Config)
      using assms by simp
    apply(rule Migrate_branch2_Inv_Space_Spaces_In_Config)
    using assms by simp
  using assms by simp

lemma Migrate_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (Migrate SysConf s gno sp)"
 apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_InitialSpaces_In_Spaces)
    apply(rule elim_if)
    subgoal
      apply(rule Migrate_branch1_Inv_Space_InitialSpaces_In_Spaces)
      apply(rule DeleteAddressSpace_Inv_Space_InitialSpaces_In_Spaces)
      using assms by simp
    apply(rule Migrate_branch2_Inv_Space_InitialSpaces_In_Spaces)
    using assms by simp
  using assms by simp

lemma Migrate_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
      and "Inv_Threads_Space_In_Spaces s"
    shows "Inv_Space_Spaces_IsNot_None (Migrate SysConf s gno sp)"
 apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Space_Spaces_IsNot_None)
    apply(rule elim_if)
    subgoal
      apply(rule Migrate_branch1_Inv_Space_Spaces_IsNot_None)
      apply(rule DeleteAddressSpace_Inv_Space_Spaces_IsNot_None)
      using assms apply simp
      unfolding Migrate_Cond_def using DeleteAddressSpace_NC_Space_Other2
      by auto
    unfolding Migrate_Cond_def
    apply(rule Migrate_branch2_Inv_Space_Spaces_IsNot_None)
    using assms by auto
  using assms by simp

lemma Migrate_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (Migrate SysConf s gno sp)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def] Migrate_valid
  by blast

lemma Migrate_Inv_Space:
  assumes p1:"Inv_Space s"
      and "Inv_Threads_Space_In_Spaces s"
    shows "Inv_Space (Migrate SysConf s gno sp)"
  using assms unfolding Inv_Space_def
  using Migrate_Inv_Space_HasNot_Loop Migrate_Inv_Space_Valid_Has_Real
   Migrate_Inv_Space_Perms_IsNot_Empty Migrate_Inv_Space_Spaces_In_Config 
   Migrate_Inv_Space_Spaces_IsNot_None Migrate_Inv_Space_InitialSpaces_In_Spaces Migrate_Inv_Space_Perms_Subset
   Migrate_Inv_Space_Spaces_IsNot_None Migrate_Inv_Space_Vpage_Range
  by auto

subsection\<open>Thread\<close>
lemma Migrate_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def DeleteAddressSpace_Inv_Idle_NotIn_Threads
  by auto

lemma Migrate_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
      and "Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_Space_Is_KernelSpace (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using assms Inv_Idle_Space_Is_KernelSpace_def DeleteAddressSpace_Inv_Idle_Space_Is_KernelSpace
    apply auto
  unfolding Migrate_Cond_def Inv_Idle_NotIn_Threads_def
  by auto

lemma Migrate_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def DeleteAddressSpace_Inv_Sigma0_In_Active
  by auto

lemma Migrate_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def DeleteAddressSpace_Inv_RootServer_In_Active
  by auto

lemma Migrate_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def DeleteAddressSpace_Inv_IntThreads_In_Active
  by auto

lemma Migrate_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (Migrate SysConf s gno handler)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def DeleteAddressSpace_Inv_Threads_In_Config
  by auto

lemma Migrate_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def DeleteAddressSpace_Inv_Active_In_Threads
  by auto

lemma Migrate_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  apply(rule elim_if)
  using p0 p1 p2 Inv_NThreads_Is_None_def DeleteAddressSpace_Inv_NThreads_Is_None  
      apply auto[1]
      apply(simp add:Migrate_Cond_def)
      apply (simp add: DeleteAddressSpace_NC_Thread)
      apply(simp add:Migrate_Cond_def)
  using Inv_NThreads_Is_None_def p1 apply auto[1]
    apply(rule elim_if)
  using p0 DeleteAddressSpace_Inv_Active_In_Threads Inv_Active_In_Threads_def apply simp
     apply(simp add:Migrate_Cond_def)
  using p2 apply blast
    apply(simp add:Inv_Active_In_Threads_def)
    apply(simp add:Migrate_Cond_def)
  using Inv_Active_In_Threads_def p2 apply blast
   apply simp
  by (simp add: p1)

lemma Migrate_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def DeleteAddressSpace_Inv_Threads_IsNot_None
  by auto

lemma Migrate_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
  apply(rule SetError_Inv_Threads_Space_Dom)
  using assms unfolding Inv_Threads_Space_Dom_def Migrate_Cond_def
  using DeleteAddressSpace_NC_Thread
  by auto
  
lemma Migrate_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
      and p2:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Space_In_Spaces (Migrate SysConf s gno sp)"
  apply(subst Migrate_eq)
  apply(rule elim_if)
   apply(rule SetError_Inv_Threads_Space_In_Spaces)
  subgoal
    apply(rule elim_if)
    subgoal
      unfolding Inv_Threads_Space_In_Spaces_def
      apply rule apply rule
    proof-
      fix t
      assume a1:"Migrate_Cond SysConf s gno sp" and
        a2:"the (space_threads s (the (thread_space s gno))) = {gno}" and
        a3:"t \<in> threads (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp)"
      then have h1:"the (thread_space s gno) \<noteq> sp" using a1 Migrate_Cond_def by simp
      from a1 have h2:"sp \<in> spaces s" using Migrate_Cond_def by simp
      then have h21:"\<exists>y. space_mapping s sp = Some y" using spaces_def dom_def by auto
      from a3[unfolded Migrate_branch1_def] have h3:"t \<in> threads s" using DeleteAddressSpace_NC_Thread by simp
      then have h31:"\<exists>space. space \<in> spaces s \<and> thread_space s t = Some space"
        using p1[unfolded Inv_Threads_Space_In_Spaces_def] by simp
      then obtain space where h32:"space \<in> spaces s \<and> thread_space s t = Some space" by auto
      then have h33:"thread_space (DeleteAddressSpace s (the (thread_space s gno))) t = Some space"
        using DeleteAddressSpace_NC_Thread by simp
      have h4:"t \<noteq> gno \<Longrightarrow> (the (thread_space s gno)) \<noteq> space"
      proof
        assume a41:"t \<noteq> gno" and a42:"the (thread_space s gno) = space"
        then show False using h32 a2 p2[unfolded Inv_Threads_Eq_Space_Threads_def] by auto
      qed
      then have h41:"t \<noteq> gno \<Longrightarrow> space \<in> dom (space_mapping (DeleteAddressSpace s (the (thread_space s gno))))"
        using DeleteAddressSpace_NC_Space_Other2 h32
        by (simp add:spaces_def)
      show "\<exists>space.
            space \<in> spaces (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) \<and>
            thread_space (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) t = Some space"
        unfolding Migrate_branch1_def spaces_def
        apply (auto)
        subgoal
          using h1 h21 DeleteAddressSpace_NC_Space_Other1
          by blast
        using h41 h33 by simp
    qed
    using p1
    unfolding Inv_Threads_Space_In_Spaces_def Migrate_branch2_def spaces_def
      Migrate_Cond_def
    by auto
  using p1 by auto

lemma Migrate_branch1_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    and p2:"Migrate_Cond SysConf s gno sp"
    and p3:"the (space_threads s (the (thread_space s gno))) = {gno}"
    and p4:"Inv_Threads_Space_In_Spaces s"
  shows "Inv_Threads_Eq_Space_Threads (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp)"
  unfolding Inv_Threads_Eq_Space_Threads_def
  apply rule
  apply rule
  proof-
    fix space
    assume a1:"space \<in> spaces (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp)"
    have h1:"the (thread_space s gno) \<noteq> sp" using p2 Migrate_Cond_def by simp
    have h2:"the (thread_space s gno) \<in> spaces s" 
      using p4[unfolded Inv_Threads_Space_In_Spaces_def] p2[unfolded Migrate_Cond_def] by auto
    have h3:"\<not>dIsPrivilegedSpace(the (thread_space s gno))"
      unfolding dIsPrivilegedSpace_def is_kSigma0Space_def is_kRootServerSpace_def
      using p2[unfolded Migrate_Cond_def] by auto
    then have h4:"(the (thread_space s gno)) \<notin> spaces (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp)"
      unfolding DeleteAddressSpace_def Let_def Migrate_branch1_def spaces_def dom_def using h2 h3 by auto
    then have h5:"space \<noteq> the (thread_space s gno)"
      using a1 by auto
    have h6:"space \<in> spaces (DeleteAddressSpace s (the (thread_space s gno)))"
      using a1[unfolded Migrate_branch1_def] by(auto simp:spaces_def)
    then have h7:"space \<in> spaces (DeleteAddressSpace1 s (the (thread_space s gno)))"
      using DeleteAddressSpace_eq by simp
    then have h8:"space \<in> spaces (DeleteAddressSpace_auxi (Unmap_fpage s (the (thread_space s gno)) 0 UNIV page_maxnum)
               (the (thread_space s gno)))"
      unfolding DeleteAddressSpace1_def using h2 h3 by simp
    have h9:"\<And>s a. space \<in> spaces (DeleteAddressSpace_auxi s a) \<Longrightarrow> space \<in> spaces s"
      unfolding DeleteAddressSpace_auxi_def spaces_def by auto
    then have h10:"space \<in> spaces (Unmap_fpage s (the (thread_space s gno)) 0 UNIV page_maxnum)"
      using h8 by auto
    then have h11:"space \<in> spaces s"
      using Unmap_fpage_NC_Space by simp
    then have h12:"the (space_threads s space) = {t. thread_space s t = Some space}" 
      using p1 Inv_Threads_Eq_Space_Threads_def by simp
    show "the (space_threads (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) space) =
       {t. thread_space (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) t = Some space}"
    proof(cases "space = sp")
      case True
      then have h110:"{t. thread_space s t = Some space} = 
        {t. thread_space (DeleteAddressSpace s (the (thread_space s gno))) t = Some space}"
        using DeleteAddressSpace_NC_Thread by simp
      have h111:"{t. thread_space (DeleteAddressSpace s (the (thread_space s gno))) t = Some space} \<union> {gno} =
            {t. thread_space (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) t = Some space}"
        unfolding Migrate_branch1_def using True h5 DeleteAddressSpace_NC_Thread by auto
      then have h112:"{t. thread_space s t = Some space} \<union> {gno} = 
          {t. thread_space (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) t = Some space}"
        using h110 by simp
      have h220:"the (space_threads s space) = the (space_threads (DeleteAddressSpace s (the (thread_space s gno))) space)"
        using DeleteAddressSpace_NC_Space_Other h5 by simp
      have h221:"the (space_threads (DeleteAddressSpace s (the (thread_space s gno))) space) \<union> {gno} = 
          the (space_threads (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) space)"
        unfolding Migrate_branch1_def using True by auto
      then have "the (space_threads s space) \<union> {gno} = 
          the (space_threads (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) space)"
        using h220 by auto
      then show ?thesis using h112 h12 by auto
    next
      case False
      then have h210:"{t. thread_space s t = Some space} = 
        {t. thread_space (DeleteAddressSpace s (the (thread_space s gno))) t = Some space}"
        using DeleteAddressSpace_NC_Thread by simp
      have h211:"{t. thread_space (DeleteAddressSpace s (the (thread_space s gno))) t = Some space} =
            {t. thread_space (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) t = Some space}"
        unfolding Migrate_branch1_def using False h5 DeleteAddressSpace_NC_Thread by auto
      then have h212:"{t. thread_space s t = Some space} = 
          {t. thread_space (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) t = Some space}"
        using h210 by simp
      have h220:"the (space_threads s space) = the (space_threads (DeleteAddressSpace s (the (thread_space s gno))) space)"
        using DeleteAddressSpace_NC_Space_Other h5 by simp
      have h221:"\<And>s. the (space_threads s space) = the (space_threads (Migrate_branch1 s gno sp) space)"
        unfolding Migrate_branch1_def using False by auto
      then have "the (space_threads s space) = the (space_threads (Migrate_branch1 (DeleteAddressSpace s (the (thread_space s gno))) gno sp) space)"
        using h220 by auto
      then show ?thesis using h212 h12 by simp
    qed
   qed
lemma "A=B \<Longrightarrow> A-{x} = C \<Longrightarrow> B-{x}=D \<Longrightarrow> C = D"
  by auto


lemma Migrate_branch2_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    and p2:"Migrate_Cond SysConf s gno sp"
    and p3:"the (space_threads s (the (thread_space s gno))) \<noteq> {gno}"
    and p4:"Inv_Threads_Space_In_Spaces s"
  shows"Inv_Threads_Eq_Space_Threads (Migrate_branch2 s gno sp)"
  unfolding Inv_Threads_Eq_Space_Threads_def
  apply rule apply rule
  proof-
    fix space
    assume a1:"space \<in> spaces (Migrate_branch2 s gno sp)"
    have h1:"the (thread_space s gno) \<noteq> sp" using p2 Migrate_Cond_def by simp
    have h2:"space \<in> spaces s" using a1[unfolded Migrate_branch2_def spaces_def] spaces_def by auto
    then have h21:"the (space_threads s space) = {t. thread_space s t = Some space}" 
      using p1 Inv_Threads_Eq_Space_Threads_def by simp
    show "the (space_threads (Migrate_branch2 s gno sp) space) = {t. thread_space (Migrate_branch2 s gno sp) t = Some space}"
    proof(cases "space = sp")
    case True
    then have h111:"{t. thread_space s t = Some space} \<union> {gno}= {t. thread_space (Migrate_branch2 s gno sp) t = Some space}"
      unfolding Migrate_branch2_def using h1 by auto
    have h112:"the (space_threads s space) \<union> {gno} = the (space_threads (Migrate_branch2 s gno sp) space)"
      unfolding Migrate_branch2_def using h1 True h2 p1[unfolded Inv_Threads_Eq_Space_Threads_def]
      by auto
    then show ?thesis using h111 h21 by simp
    next
      case False
      then have h211:"space \<noteq> sp" by simp
      then show ?thesis
      proof(cases "space = the (thread_space s gno)")
        case True
        then have h212:"{t. thread_space s t = Some space} - {gno}= {t. thread_space (Migrate_branch2 s gno sp) t = Some space}"
          unfolding Migrate_branch2_def using h1 by auto
        have h213:"the (space_threads s space) - {gno} = the (space_threads (Migrate_branch2 s gno sp) space)"
          unfolding Migrate_branch2_def using h1 True h2 p1[unfolded Inv_Threads_Eq_Space_Threads_def]
          by auto
        then show ?thesis using h212 h21 h213 by simp
      next
        case False
        then have h221:"{t. thread_space s t = Some space} = {t. thread_space (Migrate_branch2 s gno sp) t = Some space}"
          unfolding Migrate_branch2_def using h1 h211 by auto
        have h222:"the (space_threads s space) = the (space_threads (Migrate_branch2 s gno sp) space)"
          unfolding Migrate_branch2_def using False h1 h211 h2 p1[unfolded Inv_Threads_Eq_Space_Threads_def]
          by auto
        then show ?thesis using h221 h222 h21 by simp
      qed
    qed
  qed
    
lemma Migrate_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    and p2:"Inv_Threads_Space_In_Spaces s"
  shows "Inv_Threads_Eq_Space_Threads (Migrate SysConf s gno sp)"
  apply(subst Migrate_eq)
  apply(rule elim_if)
  subgoal
    apply(rule SetError_Inv_Threads_Eq_Space_Threads)
    apply(rule elim_if)
    using assms Migrate_branch1_Inv_Threads_Eq_Space_Threads
    Migrate_branch2_Inv_Threads_Eq_Space_Threads
    by auto
    using assms by simp

lemma Migrate_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def DeleteAddressSpace_Inv_Threads_Sche_In_Threads
  by auto

lemma Migrate_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def DeleteAddressSpace_Inv_NActive_Utcb_Is_None
  by auto

lemma Migrate_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (Migrate SysConf s gno sp)"
  unfolding Migrate_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def DeleteAddressSpace_Inv_Active_Utcb_IsNot_None
  by auto

lemma Migrate_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 Inv_IntThreads_Utcb_Is_None_def DeleteAddressSpace_Inv_IntThreads_Utcb_Is_None
  by auto

lemma Migrate_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (Migrate SysConf s gno sp)"
  unfolding Migrate_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def 
    DeleteAddressSpace_Inv_Threads_Partner_In_Threads
  by auto

lemma Migrate_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def 
    DeleteAddressSpace_Inv_Threads_Incoming_In_Threads
  by auto

lemma Migrate_Inv_Sigma0_Space:
  assumes p1:"Inv_Sigma0_Space s"
    shows "Inv_Sigma0_Space (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_Space)
  using p1 Inv_Sigma0_Space_def Migrate_Cond_def
    DeleteAddressSpace_Inv_Sigma0_Space
  by auto

lemma Migrate_Inv_RootServer_Space:
  assumes p1:"Inv_RootServer_Space s"
    shows "Inv_RootServer_Space (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_Space)
  using p1 Inv_RootServer_Space_def Migrate_Cond_def
    DeleteAddressSpace_Inv_RootServer_Space
  by auto

lemma Migrate_Inv_IntThreads_Space:
  assumes p1:"Inv_IntThreads_Space s"
    shows "Inv_IntThreads_Space (Migrate SysConf s gno sp)"
  unfolding Migrate_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Space)
  using p1 Inv_IntThreads_Space_def Migrate_Cond_def
    DeleteAddressSpace_Inv_IntThreads_Space
  by auto

lemma Migrate_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (Migrate SysConf s gno sp)"
  using assms unfolding Inv_Thread_def
  using Migrate_Inv_Idle_Space_Is_KernelSpace
    Migrate_Inv_Idle_NotIn_Threads 
    Migrate_Inv_Sigma0_In_Active Migrate_Inv_RootServer_In_Active 
    Migrate_Inv_IntThreads_In_Active 
    Migrate_Inv_Threads_In_Config Migrate_Inv_Active_In_Threads 
    Migrate_Inv_NThreads_Is_None Migrate_Inv_Threads_IsNot_None
    Migrate_Inv_Threads_Space_Dom
    Migrate_Inv_Threads_Space_In_Spaces Migrate_Inv_Threads_Eq_Space_Threads
    Migrate_Inv_Threads_Sche_In_Threads 
    Migrate_Inv_NActive_Utcb_Is_None Migrate_Inv_Active_Utcb_IsNot_None
    Migrate_Inv_IntThreads_Utcb_Is_None Migrate_Inv_Threads_Partner_In_Threads
    Migrate_Inv_Threads_Incoming_In_Threads Migrate_Inv_Sigma0_Space
    Migrate_Inv_RootServer_Space Migrate_Inv_IntThreads_Space
  by auto

lemma Migrate_Inv:
  assumes "Invariants s"
  shows "Invariants (Migrate SysConf s gno sp)"
  using assms unfolding Invariants_def
  using Migrate_Inv_Current Migrate_Inv_Space Migrate_Inv_Thread
    Inv_Thread_def
  by auto

section\<open>ActivateInterrupt\<close>
subsection\<open>Current\<close>
lemma ActivateInterrupt_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma ActivateInterrupt_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma ActivateInterrupt_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (ActivateInterrupt SysConf s gno handler)"
  using ActivateInterrupt_Inv_Current_Thread_In_Active ActivateInterrupt_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma ActivateInterrupt_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst ActivateInterrupt_tran)

lemma ActivateInterrupt_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: ActivateInterrupt_rtran ActivateInterrupt_valid)

lemma ActivateInterrupt_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: ActivateInterrupt_valid ActivateInterrupt_NC_Space)

lemma ActivateInterrupt_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (ActivateInterrupt SysConf s gno pa)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using ActivateInterrupt_direct_eq ActivateInterrupt_NC_Space
  by auto

lemma ActivateInterrupt_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:ActivateInterrupt_NC_Space)

lemma ActivateInterrupt_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:ActivateInterrupt_NC_Space)

lemma ActivateInterrupt_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:ActivateInterrupt_NC_Space)

lemma ActivateInterrupt_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:ActivateInterrupt_valid)

lemma ActivateInterrupt_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Space_def
  using ActivateInterrupt_Inv_Space_HasNot_Loop ActivateInterrupt_Inv_Space_Valid_Has_Real
   ActivateInterrupt_Inv_Space_Perms_IsNot_Empty ActivateInterrupt_Inv_Space_Spaces_In_Config 
   ActivateInterrupt_Inv_Space_InitialSpaces_In_Spaces ActivateInterrupt_Inv_Space_Perms_Subset
   ActivateInterrupt_Inv_Space_Spaces_IsNot_None ActivateInterrupt_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma ActivateInterrupt_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def
  by auto

lemma ActivateInterrupt_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def
  by auto

lemma ActivateInterrupt_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma ActivateInterrupt_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma ActivateInterrupt_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma ActivateInterrupt_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def
  by auto

lemma ActivateInterrupt_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma ActivateInterrupt_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def Inv_Active_In_Threads_def
  by auto

lemma ActivateInterrupt_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma ActivateInterrupt_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_Dom)
  using assms unfolding Inv_Threads_Space_Dom_def
  by (auto)

lemma ActivateInterrupt_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
  using p1 Inv_Threads_Space_In_Spaces_def
  by (auto simp:spaces_def)

lemma ActivateInterrupt_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Eq_Space_Threads)
  using p1 Inv_Threads_Eq_Space_Threads_def
  by (auto simp:spaces_def)

lemma ActivateInterrupt_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def
  by auto

lemma ActivateInterrupt_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma ActivateInterrupt_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma ActivateInterrupt_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 Inv_IntThreads_Utcb_Is_None_def
  by auto

lemma ActivateInterrupt_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def
  by auto

lemma ActivateInterrupt_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (ActivateInterrupt SysConf s gno handler)"
  unfolding ActivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def
  by auto

lemma ActivateInterrupt_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (ActivateInterrupt SysConf s gno handler)"
  using assms unfolding Inv_Sigma0_Space_def ActivateInterrupt_def
    SetThreadScheduler_def SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma ActivateInterrupt_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (ActivateInterrupt SysConf s gno handler)"
  using assms unfolding Inv_RootServer_Space_def ActivateInterrupt_def
    SetThreadScheduler_def SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma ActivateInterrupt_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (ActivateInterrupt SysConf s gno handler)"
  using assms unfolding Inv_IntThreads_Space_def ActivateInterrupt_def
    SetThreadScheduler_def SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma ActivateInterrupt_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (ActivateInterrupt SysConf s gno handler)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] ActivateInterrupt_Inv_Idle_Space_Is_KernelSpace
    ActivateInterrupt_Inv_Idle_NotIn_Threads 
    ActivateInterrupt_Inv_Sigma0_In_Active ActivateInterrupt_Inv_RootServer_In_Active 
    ActivateInterrupt_Inv_IntThreads_In_Active 
    ActivateInterrupt_Inv_Threads_In_Config ActivateInterrupt_Inv_Active_In_Threads 
    ActivateInterrupt_Inv_NThreads_Is_None ActivateInterrupt_Inv_Threads_IsNot_None
    ActivateInterrupt_Inv_Threads_Space_Dom
    ActivateInterrupt_Inv_Threads_Space_In_Spaces ActivateInterrupt_Inv_Threads_Eq_Space_Threads 
    ActivateInterrupt_Inv_Threads_Sche_In_Threads 
    ActivateInterrupt_Inv_NActive_Utcb_Is_None ActivateInterrupt_Inv_Active_Utcb_IsNot_None
    ActivateInterrupt_Inv_IntThreads_Utcb_Is_None ActivateInterrupt_Inv_Threads_Partner_In_Threads
    ActivateInterrupt_Inv_Threads_Incoming_In_Threads ActivateInterrupt_Inv_Sigma0_Space
    ActivateInterrupt_Inv_RootServer_Space ActivateInterrupt_Inv_IntThreads_Space
  by auto

lemma ActivateInterrupt_Inv:
  assumes "Invariants s"
  shows "Invariants (ActivateInterrupt SysConf s gno handler)"
  using assms unfolding Invariants_def
  using ActivateInterrupt_Inv_Current ActivateInterrupt_Inv_Space ActivateInterrupt_Inv_Thread 
  by auto

section\<open>DeactivateInterrupt\<close>
subsection\<open>Current\<close>
lemma DeactivateInterrupt_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Thread_In_Active)
  using p1 Inv_Current_Thread_In_Active_def
  by auto

lemma DeactivateInterrupt_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Current_Space_IsNot_None)
  using p1 Inv_Current_Space_IsNot_None_def
  by auto

lemma DeactivateInterrupt_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (DeactivateInterrupt s gno)"
  using DeactivateInterrupt_Inv_Current_Thread_In_Active DeactivateInterrupt_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma DeactivateInterrupt_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (DeactivateInterrupt s gno)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by(subst DeactivateInterrupt_tran)

lemma DeactivateInterrupt_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (DeactivateInterrupt s gno)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: DeactivateInterrupt_rtran DeactivateInterrupt_valid)

lemma DeactivateInterrupt_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (DeactivateInterrupt s gno)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  by (auto simp: DeactivateInterrupt_valid DeactivateInterrupt_NC_Space)

lemma DeactivateInterrupt_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (DeactivateInterrupt s gno)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  using DeactivateInterrupt_direct_eq DeactivateInterrupt_NC_Space
  by auto

lemma DeactivateInterrupt_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (DeactivateInterrupt s gno)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
  by (auto simp:DeactivateInterrupt_NC_Space)

lemma DeactivateInterrupt_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (DeactivateInterrupt s gno)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:DeactivateInterrupt_NC_Space)

lemma DeactivateInterrupt_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (DeactivateInterrupt s gno)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by (auto simp:DeactivateInterrupt_NC_Space)

lemma DeactivateInterrupt_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (DeactivateInterrupt s gno)"
  unfolding Inv_Space_Vpage_Range_def 
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp:DeactivateInterrupt_valid)

lemma DeactivateInterrupt_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (DeactivateInterrupt s gno)"
  unfolding Inv_Space_def
  using DeactivateInterrupt_Inv_Space_HasNot_Loop DeactivateInterrupt_Inv_Space_Valid_Has_Real
   DeactivateInterrupt_Inv_Space_Perms_IsNot_Empty DeactivateInterrupt_Inv_Space_Spaces_In_Config 
   DeactivateInterrupt_Inv_Space_InitialSpaces_In_Spaces DeactivateInterrupt_Inv_Space_Perms_Subset
   DeactivateInterrupt_Inv_Space_Spaces_IsNot_None DeactivateInterrupt_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma DeactivateInterrupt_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_NotIn_Threads)
  using p1 Inv_Idle_NotIn_Threads_def
  by auto

lemma DeactivateInterrupt_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Idle_Space_Is_KernelSpace)
  using p1 Inv_Idle_Space_Is_KernelSpace_def
  by auto

lemma DeactivateInterrupt_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
      shows "Inv_Sigma0_In_Active (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Sigma0_In_Active)
  using p1 Inv_Sigma0_In_Active_def
  by auto

lemma DeactivateInterrupt_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_RootServer_In_Active)
  using p1 Inv_RootServer_In_Active_def
  by auto

lemma DeactivateInterrupt_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_In_Active)
  using p1 Inv_IntThreads_In_Active_def
  by auto

lemma DeactivateInterrupt_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_In_Config)
  using p1 Inv_Threads_In_Config_def
  by auto

lemma DeactivateInterrupt_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_In_Threads)
  using p1 Inv_Active_In_Threads_def
  by auto

lemma DeactivateInterrupt_Inv_NThreads_Is_None:
  assumes p0:"Inv_IntThreads_In_Active s"
      and p1:"Inv_NThreads_Is_None s"
      and p2:"Inv_Active_In_Threads s"
    shows "Inv_NThreads_Is_None (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NThreads_Is_None)
  using p0 p1 p2 Inv_IntThreads_In_Active_def Inv_NThreads_Is_None_def Inv_Active_In_Threads_def
  by auto

lemma DeactivateInterrupt_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_IsNot_None)
  using p1 Inv_Threads_IsNot_None_def
  by auto

lemma DeactivateInterrupt_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_Dom)
  using assms unfolding Inv_Threads_Space_Dom_def
  by auto
  
lemma DeactivateInterrupt_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Space_In_Spaces)
  using p1 Inv_Threads_Space_In_Spaces_def
  by (auto simp:spaces_def)

lemma DeactivateInterrupt_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Eq_Space_Threads)
  using p1 Inv_Threads_Eq_Space_Threads_def
  by (auto simp:spaces_def)

lemma DeactivateInterrupt_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Sche_In_Threads)
  using p1 Inv_Threads_Sche_In_Threads_def
  by auto

lemma DeactivateInterrupt_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_NActive_Utcb_Is_None)
  using p1 Inv_NActive_Utcb_Is_None_def
  by auto

lemma DeactivateInterrupt_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Active_Utcb_IsNot_None)
  using p1 Inv_Active_Utcb_IsNot_None_def
  by auto

lemma DeactivateInterrupt_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_IntThreads_Utcb_Is_None)
  using p1 Inv_IntThreads_Utcb_Is_None_def
  by auto

lemma DeactivateInterrupt_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Partner_In_Threads)
  using p1 Inv_Threads_Partner_In_Threads_def
  by auto

lemma DeactivateInterrupt_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (DeactivateInterrupt s gno)"
  unfolding DeactivateInterrupt_def SetThreadScheduler_def SetThreadState_def Let_def
  apply(rule elim_if)
   apply(subst SetError_Inv_Threads_Incoming_In_Threads)
  using p1 Inv_Threads_Incoming_In_Threads_def
  by auto

lemma DeactivateInterrupt_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (DeactivateInterrupt s gno)"
  using assms unfolding Inv_Sigma0_Space_def DeactivateInterrupt_def
    SetThreadScheduler_def SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma DeactivateInterrupt_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (DeactivateInterrupt s gno)"
  using assms unfolding Inv_RootServer_Space_def DeactivateInterrupt_def
    SetThreadScheduler_def SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma DeactivateInterrupt_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (DeactivateInterrupt s gno)"
  using assms unfolding Inv_IntThreads_Space_def DeactivateInterrupt_def
    SetThreadScheduler_def SetThreadState_def SetError_def SetThreadError_def
  by auto

lemma DeactivateInterrupt_Inv_Thread:
  assumes p1:"Inv_Thread s"
    shows "Inv_Thread (DeactivateInterrupt s gno)"
  unfolding Inv_Thread_def
  using p1[unfolded Inv_Thread_def] DeactivateInterrupt_Inv_Idle_Space_Is_KernelSpace
    DeactivateInterrupt_Inv_Idle_NotIn_Threads 
    DeactivateInterrupt_Inv_Sigma0_In_Active DeactivateInterrupt_Inv_RootServer_In_Active 
    DeactivateInterrupt_Inv_IntThreads_In_Active 
    DeactivateInterrupt_Inv_Threads_In_Config DeactivateInterrupt_Inv_Active_In_Threads 
    DeactivateInterrupt_Inv_NThreads_Is_None DeactivateInterrupt_Inv_Threads_IsNot_None 
    DeactivateInterrupt_Inv_Threads_Space_Dom DeactivateInterrupt_Inv_Threads_Space_In_Spaces 
    DeactivateInterrupt_Inv_Threads_Eq_Space_Threads DeactivateInterrupt_Inv_Threads_Sche_In_Threads 
    DeactivateInterrupt_Inv_NActive_Utcb_Is_None DeactivateInterrupt_Inv_Active_Utcb_IsNot_None
    DeactivateInterrupt_Inv_IntThreads_Utcb_Is_None DeactivateInterrupt_Inv_Threads_Partner_In_Threads
    DeactivateInterrupt_Inv_Threads_Incoming_In_Threads DeactivateInterrupt_Inv_Sigma0_Space
    DeactivateInterrupt_Inv_RootServer_Space DeactivateInterrupt_Inv_IntThreads_Space
  by auto

lemma DeactivateInterrupt_Inv:
  assumes "Invariants s"
  shows "Invariants (DeactivateInterrupt s gno)"
  using assms unfolding Invariants_def
  using DeactivateInterrupt_Inv_Current DeactivateInterrupt_Inv_Space DeactivateInterrupt_Inv_Thread 
  by auto

end