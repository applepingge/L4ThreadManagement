theory L4_Inv_Space
  imports L4_Inv_s0
begin

section\<open>CreateAddressSpace\<close>
subsection\<open>Current\<close>
lemma CreateAddressSpace_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma CreateAddressSpace_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma CreateAddressSpace_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (CreateAddressSpace SysConf s sp)"
  using CreateAddressSpace_Inv_Current_Thread_In_Active CreateAddressSpace_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma CreateAddressSpace_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  apply (subst CreateAddressSpace_tran)
  by auto

lemma CreateAddressSpace_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: CreateAddressSpace_rtran CreateAddressSpace_valid)

lemma CreateAddressSpace_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  apply(subst CreateAddressSpace_valid)
  using CreateAddressSpace_NC_Space_Other CreateAddressSpace_C_Space
    CreateAddressSpace_NC_Space
  by (metis (no_types, lifting) Inv_Space_Valid_In_Spaces_lemma)

lemma CreateAddressSpace_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Perms_Subset (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_Perms_Subset_def
  apply auto
proof-
  fix sp1 sp2 v1 v2 x
  assume a1:"(CreateAddressSpace SysConf s sp)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
  then have h1:"s \<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)" using CreateAddressSpace_direct_eq
    by simp
  then have h2:"s \<turnstile>(Virtual sp2 v2)" using YIsValid p2 by simp
  have h3:"space_mapping s sp1 \<noteq> None" using h1 direct_path_def by auto
  then have h4:"space_mapping s sp1 = space_mapping (CreateAddressSpace SysConf s sp) sp1"
    using CreateAddressSpace_space by simp
  have h5:"space_mapping s sp2 \<noteq> None" using h2 valid_page_def direct_path_def by auto
  then have h6:"space_mapping s sp2 = space_mapping (CreateAddressSpace SysConf s sp) sp2"
    using CreateAddressSpace_space by simp
  have "get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" using p1 Inv_Space_Perms_Subset_def h1 by simp
  then have "get_perms (CreateAddressSpace SysConf s sp) sp1 v1 \<subseteq>
        get_perms (CreateAddressSpace SysConf s sp) sp2 v2" using h4 h6 get_perms_def
    by auto
  then show "x \<in> get_perms (CreateAddressSpace SysConf s sp) sp1 v1 \<Longrightarrow>
       x \<in> get_perms (CreateAddressSpace SysConf s sp) sp2 v2"
  by auto 
qed

lemma CreateAddressSpace_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
    CreateAddressSpace_NC_Space_Other CreateAddressSpace_NC_Space CreateAddressSpace_C_Space
  by (metis Diff_eq_empty_iff Un_empty_right Un_insert_right insert_Diff_if)

lemma CreateAddressSpace_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
    CreateAddressSpace_NC_Space_Other CreateAddressSpace_NC_Space CreateAddressSpace_C_Space
  by (metis (no_types, lifting) Un_assoc subset_Un_eq)

lemma CreateAddressSpace_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
  shows "Inv_Space_Spaces_IsNot_None (CreateAddressSpace SysConf s sp)"
proof(cases "sp \<in> (Address_Space SysConf) \<and> sp \<notin> spaces s")
  case True
  have h1:"dom (space_threads (CreateAddressSpace SysConf s sp)) = dom (space_threads s) \<union> {sp}"
    using True CreateAddressSpace_def by auto
  then have "spaces (CreateAddressSpace SysConf s sp) = spaces s \<union> {sp}"
    using True CreateAddressSpace_C_Space by auto
  then show ?thesis 
    unfolding Inv_Space_Spaces_IsNot_None_def
    using p1[unfolded Inv_Space_Spaces_IsNot_None_def] h1
    by auto
next
  case False
  then show ?thesis  
    using CreateAddressSpace_NC_Space Inv_Space_Spaces_IsNot_None_def
      p1[unfolded Inv_Space_Spaces_IsNot_None_def]
  by simp
qed

lemma CreateAddressSpace_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp: CreateAddressSpace_valid)

lemma CreateAddressSpace_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Space_def
  using CreateAddressSpace_Inv_Space_HasNot_Loop CreateAddressSpace_Inv_Space_Valid_Has_Real
   CreateAddressSpace_Inv_Space_Perms_IsNot_Empty CreateAddressSpace_Inv_Space_Perms_Subset
   CreateAddressSpace_Inv_Space_Spaces_In_Config CreateAddressSpace_Inv_Space_InitialSpaces_In_Spaces 
   CreateAddressSpace_Inv_Space_Spaces_IsNot_None CreateAddressSpace_Inv_Space_Vpage_Range 
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma CreateAddressSpace_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma CreateAddressSpace_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma CreateAddressSpace_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma CreateAddressSpace_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma CreateAddressSpace_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma CreateAddressSpace_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma CreateAddressSpace_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma CreateAddressSpace_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma CreateAddressSpace_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma CreateAddressSpace_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma CreateAddressSpace_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Threads_Space_In_Spaces_def
  apply(subst CreateAddressSpace_NC_Thread)
  apply auto
proof-
  fix t
  assume a1:"t \<in> threads s"
  then have h1:"\<exists>space. space \<in> spaces s \<and> thread_space s t = Some space"
    using p1[unfolded Inv_Threads_Space_In_Spaces_def] by simp
  then obtain space where h2:"space \<in> spaces s \<and> thread_space s t = Some space"
    by auto
  then show "\<exists>space.
            space \<in> spaces (CreateAddressSpace SysConf s sp) \<and>
            thread_space (CreateAddressSpace SysConf s sp) t = Some space"
  proof(cases "sp \<in> (Address_Space SysConf) \<and> sp \<notin> spaces s")
    case True
    then have "space \<in> spaces (CreateAddressSpace SysConf s sp)" 
      using CreateAddressSpace_C_Space h2 by auto
    then show ?thesis using CreateAddressSpace_NC_Thread h2 by auto
  next
    case False
    then show ?thesis using CreateAddressSpace_NC_Thread CreateAddressSpace_NC_Space h2 by auto
  qed
qed

lemma CreateAddressSpace_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma CreateAddressSpace_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma CreateAddressSpace_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma CreateAddressSpace_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"current_thread s \<notin> kIntThreads"
      and p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (CreateAddressSpace SysConf s sp)"
  unfolding Inv_IntThreads_Utcb_Is_None_def CreateAddressSpace_def SetThreadError_def
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def] p0
  by auto

lemma CreateAddressSpace_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma CreateAddressSpace_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (CreateAddressSpace SysConf s sp)"
  unfolding CreateAddressSpace_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma CreateAddressSpace_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (CreateAddressSpace SysConf s sp)"
  using assms unfolding Inv_Sigma0_Space_def CreateAddressSpace_def
  by auto

lemma CreateAddressSpace_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (CreateAddressSpace SysConf s sp)"
  using assms unfolding Inv_RootServer_Space_def CreateAddressSpace_def
  by auto

lemma CreateAddressSpace_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (CreateAddressSpace SysConf s sp)"
  using assms unfolding Inv_IntThreads_Space_def CreateAddressSpace_def
  by auto

lemma CreateAddressSpace_Inv_Thread:
  assumes p0:"current_thread s \<notin> kIntThreads"
      and p1:"Inv_Thread s"
    shows "Inv_Thread (CreateAddressSpace SysConf s sp)"
  unfolding Inv_Thread_def
  using p0 p1[unfolded Inv_Thread_def] CreateAddressSpace_Inv_Idle_NotIn_Threads 
    CreateAddressSpace_Inv_Sigma0_In_Active CreateAddressSpace_Inv_Idle_Space_Is_KernelSpace
    CreateAddressSpace_Inv_RootServer_In_Active CreateAddressSpace_Inv_IntThreads_In_Active 
    CreateAddressSpace_Inv_Threads_In_Config CreateAddressSpace_Inv_Active_In_Threads 
    CreateAddressSpace_Inv_NThreads_Is_None CreateAddressSpace_Inv_Threads_IsNot_None 
    CreateAddressSpace_Inv_Threads_Space_In_Spaces
    CreateAddressSpace_Inv_Threads_Sche_In_Threads 
    CreateAddressSpace_Inv_NActive_Utcb_Is_None CreateAddressSpace_Inv_Active_Utcb_IsNot_None
    CreateAddressSpace_Inv_IntThreads_Utcb_Is_None CreateAddressSpace_Inv_Threads_Partner_In_Threads
    CreateAddressSpace_Inv_Threads_Incoming_In_Threads CreateAddressSpace_Inv_Sigma0_Space
    CreateAddressSpace_Inv_RootServer_Space CreateAddressSpace_Inv_IntThreads_Space
  oops

section\<open>InitialiseAddressSpace\<close>
subsection\<open>Current\<close>
lemma InitialiseAddressSpace_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def]
  by auto

lemma InitialiseAddressSpace_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def]
  by auto

lemma InitialiseAddressSpace_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (InitialiseAddressSpace s sp)"
  using InitialiseAddressSpace_Inv_Current_Thread_In_Active InitialiseAddressSpace_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma InitialiseAddressSpace_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
    shows "Inv_Space_HasNot_Loop (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_HasNot_Loop_def
  using p1[unfolded Inv_Space_HasNot_Loop_def]
  by (subst InitialiseAddressSpace_tran)

lemma InitialiseAddressSpace_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s"
    shows "Inv_Space_Valid_Has_Real (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_Valid_Has_Real_def
  using p1[unfolded Inv_Space_Valid_Has_Real_def]
  by (auto simp: InitialiseAddressSpace_rtran InitialiseAddressSpace_valid)

lemma InitialiseAddressSpace_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def
  using p1[unfolded Inv_Space_Perms_IsNot_Empty_def get_perms_def]
  apply(subst InitialiseAddressSpace_valid)
  using InitialiseAddressSpace_C_Space InitialiseAddressSpace_NC_Space
  by metis

lemma InitialiseAddressSpace_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
    shows "Inv_Space_Perms_Subset (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_Perms_Subset_def get_perms_def
  using p1[unfolded Inv_Space_Perms_Subset_def get_perms_def]
  by (auto simp: InitialiseAddressSpace_direct_eq InitialiseAddressSpace_NC_Space)

lemma InitialiseAddressSpace_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
     InitialiseAddressSpace_NC_Space InitialiseAddressSpace_C_Space
  by metis

lemma InitialiseAddressSpace_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
  by (auto simp:InitialiseAddressSpace_def spaces_def)

lemma InitialiseAddressSpace_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
    shows "Inv_Space_Spaces_IsNot_None (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_Spaces_IsNot_None_def 
  using p1[unfolded Inv_Space_Spaces_IsNot_None_def]
    InitialiseAddressSpace_NC_Space InitialiseAddressSpace_C_Space
  by metis

lemma InitialiseAddressSpace_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def]
  by (auto simp: InitialiseAddressSpace_valid)

lemma InitialiseAddressSpace_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (InitialiseAddressSpace s sp)"
  unfolding Inv_Space_def
  using InitialiseAddressSpace_Inv_Space_HasNot_Loop InitialiseAddressSpace_Inv_Space_Valid_Has_Real
   InitialiseAddressSpace_Inv_Space_Perms_IsNot_Empty InitialiseAddressSpace_Inv_Space_Spaces_In_Config 
   InitialiseAddressSpace_Inv_Space_InitialSpaces_In_Spaces InitialiseAddressSpace_Inv_Space_Perms_Subset
   InitialiseAddressSpace_Inv_Space_Spaces_IsNot_None InitialiseAddressSpace_Inv_Space_Vpage_Range
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma InitialiseAddressSpace_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Idle_NotIn_Threads_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def]
  by auto

lemma InitialiseAddressSpace_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
    shows "Inv_Idle_Space_Is_KernelSpace (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Idle_Space_Is_KernelSpace_def
  using p1[unfolded Inv_Idle_Space_Is_KernelSpace_def]
  by auto

lemma InitialiseAddressSpace_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Sigma0_In_Active_def
  using p1[unfolded Inv_Sigma0_In_Active_def]
  by auto

lemma InitialiseAddressSpace_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_RootServer_In_Active_def
  using p1[unfolded Inv_RootServer_In_Active_def]
  by auto

lemma InitialiseAddressSpace_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_IntThreads_In_Active_def
  using p1[unfolded Inv_IntThreads_In_Active_def]
  by auto

lemma InitialiseAddressSpace_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_Space_Dom_def
  using p1[unfolded Inv_Threads_Space_Dom_def]
  by auto
  
lemma InitialiseAddressSpace_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_In_Config_def
  using p1[unfolded Inv_Threads_In_Config_def]
  by auto

lemma InitialiseAddressSpace_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Active_In_Threads_def
  using p1[unfolded Inv_Active_In_Threads_def]
  by auto

lemma InitialiseAddressSpace_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_NThreads_Is_None_def
  using p1[unfolded Inv_NThreads_Is_None_def]
  by auto

lemma InitialiseAddressSpace_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_IsNot_None_def
  using p1[unfolded Inv_Threads_IsNot_None_def]
  by auto

lemma InitialiseAddressSpace_Inv_Threads_Space_In_Spaces:
  assumes p1:"Inv_Threads_Space_In_Spaces s"
    shows "Inv_Threads_Space_In_Spaces (InitialiseAddressSpace s sp)"
  unfolding Inv_Threads_Space_In_Spaces_def
  apply(subst InitialiseAddressSpace_NC_Thread)
  apply auto
  using p1[unfolded Inv_Threads_Space_In_Spaces_def] 
  unfolding InitialiseAddressSpace_def spaces_def
  by auto

lemma InitialiseAddressSpace_Inv_Threads_Eq_Space_Threads:
  assumes p1:"Inv_Threads_Eq_Space_Threads s"
    shows "Inv_Threads_Eq_Space_Threads (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_Eq_Space_Threads_def spaces_def
  using p1[unfolded Inv_Threads_Eq_Space_Threads_def] spaces_def
  by auto

lemma InitialiseAddressSpace_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_Sche_In_Threads_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def]
  by auto

lemma InitialiseAddressSpace_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_NActive_Utcb_Is_None_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def]
  by auto

lemma InitialiseAddressSpace_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Active_Utcb_IsNot_None_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def]
  by auto

lemma InitialiseAddressSpace_Inv_IntThreads_Utcb_Is_None:
  assumes p0:"current_thread s \<notin> kIntThreads"
      and p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (InitialiseAddressSpace s sp)"
  unfolding Inv_IntThreads_Utcb_Is_None_def InitialiseAddressSpace_def SetThreadError_def
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def] p0
  by auto

lemma InitialiseAddressSpace_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
    shows "Inv_Threads_Partner_In_Threads (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def]
  by auto

lemma InitialiseAddressSpace_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
    shows "Inv_Threads_Incoming_In_Threads (InitialiseAddressSpace s sp)"
  unfolding InitialiseAddressSpace_def Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def]
  by auto

lemma InitialiseAddressSpace_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (InitialiseAddressSpace s sp)"
  using assms unfolding Inv_Sigma0_Space_def InitialiseAddressSpace_def
  by auto

lemma InitialiseAddressSpace_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (InitialiseAddressSpace s sp)"
  using assms unfolding Inv_RootServer_Space_def InitialiseAddressSpace_def
  by auto

lemma InitialiseAddressSpace_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (InitialiseAddressSpace s sp)"
  using assms unfolding Inv_IntThreads_Space_def InitialiseAddressSpace_def
  by auto

lemma InitialiseAddressSpace_Inv_Thread:
  assumes p0:"current_thread s \<notin> kIntThreads"
      and p1:"Inv_Thread s"
    shows "Inv_Thread (InitialiseAddressSpace s sp)"
  unfolding Inv_Thread_def
  using p0 p1[unfolded Inv_Thread_def] InitialiseAddressSpace_Inv_Idle_NotIn_Threads 
    InitialiseAddressSpace_Inv_Sigma0_In_Active InitialiseAddressSpace_Inv_Idle_Space_Is_KernelSpace
    InitialiseAddressSpace_Inv_RootServer_In_Active InitialiseAddressSpace_Inv_IntThreads_In_Active
    InitialiseAddressSpace_Inv_Threads_Space_Dom
    InitialiseAddressSpace_Inv_Threads_In_Config InitialiseAddressSpace_Inv_Active_In_Threads 
    InitialiseAddressSpace_Inv_NThreads_Is_None InitialiseAddressSpace_Inv_Threads_IsNot_None 
    InitialiseAddressSpace_Inv_Threads_Space_In_Spaces InitialiseAddressSpace_Inv_Threads_Eq_Space_Threads
    InitialiseAddressSpace_Inv_Threads_Sche_In_Threads 
    InitialiseAddressSpace_Inv_NActive_Utcb_Is_None InitialiseAddressSpace_Inv_Active_Utcb_IsNot_None
    InitialiseAddressSpace_Inv_IntThreads_Utcb_Is_None InitialiseAddressSpace_Inv_Threads_Partner_In_Threads
    InitialiseAddressSpace_Inv_Threads_Incoming_In_Threads InitialiseAddressSpace_Inv_Sigma0_Space
    InitialiseAddressSpace_Inv_RootServer_Space InitialiseAddressSpace_Inv_IntThreads_Space
  by auto

lemma InitialiseAddressSpace_Inv:"\<forall>s error. current_thread s \<notin> kIntThreads \<longrightarrow> Invariants s \<longrightarrow> Invariants (InitialiseAddressSpace s sp)"
  unfolding Invariants_def
  using InitialiseAddressSpace_Inv_Current InitialiseAddressSpace_Inv_Space InitialiseAddressSpace_Inv_Thread  
  by auto

section\<open>DeleteAddressSpace\<close>
subsection\<open>Current\<close>
lemma DeleteAddressSpace_Inv_Current_Thread_In_Active:
  assumes p1:"Inv_Current_Thread_In_Active s"
    shows "Inv_Current_Thread_In_Active (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Let_def Inv_Current_Thread_In_Active_def
  using p1[unfolded Inv_Current_Thread_In_Active_def] Unmap_fpage_NC_Current
    Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_Current_Space_IsNot_None:
  assumes p1:"Inv_Current_Space_IsNot_None s"
    shows "Inv_Current_Space_IsNot_None (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Let_def Inv_Current_Space_IsNot_None_def
  using p1[unfolded Inv_Current_Space_IsNot_None_def] Unmap_fpage_NC_Current
    Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_Current:
  assumes p1:"Inv_Current s"
    shows "Inv_Current (DeleteAddressSpace s sp)"
  using DeleteAddressSpace_Inv_Current_Thread_In_Active DeleteAddressSpace_Inv_Current_Space_IsNot_None
    Inv_Current_def p1
  by auto

subsection\<open>Space\<close>
lemma DeleteAddressSpace_Inv_Space_Vpage_Range:
  assumes p1:"Inv_Space_Vpage_Range s"
    shows "Inv_Space_Vpage_Range (DeleteAddressSpace s sp)"
  unfolding Inv_Space_Vpage_Range_def
  using p1[unfolded Inv_Space_Vpage_Range_def] DeleteAddressSpace_valid
  by blast

lemma DeleteAddressSpace_auxi_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (DeleteAddressSpace_auxi s sp)"
  using p1
  unfolding Inv_Space_HasNot_Loop_def
  apply auto
  using DeleteAddressSpace_auxi_tran
  by metis

lemma sys_unmap_pre1:"(sys_unmap s sp v UNIV)\<turnstile>x \<Longrightarrow> \<not>s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v)"
proof
  assume a1:"(sys_unmap s sp v UNIV)\<turnstile>x" and a2:"s\<turnstile>x\<leadsto>\<^sup>+(Virtual sp v)"
  then have h1:"\<forall>r. x \<noteq> Real r" using SonIsNoReal basic3 by blast
  from a1 have h2:"s\<turnstile>x" using sys_unmap_valid by simp
  then have "\<not>(sys_unmap s sp v UNIV)\<turnstile>x" using a2 h1 unmap_path_tran_valid
    by (metis FatherIsVirtual ValidExSon subset_UNIV)
  then show False
    using a1 by simp
qed

lemma DeleteAddressSpace_auxi_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
  shows "Inv_Space_Perms_IsNot_Empty (DeleteAddressSpace_auxi s sp)"
  unfolding Inv_Space_Perms_IsNot_Empty_def
  apply auto
proof-
  fix spa v_page
  assume a1:"(DeleteAddressSpace_auxi s sp)\<turnstile>(Virtual spa v_page)" and
     a2:"get_perms (DeleteAddressSpace_auxi s sp) spa v_page = {}"
  from a1 have h1:"s\<turnstile>(Virtual spa v_page)" using DeleteAddressSpace_auxi_valid by simp
  then have h2:"get_perms s spa v_page \<noteq> {}" using p1 Inv_Space_Perms_IsNot_Empty_def by simp
  have h3:"sp \<noteq> spa" using a1 DeleteAddressSpace_auxi_pre2 by auto
  then have "get_perms (DeleteAddressSpace_auxi s sp) spa v_page \<noteq> {}" using h2
    unfolding get_perms_def DeleteAddressSpace_auxi_def by auto
  then show False using a2 by simp
qed

lemma DeleteAddressSpace_auxi_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"(DeleteAddressSpace_auxi s sp)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
      and p3:"sp \<noteq> sp2"
  shows "get_perms (DeleteAddressSpace_auxi s sp) sp1 v1 \<subseteq> get_perms (DeleteAddressSpace_auxi s sp) sp2 v2"
proof-
  from p2 have h1:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)" using DeleteAddressSpace_auxi_direct_eq by simp
  then have h2:"get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" using p1 Inv_Space_Perms_Subset_def by simp
  from p2 have h3:"sp \<noteq> sp1" using DeleteAddressSpace_auxi_pre1 page_t.sel(1) by blast
  then have h4:"get_perms s sp1 v1 = get_perms (DeleteAddressSpace_auxi s sp) sp1 v1"
    unfolding get_perms_def DeleteAddressSpace_auxi_def by auto
  have h5:"get_perms s sp2 v2 = get_perms (DeleteAddressSpace_auxi s sp) sp2 v2"
    unfolding get_perms_def DeleteAddressSpace_auxi_def using p3 by auto
  show ?thesis using h2 h4 h5 by simp
qed

lemma DeleteAddressSpace_Inv_Space_HasNot_Loop:
  assumes p1:"Inv_Space_HasNot_Loop s"
  shows "Inv_Space_HasNot_Loop (DeleteAddressSpace s sp)"
  thm DeleteAddressSpace_def[unfolded Let_def]
proof-
  from p1 have h1:"Inv_Space_HasNot_Loop (Unmap_fpage s sp 0 UNIV page_maxnum)"
    using Unmap_fpage_Inv_Space_HasNot_Loop by simp
  then have h2:"Inv_Space_HasNot_Loop (DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp)"
    using DeleteAddressSpace_auxi_Inv_Space_HasNot_Loop by simp
  show ?thesis unfolding DeleteAddressSpace_def Let_def 
    using p1 h2[unfolded DeleteAddressSpace_auxi_def] by auto
qed

lemma DeleteAddressSpace_Inv_Space_Perms_IsNot_Empty:
  assumes p1:"Inv_Space_Perms_IsNot_Empty s"
    shows "Inv_Space_Perms_IsNot_Empty (DeleteAddressSpace s sp)"
proof-
  from p1 have h1:"Inv_Space_Perms_IsNot_Empty (Unmap_fpage s sp 0 UNIV page_maxnum)"
    using Unmap_fpage_Inv_Space_Perms_IsNot_Empty by simp
  then have h2:"Inv_Space_Perms_IsNot_Empty (DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp)"
    using DeleteAddressSpace_auxi_Inv_Space_Perms_IsNot_Empty by simp
  show ?thesis unfolding DeleteAddressSpace_def Let_def 
    using p1 h2[unfolded DeleteAddressSpace_auxi_def] by auto
qed


lemma sys_unmap_univ:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v) \<Longrightarrow> 
  the (space_mapping (sys_unmap s sp v UNIV) sp1) v1 = None"
  using one_path unmap_path_space by auto

lemma sys_unmap_not_influence_next:
  assumes p1:"Inv_Space_HasNot_Loop s"
  shows "
  (sys_unmap s sp v UNIV)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (Suc v)) = s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (Suc v))"
proof(rule iffI)
  assume a1:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (Suc v))"
  show "(sys_unmap s sp v UNIV)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (Suc v))"
    by (metis Inv_Space_Father_Is_Unique_def Space_Father_Is_Unique a1 n_not_Suc_n p1 tran_one_unique unmap_not_path_direct)
next
  assume a2:"(sys_unmap s sp v UNIV)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (Suc v))"
  show "s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (Suc v))"
    using a2 sys_unmap_pre by blast
qed

lemma sys_unmap_not_influence_any:
  assumes p1:"Inv_Space_HasNot_Loop s"
      and p2:"v \<noteq> v2"
  shows "
  (sys_unmap s sp v UNIV)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2) = s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2)"
proof(rule iffI)
  assume a1:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2)"
  show "(sys_unmap s sp v UNIV)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2)"
    by (metis Inv_Space_HasNot_Loop_def a1 basic15 p1 p2 page_t.inject(1) rtran_tran unmap_not_path_direct)
next
  assume a2:"(sys_unmap s sp v UNIV)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2)"
  show "s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2)"
    using a2 sys_unmap_pre by blast
qed

lemma Unmap_fpage_sep:" Unmap_fpage s sp v UNIV (Suc n) = Unmap_fpage (sys_unmap s sp v UNIV) sp (Suc v) UNIV n"
  apply(induction n)
  by auto

lemma Unmap_fpage_not_influence_other:"s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (v + n)) \<Longrightarrow> Inv_Space_HasNot_Loop s \<Longrightarrow>
(Unmap_fpage s sp v UNIV n)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp (v + n))"
proof(induction n arbitrary:s v)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have h1:"(Unmap_fpage s sp (Suc v) UNIV n)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp ((Suc v) + n))"
    by (metis add_Suc_shift)
  then show ?case 
    by (metis Suc.IH Suc.prems(1) Suc.prems(2) Unmap_fpage_sep add_Suc_shift add_cancel_left_right nat.simps(3) sys_unmap_Inv_Space_HasNot_Loop sys_unmap_not_influence_any)
qed

lemma Unmap_fpage_univ:"Inv_Space_HasNot_Loop s \<Longrightarrow> s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2) \<Longrightarrow> v2 \<ge> v \<and> v2 < v + n \<Longrightarrow>
  the (space_mapping (Unmap_fpage s sp v UNIV n) sp1) v1 = None"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
  proof(cases "v2 = v + n")
    case True
    then show ?thesis
      using Suc sys_unmap_univ Unmap_fpage_not_influence_other by auto
  next
    case False
    then have "the (space_mapping (Unmap_fpage s sp v UNIV n) sp1) v1 = None"
      using Suc by simp
    then show ?thesis
      apply simp
      by (metis (full_types) ValidVpageMappingNotNone path_space1 sys_unmap_valid unmap_not_path_space)
  qed
qed

lemma Unmap_fpage_pre1:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x \<Longrightarrow> s\<turnstile>x\<leadsto>\<^sup>1y \<Longrightarrow> (Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x\<leadsto>\<^sup>1y"
  by (metis FatherEqValid Space_Father_Is_Unique Unmap_fpage_direct_eq)

lemma Unmap_fpage_univ_valid:"Inv_Space_HasNot_Loop s \<Longrightarrow> s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2) \<Longrightarrow> v2 \<ge> v \<and> v2 < v + n \<Longrightarrow>
  \<not>(Unmap_fpage s sp v UNIV n)\<turnstile>(Virtual sp1 v1)"
  using Unmap_fpage_univ ValidVpageMappingNotNone
  by simp

lemma Unmap_fpage_univ_valid1:"Inv_Space_Vpage_Range s \<Longrightarrow> Inv_Space_Valid_Has_Real s \<Longrightarrow> 
  Inv_Space_HasNot_Loop s \<Longrightarrow> s\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp v2) \<Longrightarrow> \<not>(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>(Virtual sp1 v1)"
  using Unmap_fpage_univ_valid YIsValid
  by (meson Inv_Space_Vpage_Range_def trans_less_add2)

lemma Unmap_fpage_univ_valid_tran:"s\<turnstile>x\<leadsto>\<^sup>+y \<Longrightarrow> y = (Virtual sp v2) \<Longrightarrow> Inv_Space_Vpage_Range s \<Longrightarrow> Inv_Space_Valid_Has_Real s \<Longrightarrow> 
  Inv_Space_HasNot_Loop s \<Longrightarrow> Inv_Space_Perms_Subset s \<Longrightarrow> \<not>(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x"
proof(induction rule:tran_path.induct)
  case (one_path x y)
  then show ?case using Unmap_fpage_univ_valid1 FatherIsVirtual by blast
next
  case (tran_path x y z)
  then have h1:"\<not>(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y" by simp
  show ?case
  proof
    assume a1:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x"
    then have "(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x\<leadsto>\<^sup>1y" 
      using Unmap_fpage_pre1 tran_path by simp
    then have "(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y" 
      using YIsValid tran_path Unmap_fpage_Inv_Space_Valid_Has_Real by simp
    then show False using tran_path by simp
  qed
qed

lemma DeleteAddressSpace_Inv_Space_Perms_Subset11:
  assumes p1:"Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s \<and> Inv_Space_Vpage_Range s"
      and p2:"sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp"
      and p3:"(DeleteAddressSpace1 s sp)\<turnstile> (Virtual sp1 v1) \<leadsto>\<^sup>1 (Virtual sp2 v2)"
    shows "get_perms ((DeleteAddressSpace1 s sp)) sp1 v1 \<subseteq> get_perms ((DeleteAddressSpace1 s sp)) sp2 v2"
  thm DeleteAddressSpace_auxi_pre1
proof-
  have h1:"s\<turnstile>(Virtual sp1 v1) \<leadsto>\<^sup>1 (Virtual sp2 v2)" using p3 p2 DeleteAddressSpace1_def
     DeleteAddressSpace_auxi_direct_eq Unmap_fpage_direct_eq by metis
  then have h11:"get_perms s sp1 v1 \<subseteq> get_perms s sp2 v2" using p1 Inv_Space_Perms_Subset_def by simp
  from h1 have h12:"sp1 \<noteq> sp2" using p1 Inv_Space_HasNot_Loop_def one_path by blast
  from p3 have h2:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>(Virtual sp1 v1)\<leadsto>\<^sup>1(Virtual sp2 v2)"
    unfolding DeleteAddressSpace1_def using p2 DeleteAddressSpace_auxi_direct_eq by simp
  then have h21:"get_perms (Unmap_fpage s sp 0 UNIV page_maxnum) sp1 v1 \<subseteq>
                 get_perms (Unmap_fpage s sp 0 UNIV page_maxnum) sp2 v2"
    using Unmap_fpage_Inv_Space_Perms_Subset p1 h1 Inv_Space_Perms_Subset_def by simp
  have h3:"sp \<noteq> sp1" using DeleteAddressSpace_auxi_pre1 p2 p3 DeleteAddressSpace1_def
    by fastforce
  then have h31:"get_perms (DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp) sp1 v1 = 
                 get_perms (Unmap_fpage s sp 0 UNIV page_maxnum) sp1 v1"
    using DeleteAddressSpace_auxi_perms by simp
  have h4:"sp \<noteq> sp2" 
  proof
    thm p3[unfolded direct_path_def]
    assume a1:"sp = sp2"
    then have "the (space_mapping (Unmap_fpage s sp 0 UNIV page_maxnum) sp1) v1 = None"
      using Unmap_fpage_univ Inv_Space_Vpage_Range_def h1 valid_page_def p1
      by (metis YIsValid plus_nat.add_0 zero_le)
    then have "the (space_mapping (DeleteAddressSpace1 s sp) sp1) v1 = None"
      unfolding DeleteAddressSpace1_def DeleteAddressSpace_auxi_def using p2 h3
      by auto
    then show False using p3 direct_path_def by auto
  qed
  then have h41:"get_perms (DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp) sp2 v2 = 
                 get_perms (Unmap_fpage s sp 0 UNIV page_maxnum) sp2 v2"
    using DeleteAddressSpace_auxi_perms by simp
  show ?thesis
    unfolding DeleteAddressSpace1_def
    using p2 h21 h31 h41 by simp
qed

lemma DeleteAddressSpace_Inv_Space_Perms_Subset1:
  assumes p1:"Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s \<and> Inv_Space_Vpage_Range s"
      and p2:"sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp"
    shows "Inv_Space_Perms_Subset (DeleteAddressSpace1 s sp)"
  unfolding Inv_Space_Perms_Subset_def
  using p1 p2 DeleteAddressSpace_Inv_Space_Perms_Subset11
  by metis

lemma DeleteAddressSpace_Inv_Space_Perms_Subset2:
  assumes p1:"Inv_Space_Perms_Subset s"
      and p2:"\<not>(sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp)"
    shows "Inv_Space_Perms_Subset (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def
  using p1 p2 by auto

lemma DeleteAddressSpace_Inv_Space_Perms_Subset:
  assumes p1:"Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Valid_Has_Real s \<and> Inv_Space_Vpage_Range s"
    shows "Inv_Space_Perms_Subset (DeleteAddressSpace s sp)"
  using p1 DeleteAddressSpace_Inv_Space_Perms_Subset1 DeleteAddressSpace_Inv_Space_Perms_Subset2
    DeleteAddressSpace_eq
  by auto

lemma DeleteAddressSpace_Inv_Space_Valid_Has_Real11:
  assumes p1:"Inv_Space_Valid_Has_Real s \<and> Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Vpage_Range s"
      and p2:"sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp"
      and p3:"(DeleteAddressSpace1 s sp)\<turnstile>x"
    shows "\<exists>r. (DeleteAddressSpace1 s sp) \<turnstile> x \<leadsto>\<^sup>* (Real r)"
proof(cases x)
  case (Virtual x11 x12)
  from p3 have h1:"s\<turnstile>x" 
    using DeleteAddressSpace_valid DeleteAddressSpace_eq by simp
  then have "\<exists>r. s \<turnstile> x \<leadsto>\<^sup>* (Real r)" 
    using p1 Inv_Space_Valid_Has_Real_def by simp
  then have "\<exists>r. s \<turnstile> x \<leadsto>\<^sup>+ (Real r)" 
    using Virtual rtran_tran by simp
  then obtain r1 where h11:"s \<turnstile> x \<leadsto>\<^sup>+ (Real r1)" by auto
  then have "\<exists>y. s \<turnstile> x \<leadsto>\<^sup>1 y" using basic3 by simp
  then obtain y1 where h111:"s \<turnstile> x \<leadsto>\<^sup>1 y1 \<and> s \<turnstile> y1 \<leadsto>\<^sup>* (Real r1)"
    using basic15 h11 by blast

  have h2:"(Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> x"
    using DeleteAddressSpace_auxi_valid p3 p2 DeleteAddressSpace1_def by auto
  then have "\<exists>r. (Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> x \<leadsto>\<^sup>* (Real r)"
    using Unmap_fpage_Inv_Space_Valid_Has_Real p1 Inv_Space_Valid_Has_Real_def by auto
  then have "\<exists>r. (Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> x \<leadsto>\<^sup>+ (Real r)"
    using Virtual rtran_tran by simp
  then obtain r2 where h21:"(Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> x \<leadsto>\<^sup>+ (Real r2)" by auto
  then have "\<exists>y. (Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> x \<leadsto>\<^sup>1 y" using basic3 by simp
  then obtain y2 where h211:"(Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> x \<leadsto>\<^sup>1 y2 \<and> 
    (Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> y2 \<leadsto>\<^sup>* (Real r2)" using basic15 h21 by blast

  have h3:"y1 = y2" using h111 h211 Space_Father_Is_Unique Unmap_fpage_direct_eq by blast
  have h4:"r1 = r2" using h11 h21 Unmap_fpage_tran
    by (meson Real_HasNo_Father_tran basic16 page_t.inject(2) rtran_tran)
  
  have h5:"\<And>z. (Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> y2 \<leadsto>\<^sup>* z \<Longrightarrow> 
      (Unmap_fpage s sp 0 UNIV page_maxnum) \<turnstile> z \<leadsto>\<^sup>+ (Real r2) \<Longrightarrow> sp_name z \<noteq> sp"
  proof
    fix z
    assume a1:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y2\<leadsto>\<^sup>*z" and 
       a2:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>z\<leadsto>\<^sup>+(Real r2)" and 
       a3:"sp_name z = sp"
    then have "(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y2\<leadsto>\<^sup>+z \<or> y2 = z" 
      using rtran_tran by blast
    then show False
    proof
      assume a11:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y2\<leadsto>\<^sup>+z"
      then have h51:"s\<turnstile>y2\<leadsto>\<^sup>+z" using Unmap_fpage_tran by simp
      have h52:"\<exists>v. z = Virtual sp v" using a3 a2
        by (metis FatherIsValid basic3 page_t.exhaust_sel)
      then have h53:"\<not>(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y2"
        using p1 h51 Unmap_fpage_univ_valid_tran by blast
      have h54:"(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>y2"
        using a11 FatherEqValid PlusEqOneStar by auto
      then show ?thesis using h53 by simp
    next
      assume a12:"y2=z"
      have h121:"\<exists>sp2 v2. y2 = Virtual sp2 v2"
        using FatherIsVirtual a12 a2 basic3 by blast
      then obtain sp2 v2 where h1211:"y2 = Virtual sp2 v2" by auto
      have h122:"s\<turnstile>y2" using YIsValid h111 h3 p1 by blast
      then have h1221:"v2 \<ge> 0 \<and> v2 < page_maxnum" 
        using p1 Inv_Space_Vpage_Range_def h1211 h122 by simp
      then have "\<not>(Unmap_fpage s sp 0 UNIV page_maxnum)\<turnstile>x"
        using Unmap_fpage_univ p1 h111 h3 h1211 h1221 Virtual 
          valid_page_def direct_path_def a12 a3 by fastforce
      then show ?thesis using h2 by simp
    qed
  qed
  thm DeleteAddressSpace_auxi_pre3
  have h6:"(DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp) \<turnstile> x \<leadsto>\<^sup>1 y2"
    using  Space_Father_Is_Unique h211 p2 p3 valid_page_def DeleteAddressSpace1_def
    by (simp add: DeleteAddressSpace_auxi_pre DeleteAddressSpace_auxi_pre2 Virtual)
  have h7:"(DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp) \<turnstile> y2 \<leadsto>\<^sup>* (Real r2)"
  proof(cases y2)
    case (Virtual x11 x12)
    then have "(DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp)\<turnstile>y2\<leadsto>\<^sup>+(Real r2)"
      using h5 DeleteAddressSpace_auxi_pre3 h211 rtran_tran by simp
    then show ?thesis using Virtual
      by (simp add: rtran_tran)
  next
    case (Real x2)
    then show ?thesis using refl_path Real_HasNo_Father_tran h211 rtran_tran by auto
  qed
  have "(DeleteAddressSpace_auxi (Unmap_fpage s sp 0 UNIV page_maxnum) sp) \<turnstile> x \<leadsto>\<^sup>+ (Real r2)"
    using h6 h7 basic111 by blast
  then have "\<exists>r. (DeleteAddressSpace1 s sp) \<turnstile> x \<leadsto>\<^sup>+ (Real r)"
    using DeleteAddressSpace1_def p2 by auto
  then show ?thesis using Virtual
    by (simp add: rtran_tran)
next
  case (Real x2)
  then show ?thesis using refl_path by blast
qed            

lemma DeleteAddressSpace_Inv_Space_Valid_Has_Real12:
  assumes p1:"Inv_Space_Valid_Has_Real s"
      and p2:"sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp"
      and p3:"\<exists>r. (DeleteAddressSpace1 s sp) \<turnstile> x \<leadsto>\<^sup>* (Real r)"
    shows "(DeleteAddressSpace1 s sp)\<turnstile>x"
proof(cases x)
  case (Virtual x11 x12)
  from p3 have h1:"\<exists>r. (DeleteAddressSpace1 s sp) \<turnstile> x \<leadsto>\<^sup>+ (Real r)"
    by (simp add: Virtual rtran_tran)
  then show ?thesis using basic3 valid_page_def FatherEqValid by blast
next
  case (Real x2)
  then show ?thesis using valid_page_def by simp
qed

lemma DeleteAddressSpace_Inv_Space_Valid_Has_Real1:
  assumes p1:"Inv_Space_Valid_Has_Real s  \<and> Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Vpage_Range s"
      and p2:"sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp"
    shows "Inv_Space_Valid_Has_Real (DeleteAddressSpace1 s sp)"
  using p1 p2 DeleteAddressSpace_Inv_Space_Valid_Has_Real11
  DeleteAddressSpace_Inv_Space_Valid_Has_Real12 Inv_Space_Valid_Has_Real_def
  by metis

lemma DeleteAddressSpace_Inv_Space_Valid_Has_Real2:
  assumes p1:"Inv_Space_Valid_Has_Real s"
      and p2:"\<not>(sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp)"
  shows "Inv_Space_Valid_Has_Real (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def
  using p1 p2 by auto

lemma DeleteAddressSpace_Inv_Space_Valid_Has_Real:
  assumes p1:"Inv_Space_Valid_Has_Real s  \<and> Inv_Space_Perms_Subset s \<and> Inv_Space_HasNot_Loop s \<and> Inv_Space_Vpage_Range s"
    shows "Inv_Space_Valid_Has_Real (DeleteAddressSpace s sp)"
  using p1 DeleteAddressSpace_Inv_Space_Valid_Has_Real1 DeleteAddressSpace_Inv_Space_Valid_Has_Real2
    DeleteAddressSpace_eq
  by auto

lemma DeleteAddressSpace_Inv_Space_Spaces_In_Config:
  assumes p1:"Inv_Space_Spaces_In_Config s"
    shows "Inv_Space_Spaces_In_Config (DeleteAddressSpace s sp)"
  unfolding Inv_Space_Spaces_In_Config_def 
  using p1[unfolded Inv_Space_Spaces_In_Config_def]
     DeleteAddressSpace_NC_Space DeleteAddressSpace_C_Space
  using DiffD1 by blast

lemma DeleteAddressSpace_Inv_Space_InitialSpaces_In_Spaces:
  assumes p1:"Inv_Space_InitialSpaces_In_Spaces s"
    shows "Inv_Space_InitialSpaces_In_Spaces (DeleteAddressSpace s sp)"
  unfolding Inv_Space_InitialSpaces_In_Spaces_def 
  using p1[unfolded Inv_Space_InitialSpaces_In_Spaces_def]
     DeleteAddressSpace_NC_Space DeleteAddressSpace_C_Space
  by blast

lemma DeleteAddressSpace_Inv_Space_Spaces_IsNot_None:
  assumes p1:"Inv_Space_Spaces_IsNot_None s"
  shows "Inv_Space_Spaces_IsNot_None (DeleteAddressSpace s sp)"
  using p1 Inv_Space_Spaces_IsNot_None_def
  unfolding DeleteAddressSpace_def Let_def spaces_def
  by (auto simp add:Unmap_fpage_NC_Space)

lemma DeleteAddressSpace_Inv_Space:
  assumes p1:"Inv_Space s"
    shows "Inv_Space (DeleteAddressSpace s sp)"
  unfolding Inv_Space_def
  using DeleteAddressSpace_Inv_Space_HasNot_Loop DeleteAddressSpace_Inv_Space_Valid_Has_Real
   DeleteAddressSpace_Inv_Space_Perms_IsNot_Empty DeleteAddressSpace_Inv_Space_Spaces_In_Config 
   DeleteAddressSpace_Inv_Space_InitialSpaces_In_Spaces DeleteAddressSpace_Inv_Space_Perms_Subset
   DeleteAddressSpace_Inv_Space_Spaces_IsNot_None DeleteAddressSpace_Inv_Space_Vpage_Range 
   p1[unfolded Inv_Space_def]
  by auto

subsection\<open>Thread\<close>
lemma DeleteAddressSpace_Inv_Idle_NotIn_Threads:
  assumes p1:"Inv_Idle_NotIn_Threads s"
    shows "Inv_Idle_NotIn_Threads (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Idle_NotIn_Threads_def Let_def
  using p1[unfolded Inv_Idle_NotIn_Threads_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_Idle_Space_Is_KernelSpace:
  assumes p1:"Inv_Idle_Space_Is_KernelSpace s"
  shows "Inv_Idle_Space_Is_KernelSpace (DeleteAddressSpace s sp)"
  using assms unfolding Inv_Idle_Space_Is_KernelSpace_def
  using DeleteAddressSpace_NC_Thread 
  by auto

lemma DeleteAddressSpace_Inv_Sigma0_In_Active:
  assumes p1:"Inv_Sigma0_In_Active s"
    shows "Inv_Sigma0_In_Active (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Sigma0_In_Active_def Let_def
  using p1[unfolded Inv_Sigma0_In_Active_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_RootServer_In_Active:
  assumes p1:"Inv_RootServer_In_Active s"
    shows "Inv_RootServer_In_Active (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_RootServer_In_Active_def Let_def
  using p1[unfolded Inv_RootServer_In_Active_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_IntThreads_In_Active:
  assumes p1:"Inv_IntThreads_In_Active s"
    shows "Inv_IntThreads_In_Active (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_IntThreads_In_Active_def Let_def
  using p1[unfolded Inv_IntThreads_In_Active_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_Threads_Space_Dom:
  assumes p1:"Inv_Threads_Space_Dom s"
    shows "Inv_Threads_Space_Dom (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Threads_Space_Dom_def Let_def
  using p1[unfolded Inv_Threads_Space_Dom_def] Unmap_fpage_NC_Thread
  by auto
  
lemma DeleteAddressSpace_Inv_Threads_In_Config:
  assumes p1:"Inv_Threads_In_Config s"
    shows "Inv_Threads_In_Config (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Threads_In_Config_def Let_def
  using p1[unfolded Inv_Threads_In_Config_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_Active_In_Threads:
  assumes p1:"Inv_Active_In_Threads s"
    shows "Inv_Active_In_Threads (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Active_In_Threads_def Let_def
  using p1[unfolded Inv_Active_In_Threads_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_NThreads_Is_None:
  assumes p1:"Inv_NThreads_Is_None s"
    shows "Inv_NThreads_Is_None (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_NThreads_Is_None_def Let_def
  using p1[unfolded Inv_NThreads_Is_None_def] Unmap_fpage_NC_Thread
    Unmap_fpage_NC_IPC Unmap_fpage_NC_User
  by auto

lemma DeleteAddressSpace_Inv_Threads_IsNot_None:
  assumes p1:"Inv_Threads_IsNot_None s"
    shows "Inv_Threads_IsNot_None (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Threads_IsNot_None_def Let_def
  using p1[unfolded Inv_Threads_IsNot_None_def] Unmap_fpage_NC_Thread
    Unmap_fpage_NC_IPC
  by auto

lemma DeleteAddressSpace_Inv_Threads_Sche_In_Threads:
  assumes p1:"Inv_Threads_Sche_In_Threads s"
    shows "Inv_Threads_Sche_In_Threads (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Threads_Sche_In_Threads_def Let_def
  using p1[unfolded Inv_Threads_Sche_In_Threads_def] Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_NActive_Utcb_Is_None:
  assumes p1:"Inv_NActive_Utcb_Is_None s"
    shows "Inv_NActive_Utcb_Is_None (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_NActive_Utcb_Is_None_def Let_def
  using p1[unfolded Inv_NActive_Utcb_Is_None_def] Unmap_fpage_NC_Thread
    Unmap_fpage_NC_User
  by auto

lemma DeleteAddressSpace_Inv_Active_Utcb_IsNot_None:
  assumes p1:"Inv_Active_Utcb_IsNot_None s"
    shows "Inv_Active_Utcb_IsNot_None (DeleteAddressSpace s sp)"
  unfolding DeleteAddressSpace_def Inv_Active_Utcb_IsNot_None_def Let_def
  using p1[unfolded Inv_Active_Utcb_IsNot_None_def] Unmap_fpage_NC_Thread
    Unmap_fpage_NC_User
  by auto

lemma DeleteAddressSpace_Inv_IntThreads_Utcb_Is_None:
  assumes p1:"Inv_IntThreads_Utcb_Is_None s"
    shows "Inv_IntThreads_Utcb_Is_None (DeleteAddressSpace s sp)"
  unfolding Inv_IntThreads_Utcb_Is_None_def DeleteAddressSpace_def Let_def
  using p1[unfolded Inv_IntThreads_Utcb_Is_None_def] Unmap_fpage_NC_User
    Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_Threads_Partner_In_Threads:
  assumes p1:"Inv_Threads_Partner_In_Threads s"
  shows "Inv_Threads_Partner_In_Threads (DeleteAddressSpace s sp)"
  unfolding Inv_Threads_Partner_In_Threads_def
  using p1[unfolded Inv_Threads_Partner_In_Threads_def] 
    DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_IPC
  by auto

lemma DeleteAddressSpace_Inv_Threads_Incoming_In_Threads:
  assumes p1:"Inv_Threads_Incoming_In_Threads s"
  shows "Inv_Threads_Incoming_In_Threads (DeleteAddressSpace s sp)"
  unfolding Inv_Threads_Incoming_In_Threads_def
  using p1[unfolded Inv_Threads_Incoming_In_Threads_def] 
    DeleteAddressSpace_NC_Thread DeleteAddressSpace_NC_IPC
  by auto

lemma DeleteAddressSpace_Inv_Sigma0_Space:
  assumes "Inv_Sigma0_Space s"
  shows "Inv_Sigma0_Space (DeleteAddressSpace s sp)"
  using assms unfolding Inv_Sigma0_Space_def DeleteAddressSpace_def Let_def
  using Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_RootServer_Space:
  assumes "Inv_RootServer_Space s"
  shows "Inv_RootServer_Space (DeleteAddressSpace s sp)"
  using assms unfolding Inv_RootServer_Space_def DeleteAddressSpace_def Let_def
  using Unmap_fpage_NC_Thread
  by auto

lemma DeleteAddressSpace_Inv_IntThreads_Space:
  assumes "Inv_IntThreads_Space s"
  shows "Inv_IntThreads_Space (DeleteAddressSpace s sp)"
  using assms unfolding Inv_IntThreads_Space_def DeleteAddressSpace_def Let_def
  using Unmap_fpage_NC_Thread
  by auto

end