theory L4_Inv_s0
  imports "L4_Thread_Lemmas"
begin

section\<open>s0_req\<close>
subsection\<open>Current\<close>
lemma s0_Inv_Current_Thread_In_Active:
"Inv_Current_Thread_In_Active s0_req"
  unfolding S0ReqInit System_Init_def Inv_Current_Thread_In_Active_def
  by auto

lemma s0_Inv_Current_Space_IsNot_None:
"Inv_Current_Space_IsNot_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_Current_Space_IsNot_None_def
  by auto

lemma s0_Inv_Current:
"Inv_Current s0_req"
  using s0_Inv_Current_Thread_In_Active s0_Inv_Current_Space_IsNot_None
    Inv_Current_def
  by auto

subsection\<open>Space\<close>
lemma Real_HasNo_Father:"\<not>s\<turnstile>(Real r)\<leadsto>\<^sup>1x"
  unfolding direct_path_def by simp

lemma Real_HasNo_Father_tran:"\<not>s\<turnstile>(Real r)\<leadsto>\<^sup>+x"
  using Real_HasNo_Father tran_path.simps by blast

lemma s0_One_Path_Sigma0Space:
"v_page < page_maxnum \<Longrightarrow> s0_req\<turnstile>(Virtual Sigma0Space v_page)\<leadsto>\<^sup>1(Real v_page)"
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by auto

lemma s0_Tran_Path_Sigma0Space:
"v_page < page_maxnum \<Longrightarrow> s0_req\<turnstile>(Virtual Sigma0Space v_page)\<leadsto>\<^sup>+(Real v_page)"
  apply(subst tran_path.simps)
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by auto

lemma s0_One_Path_Sigma0Space_Unique:
"v_page \<noteq> r \<Longrightarrow> \<not>s0_req\<turnstile>(Virtual Sigma0Space v_page)\<leadsto>\<^sup>1(Real r)"
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by simp

lemma s0_Tran_Path_Sigma0Space_Unique:
"v_page \<noteq> r \<Longrightarrow> \<not>s0_req\<turnstile>(Virtual Sigma0Space v_page)\<leadsto>\<^sup>+(Real r)"
  apply(subst tran_path.simps)
  apply auto
  subgoal
    using s0_One_Path_Sigma0Space_Unique by simp
  by (smt Space_Father_Is_Unique Real_HasNo_Father_tran S0ReqInit State.simps(22) System_Init_def one_path option.sel path_space1 s0_One_Path_Sigma0Space)

lemma s0_One_Path_RootServerSpace:
"\<not>s0_req\<turnstile>(Virtual RootServerSpace v_page)\<leadsto>\<^sup>1 x"
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by auto

lemma s0_Tran_Path_RootServerSpace:
"\<not>s0_req\<turnstile>(Virtual RootServerSpace v_page)\<leadsto>\<^sup>+ x"
  apply(subst tran_path.simps)
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by auto

lemma s0_One_Path_KernelSpace:
"\<not>s0_req\<turnstile>(Virtual KernelSpace v_page)\<leadsto>\<^sup>1 x"
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by auto

lemma s0_Tran_Path_KernelSpace:
"\<not>s0_req\<turnstile>(Virtual KernelSpace v_page)\<leadsto>\<^sup>+ x"
  apply(subst tran_path.simps)
  unfolding S0ReqInit System_Init_def direct_path_def
  using PriSpacesConfigLemma
  by auto

lemma Sigm0Space_HasNot_Loop:"\<And>y. s0_req\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>1y \<Longrightarrow>
         s0_req\<turnstile>y\<leadsto>\<^sup>+(Virtual sp v2) \<Longrightarrow>
         sp = Sigma0Space \<Longrightarrow> False"
proof-
  fix y
  assume 
    a1:"s0_req\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>1y" and
    a2:"s0_req\<turnstile>y\<leadsto>\<^sup>+(Virtual sp v2)" and
    a3:"sp = Sigma0Space"
   have a0:"v1 < page_maxnum" 
     using a1 a3 S0ReqInit System_Init_def direct_path_def
     by (smt State.select_convs(22) basic5 one_path)
  have h1:"y = (Real v1)"
    using a1[unfolded direct_path_def S0ReqInit System_Init_def] a3
    PriSpacesConfigLemma
    apply auto
    using Space_Father_Is_Unique a0 a1 s0_One_Path_Sigma0Space by blast
  show False
    using h1 a2 Real_HasNo_Father_tran by simp
qed

lemma s0_Inv_Space_HasNot_Loop_One_Path:"\<not>(s0_req\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>1((Virtual sp v2)))"
  unfolding direct_path_def S0ReqInit System_Init_def
  apply(cases "sp = KernelSpace")
  subgoal
    by auto
  apply(cases "sp = Sigma0Space")
  subgoal
    by auto
  apply(cases "sp = RootServerSpace")
  subgoal
    by auto
  by auto

lemma s0_Inv_Space_HasNot_Loop_Tran_Path:"(\<nexists>y. s0_req\<turnstile>(Virtual sp v1)\<leadsto>\<^sup>1y \<and> s0_req\<turnstile>y\<leadsto>\<^sup>+(Virtual sp v2))"
  apply auto
  apply(cases "sp = KernelSpace")
  subgoal
    unfolding direct_path_def S0ReqInit System_Init_def
    by auto
  apply(cases "sp = Sigma0Space")
  subgoal
    using Sigm0Space_HasNot_Loop by blast
  apply(cases "sp = RootServerSpace")
  subgoal
    unfolding direct_path_def S0ReqInit System_Init_def
    by auto
  unfolding direct_path_def S0ReqInit System_Init_def
  by auto
  
lemma s0_Inv_Space_HasNot_Loop:
"Inv_Space_HasNot_Loop s0_req"
  unfolding Inv_Space_HasNot_Loop_def
  using s0_Inv_Space_HasNot_Loop_One_Path s0_Inv_Space_HasNot_Loop_Tran_Path
    tran_path.simps
  by blast

lemma s0_Inv_Space_Valid_Has_Real1:"s0_req\<turnstile>x \<Longrightarrow> \<exists>r. x = Real r \<or> s0_req\<turnstile>x\<leadsto>\<^sup>+(Real r)"
  apply(cases "\<exists>r. x = Real r")
  subgoal
    by auto
  apply(cases "\<exists>v. x = Virtual Sigma0Space v")
  subgoal
    by (smt S0ReqInit State.simps(22) System_Init_def ValidVpageMappingNotNone option.sel s0_Tran_Path_Sigma0Space)
  apply(cases "\<exists>v. x = Virtual RootServerSpace v")
  subgoal
    unfolding valid_page_def
    using s0_One_Path_RootServerSpace
    by auto
  apply(cases "\<exists>v. x = Virtual KernelSpace v")
  subgoal
    unfolding valid_page_def
    using s0_One_Path_KernelSpace
    by auto
  unfolding valid_page_def direct_path_def
  apply(subgoal_tac "\<And>sp v_page. \<nexists>r. x = Real r \<Longrightarrow> \<nexists>v. x = Virtual Sigma0Space v \<Longrightarrow>
    \<nexists>v. x = Virtual RootServerSpace v \<Longrightarrow> \<nexists>v. x = Virtual KernelSpace v \<Longrightarrow> 
    x = Virtual sp v_page \<Longrightarrow> space_mapping s0_req sp = None")
  subgoal
    using not_None_eq page_t.exhaust page_t.simps(5)
    by smt
  unfolding S0ReqInit System_Init_def
  by auto

lemma s0_Inv_Space_Valid_Has_Real2:"s0_req\<turnstile>x\<leadsto>\<^sup>+(Real r) \<Longrightarrow> s0_req\<turnstile>x"
  apply(cases "\<exists>r. x = Real r")
  subgoal
    using Real_HasNo_Father_tran
    by auto
  apply(cases "\<exists>v. x = Virtual Sigma0Space v")
  subgoal
    unfolding valid_page_def
    using basic3 by auto
  apply(cases "\<exists>v. x = Virtual RootServerSpace v")
  subgoal
    using s0_Tran_Path_RootServerSpace
    by auto
  apply(cases "\<exists>v. x = Virtual KernelSpace v")
  subgoal
    using s0_Tran_Path_KernelSpace
    by auto
  unfolding valid_page_def direct_path_def
  apply(subgoal_tac "\<And>sp v_page. \<nexists>r. x = Real r \<Longrightarrow> \<nexists>v. x = Virtual Sigma0Space v \<Longrightarrow>
    \<nexists>v. x = Virtual RootServerSpace v \<Longrightarrow> \<nexists>v. x = Virtual KernelSpace v \<Longrightarrow> 
    x = Virtual sp v_page \<Longrightarrow> \<not>s0_req\<turnstile>x\<leadsto>\<^sup>+(Real r)")
  subgoal
    using not_None_eq page_t.exhaust page_t.simps(5)
    by smt
  apply(subst tran_path.simps)
  unfolding S0ReqInit System_Init_def direct_path_def
  by auto

lemma s0_Inv_Space_Valid_Has_Real:
"Inv_Space_Valid_Has_Real s0_req"
  unfolding Inv_Space_Valid_Has_Real_def
  apply(subst rtran_tran)
  apply auto
  subgoal
    using s0_Inv_Space_Valid_Has_Real1 by simp
  subgoal
    using valid_page_def by simp
  using s0_Inv_Space_Valid_Has_Real2 
  by simp

lemma s0_Inv_Space_Father_Is_Unique:
"Inv_Space_Father_Is_Unique s0_req"
  unfolding Inv_Space_Father_Is_Unique_def
 S0ReqInit System_Init_def direct_path_def
  by auto

lemma s0_Inv_Space_Path_Is_Unique:
"Inv_Space_Path_Is_Unique s0_req"
  unfolding Inv_Space_Path_Is_Unique_def
  apply auto
  apply(case_tac "sp = KernelSpace")
  subgoal
    using s0_Tran_Path_KernelSpace by simp
  apply(case_tac "sp = Sigma0Space")
  subgoal
    by (metis s0_Tran_Path_Sigma0Space_Unique)
  apply(case_tac "sp = RootServerSpace")
  subgoal
    using s0_Tran_Path_RootServerSpace
    by auto
  apply(subgoal_tac "sp \<noteq> KernelSpace \<Longrightarrow> sp \<noteq> Sigma0Space \<Longrightarrow> sp \<noteq> RootServerSpace \<Longrightarrow>
  \<forall>r. \<not>s0_req\<turnstile>(Virtual sp v_page)\<leadsto>\<^sup>+(Real r)")
  subgoal
    by simp
  apply simp
  apply(subst tran_path.simps)
  unfolding S0ReqInit System_Init_def direct_path_def
  by auto

lemma s0_Inv_Space_Perms_IsNot_Empty:
"Inv_Space_Perms_IsNot_Empty s0_req"
  unfolding Inv_Space_Perms_IsNot_Empty_def get_perms_def valid_page_def direct_path_def
  apply auto
  unfolding S0ReqInit System_Init_def PERMS_def
  apply(case_tac "sp = KernelSpace")
  subgoal
    by auto
  apply(case_tac "sp = Sigma0Space")
  subgoal
    apply auto
    by (metis UNIV_I empty_iff not_None_eq option.simps(1) prod.simps(1))
  apply(case_tac "sp = RootServerSpace")
  subgoal
    by auto
  by auto

lemma s0_Inv_Space_Spaces_In_Config:
"Inv_Space_Spaces_In_Config s0_req"
  unfolding S0ReqInit System_Init_def Inv_Space_Spaces_In_Config_def spaces_def
  apply auto
  using PriSpacesConfigLemma 
    apply(case_tac "x = KernelSpace")
  subgoal
    by auto
  apply(case_tac "x = Sigma0Space")
  subgoal
    by auto
  apply(case_tac "x = RootServerSpace")
  by auto

lemma s0_Inv_Space_InitialSpaces_In_Spaces:
"Inv_Space_InitialSpaces_In_Spaces s0_req"
  unfolding S0ReqInit System_Init_def Inv_Space_InitialSpaces_In_Spaces_def
    spaces_def
  by auto

lemma s0_Inv_Space_Spaces_IsNot_None:
"Inv_Space_Spaces_IsNot_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_Space_Spaces_IsNot_None_def spaces_def
  apply auto
    apply(case_tac "x = KernelSpace")
  subgoal
    by auto
  apply(case_tac "x = Sigma0Space")
  subgoal
    by auto
  apply(case_tac "x = RootServerSpace")
    apply auto
  by (meson option.distinct(1))

lemma s0_Inv_Space_Perms_Subset:
"Inv_Space_Perms_Subset s0_req"
  unfolding S0ReqInit System_Init_def Inv_Space_Perms_Subset_def 
    direct_path_def
  by auto

lemma s0_Inv_Space_Range_Vpage:
"Inv_Space_Vpage_Range s0_req"
  unfolding Inv_Space_Vpage_Range_def
  apply(auto simp add: S0ReqInit System_Init_def valid_page_def direct_path_def)
  apply(case_tac "sp \<noteq> Sigma0Space")
  subgoal
    by (metis option.distinct(1) option.sel)
  apply (auto simp:PriSpacesConfigLemma)
  by (metis option.distinct(1))

lemma s0_Inv_Space:
"Inv_Space s0_req"
  unfolding Inv_Space_def
  using s0_Inv_Space_HasNot_Loop s0_Inv_Space_Valid_Has_Real
   s0_Inv_Space_Perms_IsNot_Empty s0_Inv_Space_Spaces_In_Config 
   s0_Inv_Space_Spaces_IsNot_None s0_Inv_Space_Perms_Subset
   s0_Inv_Space_InitialSpaces_In_Spaces s0_Inv_Space_Range_Vpage
  by auto

subsection\<open>Thread\<close>
lemma s0_Inv_Idle_NotIn_Threads:
"Inv_Idle_NotIn_Threads s0_req"
  unfolding S0ReqInit System_Init_def Inv_Idle_NotIn_Threads_def
  using PriThreadsConfigLemma
  by auto

lemma s0_Inv_Sigma0_In_Active:
  "Inv_Sigma0_In_Active s0_req"
  unfolding S0ReqInit System_Init_def Inv_Sigma0_In_Active_def
  by auto

lemma s0_Inv_Sigma0_Space:
  "Inv_Sigma0_Space s0_req"
  unfolding S0ReqInit System_Init_def Inv_Sigma0_Space_def
  using PriThreadsConfigLemma
  by auto

lemma s0_Inv_IntThreads_Space:
  "Inv_IntThreads_Space s0_req"
  unfolding S0ReqInit System_Init_def Inv_IntThreads_Space_def
  by auto

lemma s0_Inv_RootServer_Space:
  "Inv_RootServer_Space s0_req"
  unfolding S0ReqInit System_Init_def Inv_RootServer_Space_def
  using PriThreadsConfigLemma
  by auto

lemma s0_Inv_Idle_Space_Is_KernelSpace:
"Inv_Idle_Space_Is_KernelSpace s0_req"
  unfolding S0ReqInit System_Init_def Inv_Idle_Space_Is_KernelSpace_def
  using PriThreadsConfigLemma
  by auto

lemma s0_Inv_RootServer_In_Active:
"Inv_RootServer_In_Active s0_req"
  unfolding S0ReqInit System_Init_def Inv_RootServer_In_Active_def
  by auto

lemma s0_Inv_IntThreads_In_Active:
"Inv_IntThreads_In_Active s0_req"
  unfolding S0ReqInit System_Init_def Inv_IntThreads_In_Active_def
  by auto

lemma s0_Inv_Threads_Space_Dom:
"Inv_Threads_Space_Dom s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_Space_Dom_def
  using PriThreadsConfigLemma by auto

lemma s0_Inv_Threads_In_Config:
"Inv_Threads_In_Config s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_In_Config_def
  using PriThreadsConfigLemma by auto

lemma s0_Inv_Active_In_Threads:
"Inv_Active_In_Threads s0_req"
  unfolding S0ReqInit System_Init_def Inv_Active_In_Threads_def
  by auto

lemma s0_Inv_NThreads_Is_None:
"Inv_NThreads_Is_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_NThreads_Is_None_def
  using PriThreadsConfigLemma by auto

lemma s0_Inv_Threads_IsNot_None:
"Inv_Threads_IsNot_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_IsNot_None_def
  by auto

lemma s0_Inv_Threads_Space_In_Spaces:
"Inv_Threads_Space_In_Spaces s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_Space_In_Spaces_def spaces_def
  by auto

lemma s0_Inv_Threads_Eq_Space_Threads:
"Inv_Threads_Eq_Space_Threads s0_req"
proof-
  have h1:"spaces s0_req = {KernelSpace, Sigma0Space, RootServerSpace}"
    unfolding S0ReqInit System_Init_def spaces_def apply auto
    by (meson option.distinct(1))
  have h2:"thread_space s0_req = ((\<lambda>t. (if t \<in> kIntThreads
                        then Some KernelSpace
                        else 
                      if t = kSigma0
                        then Some Sigma0Space
                        else
                      if t = kRootServer
                        then Some RootServerSpace
                        else
                      if t = idle
                        then Some KernelSpace
                        else None 
                     )
                ))" 
    unfolding S0ReqInit System_Init_def by simp
  have h3:"space_threads s0_req = (\<lambda>sp. (if sp = KernelSpace
                          then Some (kIntThreads \<union> {idle})
                          else 
                        if sp = Sigma0Space
                          then Some {kSigma0}
                          else
                        if sp = RootServerSpace
                          then Some {kRootServer}
                          else None))"
    unfolding S0ReqInit System_Init_def by simp
  show ?thesis unfolding Inv_Threads_Eq_Space_Threads_def
    apply(subst h1)
    apply auto
    using IdleDiff h2 h3 apply auto[1]
    apply (metis PriSpacesConfigLemma Un_insert_right h2 h3 insertCI option.sel option.simps(3) sup_bot.right_neutral)
    using PriSpacesConfigLemma PriThreadsConfigLemma h2 h3 apply auto[1]
    apply (metis PriSpacesConfigLemma h2 h3 insertCI option.sel option.simps(3))
    using PriThreadsConfigLemma SpaceDiff h2 h3 apply auto[1] 
    by (metis SpaceDiff h2 h3 insertCI option.sel option.simps(3))
qed

lemma s0_Inv_Threads_Sche_In_Threads:
"Inv_Threads_Sche_In_Threads s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_Sche_In_Threads_def
  by auto

lemma s0_Inv_NActive_Utcb_Is_None:
"Inv_NActive_Utcb_Is_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_NActive_Utcb_Is_None_def
  by auto

lemma s0_Inv_Active_Utcb_IsNot_None:
"Inv_Active_Utcb_IsNot_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_Active_Utcb_IsNot_None_def
  by auto

lemma s0_Inv_IntThreads_Utcb_Is_None:
"Inv_IntThreads_Utcb_Is_None s0_req"
  unfolding S0ReqInit System_Init_def Inv_IntThreads_Utcb_Is_None_def
  using PriThreadsConfigLemma
  by auto

lemma s0_Inv_Threads_Partner_In_Threads:
"Inv_Threads_Partner_In_Threads s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_Partner_In_Threads_def
  by auto

lemma s0_Inv_Threads_Incoming_In_Threads:
"Inv_Threads_Incoming_In_Threads s0_req"
  unfolding S0ReqInit System_Init_def Inv_Threads_Incoming_In_Threads_def
  by auto

lemma s0_Inv_Thread:
"Inv_Thread s0_req"
  unfolding Inv_Thread_def
  using s0_Inv_Idle_NotIn_Threads s0_Inv_Sigma0_In_Active s0_Inv_Idle_Space_Is_KernelSpace
    s0_Inv_Idle_NotIn_Threads s0_Inv_Idle_Space_Is_KernelSpace
    s0_Inv_Sigma0_Space s0_Inv_IntThreads_Space
    s0_Inv_RootServer_Space s0_Inv_Sigma0_In_Active 
    s0_Inv_RootServer_In_Active s0_Inv_IntThreads_In_Active 
    s0_Inv_Threads_In_Config s0_Inv_Active_In_Threads 
    s0_Inv_NThreads_Is_None s0_Inv_Threads_IsNot_None 
    s0_Inv_Threads_Space_In_Spaces s0_Inv_Threads_Eq_Space_Threads
    s0_Inv_Threads_Sche_In_Threads s0_Inv_Threads_Space_Dom
    s0_Inv_NActive_Utcb_Is_None s0_Inv_Active_Utcb_IsNot_None
    s0_Inv_IntThreads_Utcb_Is_None 
    s0_Inv_Threads_Partner_In_Threads s0_Inv_Threads_Incoming_In_Threads
  by auto
end