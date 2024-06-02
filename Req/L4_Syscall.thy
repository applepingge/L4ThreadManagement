theory L4_Syscall
imports L4_WeakSyscall
begin

subsection\<open> Events Specification (system calls) \<close>

definition ThreadControl_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> bool" where
"ThreadControl_Cond SysConf S destNo spaceSpec schedNo pagerNo \<equiv>
    (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and>
    (thread_state S (current_thread S) = Some tsRunning) \<and> 
    (destNo \<in> GLOBAL_TID SysConf) \<and> (spaceSpec \<in> GLOBAL_TID SysConf) \<and>
    (schedNo \<in> GLOBAL_TID SysConf) \<and> (pagerNo \<in> GLOBAL_TID SysConf)"

definition ThreadControl_Delete_Cond::"State \<Rightarrow> threadid_t \<Rightarrow> bool" where
"ThreadControl_Delete_Cond S destNo \<equiv>
  (destNo \<in> GetThreadsTids S) \<and> (destNo \<noteq> GnoToTid (current_thread S)) \<and>
  (thread_space S (TidToGno destNo) \<noteq> Some Sigma0Space) \<and>
  (thread_space S (TidToGno destNo) \<noteq> Some RootServerSpace) \<and>
  (thread_space S (TidToGno destNo) \<noteq> Some KernelSpace)"

definition ThreadControl_Create_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> bool" where
"ThreadControl_Create_Cond SysConf S destNo spaceSpec schedNo pagerNo \<equiv>
    (destNo \<in> GLOBAL_GNO SysConf) \<and> (spaceSpec \<in> GLOBAL_GNO SysConf) \<and> (schedNo \<in> GetThreadsTids S) \<and>
    (pagerNo \<in> (GetThreadsTids S \<union> {NILTHREAD})) \<and> (threads S \<noteq> Threads_Gno SysConf) \<and>
    (spaceSpec = destNo \<longrightarrow> spaces S \<noteq> Address_Space SysConf) \<and>
    (spaceSpec \<noteq> destNo \<longrightarrow> (spaceSpec \<in> GetThreadsTids S) \<and> GetThreadSpace S (TidToGno spaceSpec) \<in> spaces S) \<and>
    ((pagerNo \<in> GetThreadsTids S) \<longrightarrow>  (spaceSpec \<in> GetThreadsTids S) \<and> (GetThreadSpace S (TidToGno spaceSpec) \<in> initialised_spaces S) \<and> 
           (TidToGno schedNo \<in> active_threads S)) \<and>
    ((spaceSpec \<in> GetThreadsTids S) \<longrightarrow> 
                (GetSpaceThreadsNums S (GetThreadSpace S (TidToGno spaceSpec)) < MaxThreadsPerSpace SysConf))"

definition ThreadControl_Modify_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> bool" where
"ThreadControl_Modify_Cond SysConf S destNo spaceSpec schedNo pagerNo \<equiv>
  (destNo \<in> GetThreadsTids S) \<and> (spaceSpec \<in> GetThreadsTids S) \<and>
  (schedNo \<in> GetThreadsTids S \<union> {NILTHREAD}) \<and> (pagerNo \<in> GetThreadsTids S \<union> {NILTHREAD}) \<and>
  ((pagerNo \<noteq> NILTHREAD) \<longrightarrow> GetThreadSpace S (TidToGno spaceSpec) \<in> initialised_spaces S) \<and>
  ((pagerNo \<noteq> NILTHREAD) \<and> (destNo \<notin> GetActiveThreadsTids S) \<longrightarrow> 
      ((schedNo \<noteq> NILTHREAD) \<longrightarrow> (TidToGno schedNo \<in> active_threads S)) \<and> 
      ((schedNo = NILTHREAD) \<longrightarrow> (GetThreadScheduler S (TidToGno destNo) \<in> active_threads S))) \<and>
  (GetThreadSpace S (TidToGno spaceSpec) \<noteq> GetThreadSpace S (TidToGno destNo) \<longrightarrow>
      GetSpaceThreadsNums S (GetThreadSpace S (TidToGno spaceSpec)) < MaxThreadsPerSpace SysConf)"

definition ThreadControl::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"ThreadControl SysConf S destNo spaceSpec schedNo pagerNo =
(if ThreadControl_Cond SysConf S destNo spaceSpec schedNo pagerNo
 then (if \<not> dIsPrivilegedSpace ( GetCurrentSpace S)
       then SetError S (current_thread S) eNoPrivilege
       else (if spaceSpec = NILTHREAD 
               then (if ThreadControl_Delete_Cond S destNo
                     then WeakDeleteThread SysConf S destNo
                     else SetError S (current_thread S) (SOME e. e\<in>{eUnavailableThread,eNoPrivilege}))
               else
            (if (spaceSpec \<noteq> NILTHREAD) \<and> (destNo \<notin> GetThreadsTids S)
               then (if ThreadControl_Create_Cond SysConf S destNo spaceSpec schedNo pagerNo
                     then WeakCreateThread SysConf S destNo spaceSpec schedNo pagerNo
                     else SetError S (current_thread S) (SOME e. e \<in>{eInvalidSpace,eUnavailableThread,eInvalidScheduler,
                              eUnavailableThread,eOutOfMemory}))
               else
            (if (spaceSpec \<noteq> NILTHREAD) \<and> (destNo \<in> GetThreadsTids S) \<and> (TidToGno destNo \<notin> kIntThreads)
               then (if ThreadControl_Modify_Cond SysConf S destNo spaceSpec schedNo pagerNo
                     then WeakModifyThread SysConf S destNo spaceSpec schedNo pagerNo
                     else SetError S (current_thread S) (SOME e. e \<in>{eInvalidSpace,eUnavailableThread,eInvalidScheduler,eOutOfMemory}))
               else
            (if (spaceSpec \<noteq> NILTHREAD) \<and> (destNo \<in> GetThreadsTids S) \<and> (TidToGno destNo \<in> kIntThreads)
               then (if pagerNo \<in> GetThreadsTids S 
                      then IntThreadControl SysConf S destNo pagerNo
                      else SetError S (current_thread S) eUnavailableThread)
               else S)))))
 else S)"

definition SpaceControl::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> nat \<Rightarrow> fpage_t \<Rightarrow> fpage_t \<Rightarrow> State" where
"SpaceControl SysConf S spaceSpec control KernelInterfacePageArea UtcbArea = 
(if (current_thread S \<in> threads S) \<and>
    (current_thread S \<in> active_threads S) \<and>
    (current_thread S \<notin> kIntThreads) \<and>
    (thread_state S (current_thread S) = Some tsRunning) \<and>
    (spaceSpec \<in> Threads_Gno SysConf)
 then (if dIsPrivilegedSpace (GetThreadSpace S (current_thread S)) \<and>
          spaceSpec \<in> threads S \<and>
          (GetThreadSpace S spaceSpec) \<in> spaces S
       then (if cond
             then SetError (InitialiseAddressSpace S (GetThreadSpace S spaceSpec)) (current_thread S) eNoError
             else SetError S (current_thread S) (SOME e. e \<in> {eInvalidUtcbArea, eInvalidKipArea}))
       else SetError S (current_thread S) (SOME e. e \<in> {eNoPrivilege, eInvalidSpace}))
 else S)"

definition ExchangeRegister::" Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> control_t set\<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> globalid_t \<Rightarrow> nat \<Rightarrow> State" where
"ExchangeRegister SysConf S gno control sp ip flags pager handle = 
(if (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and> (thread_state S (current_thread S) = Some tsRunning) \<and>
    (gno \<in> Threads_Gno SysConf) \<and> (pager \<in> Threads_Gno SysConf)
 then (if gno \<in> active_threads S \<and> (the (thread_space S gno) = GetCurrentSpace S)
       then(if cond
            then Weak_Exregs SysConf S gno control pager
            else SetError S (current_thread S) (SOME e. e \<in> {eOutOfMemory, eInvalidUtcbLocation}))
       else SetError S (current_thread S) eInvalidThread)
 else S)"

definition Schedule::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> State" where
"Schedule SysConf S destNo timeControl procControl prio preemptControl = 
(if (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and> (thread_state S (current_thread S) = Some tsRunning) \<and>
    (destNo \<in> GLOBAL_TID SysConf)
 then (if TidToGno destNo \<notin> active_threads S
          then SetError S (current_thread S) eInvalidThread
          else
      (if GetThreadScheduler S (TidToGno destNo) \<notin> active_threads S
          then SetError S (current_thread S) eNoPrivilege
          else
      (if GetThreadSpace S (GetThreadScheduler S (TidToGno destNo)) \<noteq> GetThreadSpace  S (current_thread S)
          then SetError S (current_thread S) eNoPrivilege
          else do_schedule S (TidToGno destNo) timeControl prio)))
 else S)"

end