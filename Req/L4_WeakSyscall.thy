theory L4_WeakSyscall
  imports L4_Thread
begin

definition WeakCreateThread_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> bool" where
"WeakCreateThread_Cond SysConf s destNo spaceSpecifier schedNo pagerNo \<equiv>
    (current_thread s \<in> active_threads s) \<and> (dIsPrivilegedSpace (GetCurrentSpace s)) \<and> 
    (destNo \<in> GLOBAL_GNO SysConf) \<and> (destNo \<notin> GetThreadsTids s) \<and> (spaceSpecifier \<in> GLOBAL_GNO SysConf) \<and> 
    (schedNo \<in> GetThreadsTids s) \<and> (pagerNo \<in> (GetThreadsTids s \<union> {NILTHREAD})) \<and> (threads s \<noteq> Threads_Gno SysConf) \<and>
    (spaceSpecifier = destNo \<longrightarrow> spaces s \<noteq> Address_Space SysConf) \<and>
    (spaceSpecifier \<noteq> destNo \<longrightarrow> (spaceSpecifier \<in> GetThreadsTids s) \<and> GetThreadSpace s (TidToGno spaceSpecifier) \<in> spaces s) \<and>
    ((pagerNo \<in> GetThreadsTids s) \<longrightarrow> (spaceSpecifier \<in> GetThreadsTids s) \<and> (GetThreadSpace s (TidToGno spaceSpecifier) \<in> initialised_spaces s) \<and> 
                                        (TidToGno schedNo \<in> active_threads s)) \<and>
    ((spaceSpecifier \<in> GetThreadsTids s) \<longrightarrow> 
                (GetSpaceThreadsNums s (GetThreadSpace s (TidToGno spaceSpecifier)) < MaxThreadsPerSpace SysConf))"

definition WeakCreateThread::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t  \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"WeakCreateThread SysConf s destNo spaceSpecifier schedNo pagerNo = 
(if WeakCreateThread_Cond SysConf s destNo spaceSpecifier schedNo pagerNo
 then (let gno = TidToGno destNo
        in (if (pagerNo = NILTHREAD) 
            then (if (spaceSpecifier = destNo)
                  then (let space = (SOME sp. sp \<in> (Address_Space SysConf - spaces s))
                        in CreateThread SysConf s gno space (TidToGno schedNo))
                  else  CreateThread SysConf s gno (GetThreadSpace s (TidToGno spaceSpecifier)) (TidToGno schedNo)) 
            else (if(spaceSpecifier = destNo)
                  then s                                                                             \<comment> \<open>It is impossible\<close>
                  else CreateActiveThread SysConf s gno (GetThreadSpace s (TidToGno spaceSpecifier)) (TidToGno schedNo) (TidToGno pagerNo))))
 else s)"

definition WeakModifyThread_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> bool" where
"WeakModifyThread_Cond SysConf s destNo spaceSpecifier schedNo pagerNo \<equiv> 
    (current_thread s \<in> active_threads s) \<and> (dIsPrivilegedSpace (GetCurrentSpace s)) \<and> 
    (destNo \<in> GetThreadsTids s) \<and> (spaceSpecifier \<in> GetThreadsTids s) \<and>
    (schedNo \<in> GetThreadsTids s \<union> {NILTHREAD}) \<and> (pagerNo \<in> GetThreadsTids s \<union> {NILTHREAD}) \<and>
    ((pagerNo \<noteq> NILTHREAD) \<longrightarrow> GetThreadSpace s (TidToGno spaceSpecifier) \<in> initialised_spaces s) \<and>
    ((pagerNo \<noteq> NILTHREAD) \<and> (destNo \<notin> GetActiveThreadsTids s) \<longrightarrow> 
            ((schedNo \<noteq> NILTHREAD) \<longrightarrow> (TidToGno schedNo \<in> active_threads s)) \<and> 
            ((schedNo = NILTHREAD) \<longrightarrow> (GetThreadScheduler s (TidToGno destNo) \<in> active_threads s))) \<and>
    (GetThreadSpace s (TidToGno spaceSpecifier) \<noteq> GetThreadSpace s (TidToGno destNo) \<longrightarrow>
            GetSpaceThreadsNums s (GetThreadSpace s (TidToGno spaceSpecifier)) < MaxThreadsPerSpace SysConf)"

definition WeakModifyThread::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"WeakModifyThread SysConf s destNo spaceSpecifier schedNo pagerNo = 
(if WeakModifyThread_Cond SysConf s destNo spaceSpecifier schedNo pagerNo
 then let tmp_dest = TidToGno destNo;
          tmp_spec = TidToGno spaceSpecifier;
          tmp_specSpace = GetThreadSpace s tmp_spec;
          tmp_destSpace = GetThreadSpace s tmp_dest in
      (if tmp_specSpace = tmp_destSpace \<and> pagerNo = NILTHREAD \<and> schedNo = NILTHREAD 
         then s                   \<comment> \<open>skip\<close>
         else (let S1 = (if tmp_specSpace \<noteq> tmp_destSpace
                         then Migrate SysConf s tmp_dest tmp_specSpace
                         else s);
                   S2 = (if pagerNo \<noteq> NILTHREAD
                         then (if tmp_dest \<notin> active_threads S1
                               then ActivateThread SysConf S1 tmp_dest (TidToGno pagerNo)
                               else SetPager S1 tmp_dest (TidToGno pagerNo))
                         else S1);
                   S3 = (if schedNo \<noteq> NILTHREAD
                         then SetScheduler S2 tmp_dest (TidToGno schedNo)
                         else S2)
               in S3))
 else s)"

definition WeakDeleteThread_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> bool" where
"WeakDeleteThread_Cond SysConf s dest \<equiv>
    (current_thread s \<in> active_threads s) \<and> (dIsPrivilegedSpace (GetCurrentSpace s)) \<and> 
    (dest \<in> GetThreadsTids s) \<and> (thread_space s (TidToGno dest) \<noteq> Some Sigma0Space) \<and>
    (thread_space s (TidToGno dest) \<noteq> Some RootServerSpace) \<and>
    (thread_space s (TidToGno dest) \<noteq> Some KernelSpace)"

definition WeakDeleteThread::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> State" where
"WeakDeleteThread SysConf s dest =
(if WeakDeleteThread_Cond SysConf s dest
 then DeleteThread s (TidToGno dest)
 else s)"

definition IntThreadControl_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> bool" where
"IntThreadControl_Cond SysConf s destNo handlerNo \<equiv> 
    (current_thread s \<in> active_threads s) \<and> (dIsPrivilegedSpace (GetThreadSpace s (current_thread s))) \<and> 
    (destNo \<in> GetThreadsTids s) \<and> (handlerNo \<in> GetThreadsTids s) \<and> (TidToGno destNo \<in> kIntThreads)"

definition IntThreadControl::"Sys_Config \<Rightarrow> State \<Rightarrow> threadid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"IntThreadControl SysConf s destNo handlerNo = 
(if IntThreadControl_Cond SysConf s destNo handlerNo
 then (if destNo = handlerNo 
            then DeactivateInterrupt s (TidToGno destNo)
            else ActivateInterrupt SysConf s (TidToGno destNo) (TidToGno handlerNo))
 else s)"

definition Weak_Exregs::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> control_t set \<Rightarrow> globalid_t \<Rightarrow> State" where
"Weak_Exregs SysConf S gno control pager =
(if (gno \<in> active_threads S) \<and> (pager \<in> Threads_Gno SysConf) \<and> (gno \<notin> kIntThreads)
 then (let S1 = (if ex_p \<in> control
                 then SetThreadPager S gno (GnoToTid pager)
                 else S);
           S2 = (if ex_S \<in> control \<and> isSending (GetThreadState S1 gno) \<or>
                    ex_R \<in> control \<and> isReceiving (GetThreadState S1 gno)
                   then (let S11 = Unwind S1 gno;
                             S12 = SetThreadState S11 gno tsRunning;
                             S13 = enqueue_ready S12 gno
                          in S13)
                   else S1);
           S3 = (if ex_h \<in> control
                 then (if ex_H \<in> control
                       then (SetThreadState S2 gno tsAborted) 
                       else (SetThreadState S2 gno tsHalted))
                 else S2)
        in S3)
 else S)"

definition GetLowWord::"int \<Rightarrow> int" where
"GetLowWord w = w mod 2^16"

definition GetHighWord::"int \<Rightarrow> int" where
"GetHighWord w = w div 2^16"

definition do_schedule::"State \<Rightarrow> globalid_t \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> State" where
"do_schedule s destNo timeControl prio =
(let old_prio = GetThreadPriority s destNo;
     S1 = (if prio < max_nat \<and> prio \<noteq> GetThreadPriority s destNo
           then let s1 = (dequeue_ready s destNo);
                 s2 = SetThreadPriority s1 destNo (prio mod (MAX_PRIO+1));
                 s3 = enqueue_ready s2 destNo in s3
           else s);            
     S2 = (if timeControl < max_int
           then let s1 = SetThreadQuantum S1 destNo (GetLowWord timeControl);
                    s2 = SetThreadTimeslice s1 destNo (GetHighWord timeControl)
                in s2
           else S1)
  in (S2))"

end