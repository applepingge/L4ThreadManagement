theory L4_Thread
imports L4_Space
begin

definition isRunnable::"threadstate_t \<Rightarrow> bool" where
"isRunnable s = (s = tsRunning)"

definition isSending::"threadstate_t \<Rightarrow> bool" where
"isSending s = (s = tsPolling)"

definition isReceiving::"threadstate_t \<Rightarrow> bool" where
"isReceiving s = (s = tsWaitingForever \<or> s = tsWaitingTimeout)"

definition isAborted::"threadstate_t \<Rightarrow> bool" where
"isAborted s = (s = tsAborted)"

definition isRunning::"threadstate_t \<Rightarrow> bool" where
"isRunning s = (s = tsRunning)"

definition isWaiting::"threadstate_t \<Rightarrow> bool" where
"isWaiting s = (s = tsWaitingForever \<or> s = tsWaitingTimeout)"

definition isWaitingForever::"threadstate_t \<Rightarrow> bool" where
"isWaitingForever s = (s = tsWaitingForever)"

definition isWaitingWithTimeout::"threadstate_t \<Rightarrow> bool" where
"isWaitingWithTimeout s = (s = tsWaitingTimeout)"

definition isPolling::"threadstate_t \<Rightarrow> bool" where
"isPolling s = (s = tsPolling)"

definition GLOBAL_GNO::"Sys_Config \<Rightarrow> threadid_t set" where 
"GLOBAL_GNO SysConf = {tid. \<exists>gid. tid = Global gid \<and> gid \<in> Threads_Gno SysConf}"

definition GLOBAL_TID::"Sys_Config \<Rightarrow> threadid_t set" where
"GLOBAL_TID SysConf = GLOBAL_GNO SysConf \<union> {NILTHREAD,ANYTHREAD}"

definition GnoToTid::"globalid_t \<Rightarrow> threadid_t" where
"GnoToTid gno = Global gno"

definition GnosToTids::"globalid_t set \<Rightarrow> threadid_t set" where
"GnosToTids gnos = {tid. \<exists>gno. gno \<in> gnos \<and> tid = Global gno}"

definition TidsToGnos::"threadid_t set \<Rightarrow> globalid_t set" where
"TidsToGnos tids = {gno. \<exists>tid. tid \<in> tids \<and> tid = Global gno}"

definition GetThreadsTids::"State \<Rightarrow> threadid_t set" where
"GetThreadsTids s = GnosToTids (threads s)"

definition GetActiveThreadsTids::"State \<Rightarrow> threadid_t set" where
"GetActiveThreadsTids s = GnosToTids (active_threads s)"

definition GetThreadScheduler::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t" where
"GetThreadScheduler s t = the (thread_scheduler s t)"

definition GetThreadState::"State \<Rightarrow> globalid_t \<Rightarrow> threadstate_t" where
"GetThreadState s t = the (thread_state s t)"

definition GetThreadPager::"State \<Rightarrow> globalid_t \<Rightarrow> threadid_t" where
"GetThreadPager s t = the (thread_pager s t)"

definition GetThreadHandler::"State \<Rightarrow> globalid_t \<Rightarrow> threadid_t" where
"GetThreadHandler s t = the (thread_handler s t)"

definition GetThreadMessage::"State \<Rightarrow> globalid_t \<Rightarrow> message_t" where
"GetThreadMessage s t = the (thread_message s t)"

definition GetThreadRcvWindow::"State \<Rightarrow> globalid_t \<Rightarrow> fpage_t" where
"GetThreadRcvWindow s t = the (thread_rcvWindow s t)"

definition GetThreadPriority ::"State \<Rightarrow> globalid_t \<Rightarrow> nat" where
"GetThreadPriority s t = the (thread_priority s t)"

definition GetThreadQuantum ::"State \<Rightarrow> globalid_t \<Rightarrow> int" where
"GetThreadQuantum s t =(the (thread_total_quantum s t))"

definition GetThreadTimeslice ::"State \<Rightarrow> globalid_t \<Rightarrow> int" where
"GetThreadTimeslice s t = the (thread_timeslice_length s t)"

definition GetThreadCurrentTimeslice ::"State \<Rightarrow> globalid_t \<Rightarrow> int" where
"GetThreadCurrentTimeslice s t = the (thread_current_timeslice s t)"

definition GetThreadSpace::"State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t" where
"GetThreadSpace s t = the (thread_space s t)"

definition GetCurrentSpace::"State \<Rightarrow> spaceName_t" where
"GetCurrentSpace s = GetThreadSpace s (current_thread s)"

(*"GetSpaceThreads s sp = {t. \<exists>t. thread_space s t = Some sp}"*)
definition GetSpaceThreads::"State \<Rightarrow> spaceName_t \<Rightarrow> globalid_t set" where
"GetSpaceThreads s sp = the (space_threads s sp)"

definition GetSpaceThreadsNums::"State \<Rightarrow> spaceName_t \<Rightarrow> nat" where
"GetSpaceThreadsNums s sp = card (GetSpaceThreads s sp)"

definition SetCurrentThread::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetCurrentThread s t = s\<lparr>current_thread:= t\<rparr>"

definition SetThreadsAdd::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetThreadsAdd s t = s\<lparr>threads:=(threads s \<union> {t})\<rparr>"

definition SetThreadsDel::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetThreadsDel s t = s\<lparr>threads:=(threads s - {t})\<rparr>"

definition SetActiveAdd::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetActiveAdd s t = s\<lparr>active_threads:=(active_threads s \<union> {t})\<rparr>"

definition SetActiveDel::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetActiveDel s t = s\<lparr>active_threads:=(active_threads s - {t})\<rparr>"

definition SetThreadSpace::"State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> State" where
"SetThreadSpace s t sp = s\<lparr>thread_space:=(thread_space s)(t:=Some sp)\<rparr>"

definition SetThreadScheduler::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetThreadScheduler s t sche = s\<lparr>thread_scheduler:=(thread_scheduler s)(t:=Some sche)\<rparr>"

definition SetThreadState::"State \<Rightarrow> globalid_t \<Rightarrow> threadstate_t \<Rightarrow> State" where
"SetThreadState s t ts = s\<lparr>thread_state:=(thread_state s)(t:=Some ts)\<rparr>"

definition SetThreadPager::"State \<Rightarrow> globalid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"SetThreadPager s t p = s\<lparr>thread_pager:=(thread_pager s)(t:=Some p)\<rparr>"

definition SetThreadHandler::"State \<Rightarrow> globalid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"SetThreadHandler s t p = s\<lparr>thread_handler:=(thread_pager s)(t:=Some p)\<rparr>"

definition SetThreadMessage::"State \<Rightarrow> globalid_t \<Rightarrow> message_t \<Rightarrow> State" where
"SetThreadMessage s t msg = s\<lparr>thread_message:=(thread_message s)(t:=Some msg)\<rparr>"

definition SetThreadRcvWindow::"State \<Rightarrow> globalid_t \<Rightarrow> fpage_t \<Rightarrow> State" where
"SetThreadRcvWindow s t fpage = s\<lparr>thread_rcvWindow:=(thread_rcvWindow s)(t:=Some fpage)\<rparr>"

definition SetThreadPriority ::"State \<Rightarrow> globalid_t \<Rightarrow> nat \<Rightarrow> State" where
"SetThreadPriority s t prio = s \<lparr>thread_priority:=(thread_priority s)(t:=Some prio)\<rparr>"

definition SetThreadQuantum ::"State \<Rightarrow> globalid_t \<Rightarrow> int \<Rightarrow> State" where
"SetThreadQuantum s t quan =
 s\<lparr>thread_total_quantum:=(thread_total_quantum s)(t:=Some quan)\<rparr>"

definition SetThreadTimeslice ::"State \<Rightarrow> globalid_t \<Rightarrow> int \<Rightarrow> State" where
"SetThreadTimeslice s t timeslice=
 s\<lparr>thread_timeslice_length:=(thread_timeslice_length s)(t:=Some timeslice)\<rparr>"

definition SetThreadCurrentTimeslice ::"State \<Rightarrow> globalid_t \<Rightarrow> int \<Rightarrow> State" where
"SetThreadCurrentTimeslice s t timeslice =
 s\<lparr>thread_current_timeslice:=(thread_current_timeslice s)(t:=Some timeslice)\<rparr>"

definition SetSpaceThreadsAdd::"State \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetSpaceThreadsAdd s sp t = 
    s\<lparr>space_threads:=(space_threads s)(sp:= Some (the (space_threads s sp) \<union> {t}))\<rparr>"

definition SetSpaceThreadsDel::"State \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetSpaceThreadsDel s sp t = 
    s\<lparr>space_threads:=(space_threads s)(sp:= Some (the (space_threads s sp) - {t}))\<rparr>"

definition GetIpcPartner::"State \<Rightarrow> globalid_t \<Rightarrow> threadid_t" where
"GetIpcPartner s t = the (thread_ipc_partner s t)"

definition SetIpcPartner::"State \<Rightarrow> globalid_t \<Rightarrow> threadid_t \<Rightarrow> State" where
"SetIpcPartner s t gno = 
s\<lparr>thread_ipc_partner:= (thread_ipc_partner s)(t:=Some gno)\<rparr>"

definition GetIpcTimeout::"State \<Rightarrow> globalid_t \<Rightarrow> timeout_t" where
"GetIpcTimeout s t = the (thread_ipc_timeout s t)"

definition SetIpcTimeout::"State \<Rightarrow> globalid_t \<Rightarrow> timeout_t \<Rightarrow> State" where
"SetIpcTimeout s t timeout = 
s\<lparr>thread_ipc_timeout:= (thread_ipc_timeout s)(t:=Some (eFiniteTimeout ((GetTimeout timeout) + current_time s)))\<rparr>"

definition GetThreadsIncoming::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t list" where
"GetThreadsIncoming s t = the (thread_incoming s t)"

definition SetThreadsIncoming::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t list \<Rightarrow> State" where
"SetThreadsIncoming s t ts = 
s\<lparr>thread_incoming:=(thread_incoming s)(t:=Some ts)\<rparr>"

definition SetThreadsIncomingAdd::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetThreadsIncomingAdd s t gno= 
s\<lparr>thread_incoming:=(thread_incoming s)(t:= Some (the (thread_incoming s t) @ [gno]))\<rparr>"

definition SetThreadsIncomingDel::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetThreadsIncomingDel s t gno= 
s\<lparr>thread_incoming:=(thread_incoming s)(t:= Some (remove1 gno (the (thread_incoming s t))))\<rparr>"

definition GetThreadsIncomingTids::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> threadid_t list" where
"GetThreadsIncomingTids SysConf s t = map GnoToTid (the (thread_incoming s t))"


\<comment>\<open>Scheduling\<close>
definition ExistInList :: "globalid_t \<Rightarrow> globalid_t list \<Rightarrow> bool" where
"ExistInList t ts \<equiv> find (\<lambda>a. a = t) ts \<noteq> None"

definition dequeue_ready_queuing :: "(prio \<Rightarrow> globalid_t list) \<Rightarrow> prio \<Rightarrow> globalid_t \<Rightarrow> (prio \<Rightarrow> globalid_t list)" where
"dequeue_ready_queuing queue prio gno = queue(prio:= remove1 gno (queue prio))"

definition dequeue_ready::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"dequeue_ready s gno =
(let prio = GetThreadPriority s gno;
     old_queue = ready_queuing s
in s\<lparr>ready_queuing:= dequeue_ready_queuing old_queue prio gno\<rparr>)"

definition enqueue_ready_queuing :: "(prio \<Rightarrow> globalid_t list) \<Rightarrow> prio \<Rightarrow> globalid_t \<Rightarrow> (prio \<Rightarrow> globalid_t list)" where
"enqueue_ready_queuing queue prio gno = queue(prio:= gno # queue prio)"

definition enqueue_ready::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"enqueue_ready s gno = 
(let prio = GetThreadPriority s gno;
     old_queue = ready_queuing s
in (if (find (\<lambda>x. x = gno) (old_queue prio) \<noteq> None) 
    then s 
    else s\<lparr>ready_queuing:= enqueue_ready_queuing old_queue prio gno\<rparr>))"

fun enqueue_readys::"State \<Rightarrow> globalid_t list \<Rightarrow> State" where
"enqueue_readys s [] = s" |
"enqueue_readys s (t#ts) = enqueue_ready (enqueue_readys s ts) t"

definition dequeue_wait::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"dequeue_wait s gno = s\<lparr>wait_queuing:= remove1 gno (wait_queuing s)\<rparr>"

definition enqueue_wait::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"enqueue_wait s gno = (if (find (\<lambda>x. x = gno) (wait_queuing s) \<noteq> None) 
                       then s 
                       else s\<lparr>wait_queuing:= gno # wait_queuing s\<rparr>)"

fun dequeue_waits::"State \<Rightarrow> globalid_t list \<Rightarrow> State" where
"dequeue_waits s [] = s"|
"dequeue_waits s (t#ts) = dequeue_wait (dequeue_waits s ts) t"

\<comment>\<open>Thread Operations\<close>

definition CreateThread_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> bool" where
"CreateThread_Cond SysConf s gno space scheduler \<equiv> 
    (current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and> (gno \<in> Threads_Gno SysConf - threads s) \<and>
    (scheduler \<in> threads s) \<and> (space \<in> Address_Space SysConf) \<and> (space \<noteq> KernelSpace) \<and>
    (space \<in> spaces s \<longrightarrow> GetSpaceThreadsNums s space < MaxThreadsPerSpace SysConf) \<and> (gno \<noteq> idle)"

definition CreateThread::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"CreateThread SysConf s gno space scheduler = 
(if CreateThread_Cond SysConf s gno space scheduler
 then let S' = (if space \<notin> spaces s
                then CreateAddressSpace SysConf s space 
                else s);
          S'' = S'\<lparr>space_threads:=(space_threads S')(space:=Some (the (space_threads S' space) \<union> {gno})),
                   threads := threads S' \<union> {gno},
                   thread_space := (thread_space S')(gno:= Some space),
                   thread_scheduler := (thread_scheduler S')(gno:= Some scheduler),
                   thread_state := (thread_state S')(gno:= Some tsAborted),
                   thread_total_quantum :=  (thread_total_quantum S')(gno:= Some DEFAULT_TOTAL_QUANTUM),
                   thread_timeslice_length :=  (thread_timeslice_length S')(gno:= Some DEFAULT_TIMESLICE_LENGTH),
                   thread_current_timeslice :=  (thread_current_timeslice S')(gno:= Some DEFAULT_TIMESLICE_LENGTH),
                   thread_priority :=  (thread_priority S')(gno:= Some DEFAULT_PRIORITY),
                   thread_ipc_partner := (thread_ipc_partner S')(gno:= Some NILTHREAD),
                   thread_ipc_timeout := (thread_ipc_timeout S')(gno:= Some eInfiniteTimeout),
                   thread_incoming := (thread_incoming S')(gno:= Some [])\<rparr>
       in SetError S'' (current_thread S'') eNoError
 else s)"


definition CreateTcb::"State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"CreateTcb s gno space scheduler = 
     s\<lparr>space_threads:=(space_threads s)(space := Some (the (space_threads s space) \<union> {gno})),
       threads := threads s \<union> {gno},
       thread_space := (thread_space s)(gno:= Some space),
       thread_scheduler := (thread_scheduler s)(gno:= Some scheduler),
       thread_state := (thread_state s)(gno:= Some tsAborted),
       thread_total_quantum :=  (thread_total_quantum s)(gno:= Some DEFAULT_TOTAL_QUANTUM),
       thread_timeslice_length :=  (thread_timeslice_length s)(gno:= Some DEFAULT_TIMESLICE_LENGTH),
       thread_current_timeslice :=  (thread_current_timeslice s)(gno:= Some DEFAULT_TIMESLICE_LENGTH),
       thread_priority :=  (thread_priority s)(gno:= Some DEFAULT_PRIORITY),
       thread_ipc_partner := (thread_ipc_partner s)(gno:= Some NILTHREAD),
       thread_ipc_timeout := (thread_ipc_timeout s)(gno:= Some eInfiniteTimeout),
       thread_incoming := (thread_incoming s)(gno:= Some [])\<rparr>"

definition CreateThread'::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"CreateThread' SysConf s gno space scheduler = 
(if CreateThread_Cond SysConf s gno space scheduler
 then let s1 = (if space \<notin> spaces s
                then CreateAddressSpace SysConf s space 
                else s) in 
      let s2 = CreateTcb s1 gno space scheduler in 
          SetError s2 (current_thread s2) eNoError
 else s)"

lemma CreateThread_eq:"CreateThread = CreateThread'"
  unfolding CreateThread'_def CreateThread_def CreateTcb_def
  by simp

definition ActivateThread::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"ActivateThread SysConf S gno pager = 
(if (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and> (gno \<in> threads S) \<and> (gno \<notin> active_threads S) \<and>
    (pager \<in> threads S)
 then let S' = S\<lparr>
        active_threads := active_threads S \<union> {gno},
        thread_state := (thread_state S)(gno:= Some tsWaitingForever),
        thread_pager := (thread_pager S)(gno:= Some (Global pager)),
        thread_handler := (thread_handler S)(gno:= Some NILTHREAD),
        thread_message := (thread_message S)(gno:= Some (UNTYPED 0)),
        thread_rcvWindow := (thread_rcvWindow S)(gno:= Some (0,0,{})),        
        thread_error := (thread_error S)(gno:= Some eNoError),
        thread_ipc_partner := (thread_ipc_partner S)(gno:= Some (Global pager)),
        thread_ipc_timeout := (thread_ipc_timeout S)(gno:= Some eInfiniteTimeout)\<rparr>
      in SetError S' (current_thread S') eNoError
 else S)"

definition CreateActiveThread_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> bool" where
"CreateActiveThread_Cond SysConf S gno space scheduler pager \<equiv>
    (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and> (gno \<in> (Threads_Gno SysConf - threads S)) \<and>
    (scheduler \<in> active_threads S) \<and> (scheduler \<notin> kIntThreads) \<and> (space \<in> initialised_spaces S) \<and> (pager \<in> threads S) \<and> 
    (space \<noteq> KernelSpace) \<and> (GetSpaceThreadsNums S space < MaxThreadsPerSpace SysConf) \<and> (gno \<noteq> idle)"


definition CreateActiveThread::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"CreateActiveThread SysConf s gno space scheduler pager =
(if CreateActiveThread_Cond SysConf s gno space scheduler pager
 then 
   let S' = s\<lparr>space_threads:=(space_threads s)(space:=Some (the (space_threads s space) \<union> {gno})),
             threads := threads s \<union> {gno},
             active_threads := active_threads s \<union> {gno},
             thread_space := (thread_space s)(gno:= Some space),
             thread_scheduler := (thread_scheduler s)(gno:= Some scheduler),
             thread_state := (thread_state s)(gno:= Some tsWaitingForever),
             thread_pager := (thread_pager s)(gno:= Some (Global pager)),
             thread_handler := (thread_handler s)(gno:= Some NILTHREAD),
             thread_message := (thread_message s)(gno:= Some (UNTYPED 0)),
             thread_rcvWindow := (thread_rcvWindow s)(gno:= Some (0,0,{})),        
             thread_error := (thread_error s)(gno:= Some eNoError),
             thread_total_quantum := (thread_total_quantum s)(gno:= Some DEFAULT_TOTAL_QUANTUM),
             thread_timeslice_length := (thread_timeslice_length s)(gno:= Some DEFAULT_TIMESLICE_LENGTH),
             thread_current_timeslice :=  (thread_current_timeslice s)(gno:= Some DEFAULT_TIMESLICE_LENGTH),
             thread_priority :=  (thread_priority s)(gno:= Some DEFAULT_PRIORITY),
             thread_ipc_partner := (thread_ipc_partner s)(gno:= Some (Global pager)),
             thread_ipc_timeout := (thread_ipc_timeout s)(gno:= Some eInfiniteTimeout),
             thread_incoming := (thread_incoming s)(gno:= Some [])\<rparr>
    in SetError S' (current_thread S') eNoError
 else s)"

definition CreateActiveTcb::"State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"CreateActiveTcb s gno space scheduler pager = 
    s\<lparr>space_threads:=(space_threads s)(space:=Some (the (space_threads s space) \<union> {gno})),
     threads := threads s \<union> {gno},
     active_threads := active_threads s \<union> {gno},
     thread_space := (thread_space s)(gno:= Some space),
     thread_scheduler := (thread_scheduler s)(gno:= Some scheduler),
     thread_state := (thread_state s)(gno:= Some tsWaitingForever),
     thread_pager := (thread_pager s)(gno:= Some (Global pager)),
     thread_handler := (thread_handler s)(gno:= Some NILTHREAD),
     thread_message := (thread_message s)(gno:= Some (UNTYPED 0)),
     thread_rcvWindow := (thread_rcvWindow s)(gno:= Some (0,0,{})),
     thread_error := (thread_error s)(gno:= Some eNoError),
     thread_total_quantum := (thread_total_quantum s)(gno:= Some DEFAULT_TOTAL_QUANTUM),
     thread_timeslice_length := (thread_timeslice_length s)(gno:= Some DEFAULT_TIMESLICE_LENGTH),
     thread_current_timeslice :=  (thread_current_timeslice s)(gno:= Some DEFAULT_TIMESLICE_LENGTH),
     thread_priority :=  (thread_priority s)(gno:= Some DEFAULT_PRIORITY),
     thread_ipc_partner := (thread_ipc_partner s)(gno:= Some (Global pager)),
     thread_ipc_timeout := (thread_ipc_timeout s)(gno:= Some eInfiniteTimeout),
     thread_incoming := (thread_incoming s)(gno:= Some [])\<rparr>"

definition CreateActiveThread'::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"CreateActiveThread' SysConf s gno space scheduler pager =
(if CreateActiveThread_Cond SysConf s gno space scheduler pager
 then let s' = CreateActiveTcb s gno space scheduler pager
       in SetError s' (current_thread s') eNoError
 else s)"

lemma CreateActiveThread_eq:"CreateActiveThread' = CreateActiveThread"
  unfolding CreateActiveTcb_def CreateActiveThread'_def CreateActiveThread_def 
  by simp
(*
definition Unwind::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"Unwind s gno = 
(if gno \<in> active_threads s
 then 
  (let state = (GetThreadState s gno);
       partner = (GetIpcPartner s gno)
    in (if isPolling state \<and> partner \<noteq> NILTHREAD \<and> partner \<noteq> ANYTHREAD
        then 
          let S1 = dequeue_wait s gno
           in SetThreadsIncomingDel S1 (TidToGno partner) gno
        else dequeue_wait s gno))
 else s)"
*)
definition Unwind::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"Unwind s gno = 
(if gno \<in> active_threads s
 then 
  (let state = (GetThreadState s gno);
       partner = (GetIpcPartner s gno)
    in (if isPolling state \<and> partner \<noteq> NILTHREAD \<and> partner \<noteq> ANYTHREAD
        then 
          let S1 = dequeue_wait s gno
           in SetThreadsIncomingDel S1 (TidToGno partner) gno
        else if isWaiting state \<and> partner \<noteq> NILTHREAD 
             then dequeue_wait s gno
             else s))
 else s)"

definition DeleteThread_Cond::"State \<Rightarrow> globalid_t \<Rightarrow> bool" where
"DeleteThread_Cond s gno \<equiv>
    (current_thread s \<in> active_threads s) \<and> 
    (current_thread s \<notin> kIntThreads) \<and> 
    (current_thread s \<noteq> gno) \<and> 
    (gno \<in> threads s) \<and> 
    (thread_space s gno \<noteq> Some Sigma0Space) \<and> 
    (thread_space s gno \<noteq> Some RootServerSpace) \<and> 
    (thread_space s gno \<noteq> Some KernelSpace) \<and> 

    (\<forall>t. t \<in> threads s \<longrightarrow> thread_scheduler s t \<noteq> Some gno \<and>
                           thread_ipc_partner s t \<noteq> Some (GnoToTid gno) \<and>
                           gno \<notin> set (the (thread_incoming s t)))"

definition DeleteThread::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"DeleteThread s gno =
(if DeleteThread_Cond s gno
 then let s2 = (if gno \<in> active_threads s
               then let s1 = dequeue_ready s gno
                    in (if isSending (the (thread_state s gno)) \<or> 
                           isReceiving (the (thread_state s gno))
                        then Unwind s1 gno
                        else s1)
               else s);
          space = (the (thread_space s2 gno));
          s4 = if the (space_threads s2 space) = {gno}
               then DeleteAddressSpace s2 space
               else s2\<lparr>space_threads:= (space_threads s2)
                      (space:= Some (the (space_threads s2 space) - {gno}))\<rparr>;        
          s5 = s4\<lparr>threads := threads s4 - {gno},
                 active_threads := active_threads s4 - {gno},
                 thread_space := ((thread_space s4)(gno := None)),
                 thread_scheduler := ((thread_scheduler s4)(gno := None)),
                 thread_state := ((thread_state s4)(gno := None)),
                 thread_pager := ((thread_pager s4)(gno := None)),
                 thread_handler := (thread_handler s4)(gno:= None),
                 thread_message := (thread_message s4)(gno:= None),
                 thread_rcvWindow := (thread_rcvWindow s4)(gno:= None),             
                 thread_error := (thread_error s4)(gno:= None),
                 thread_priority := (thread_priority s4)(gno := None),
                 thread_total_quantum := (thread_total_quantum s4)(gno := None),
                 thread_timeslice_length := (thread_timeslice_length s4)(gno := None),
                 thread_current_timeslice := (thread_current_timeslice s4)(gno := None),
                 thread_ipc_partner := (thread_ipc_partner s4)(gno:= None),
                 thread_ipc_timeout := (thread_ipc_timeout s4)(gno:= None),
                 thread_incoming := (thread_incoming s4)(gno:= None)\<rparr>
      in SetError s5 (current_thread s5) eNoError
 else s)"

definition SetScheduler::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetScheduler s gno scheduler = 
(if (current_thread s \<in> active_threads s) \<and> 
    (current_thread s \<notin> kIntThreads) \<and> (gno \<in> threads s) \<and> (scheduler \<in> threads s)
 then let S1 = SetThreadScheduler s gno scheduler 
       in SetError S1 (current_thread S1) eNoError
 else s)"

definition SetPager::"State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"SetPager s gno pager = 
(if (current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and> (gno \<in> active_threads s) 
\<and> (gno \<notin> kIntThreads) \<and> (pager \<in> threads s)
 then let S1 = SetThreadPager s gno (Global pager) 
       in SetError S1 (current_thread S1) eNoError
 else s)"

definition SetState::"State \<Rightarrow> globalid_t \<Rightarrow> threadstate_t \<Rightarrow> State" where
"SetState s gno state = 
(if (current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and> (state \<noteq> tsAborted) \<and>
 (gno \<in> active_threads s) \<and> (gno \<notin> kIntThreads) \<and> (current_thread s \<noteq> gno)
 then let S1 = SetThreadState s gno state in SetError S1 (current_thread S1) eNoError
 else s)"

definition Migrate_Cond::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> bool" where
"Migrate_Cond SysConf s gno space \<equiv>
    (current_thread s \<in> active_threads s) \<and> (current_thread s \<notin> kIntThreads) \<and> (gno \<in> threads s) \<and> 
    (space \<in> spaces s) \<and> (space \<noteq> the (thread_space s gno)) \<and> (gno \<noteq> kSigma0) \<and> (gno \<noteq> kRootServer) \<and>
    (gno \<notin> kIntThreads) \<and> (space \<noteq> Sigma0Space) \<and> (space \<noteq> RootServerSpace) \<and> (space \<noteq> KernelSpace) \<and>
    (the (thread_space s gno) \<noteq> Sigma0Space) \<and> (the (thread_space s gno) \<noteq> RootServerSpace) \<and> 
    (the (thread_space s gno) \<noteq> KernelSpace) \<and> (GetSpaceThreadsNums s space < MaxThreadsPerSpace SysConf)"

definition Migrate::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> spaceName_t \<Rightarrow> State" where
"Migrate SysConf s gno space =
(if Migrate_Cond SysConf s gno space
 then let S2 = (
            let oldspace = the (thread_space s gno)
            in if (the (space_threads s oldspace)) = {gno}
               then let S1 = DeleteAddressSpace s oldspace
                     in S1\<lparr>thread_space := ((thread_space S1)(gno := Some space)),
                          space_threads := (space_threads S1)(space:= Some (the (space_threads S1 space) \<union> {gno}))\<rparr>
               else s\<lparr>thread_space := ((thread_space s)(gno := Some space)),
                      space_threads := (space_threads s)
                        (space:= Some (the (space_threads s space) \<union> {gno}),
                         oldspace:= Some (the (space_threads s oldspace) - {gno}))\<rparr>
       )
       in SetError S2 (current_thread S2) eNoError
 else s)"

definition ActivateInterrupt::"Sys_Config \<Rightarrow> State \<Rightarrow> globalid_t \<Rightarrow> globalid_t \<Rightarrow> State" where
"ActivateInterrupt SysConf S gno handler = 
(if (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and> (gno \<in> kIntThreads) \<and> 
    (handler \<in> Threads_Gno SysConf) \<and> (handler \<noteq> gno) \<and> (handler \<in> threads S)
 then let S1 = SetThreadScheduler (SetThreadState S gno tsHalted) gno handler
       in SetError S1 (current_thread S1) eNoError
 else S)"

definition DeactivateInterrupt::"State \<Rightarrow> globalid_t \<Rightarrow> State" where
"DeactivateInterrupt S gno = 
(if (current_thread S \<in> active_threads S) \<and> (current_thread S \<notin> kIntThreads) \<and> (gno \<in> kIntThreads)
 then let S1 = SetThreadScheduler (SetThreadState S gno tsAborted) gno gno
       in SetError S1 (current_thread S1) eNoError
 else S)"

end