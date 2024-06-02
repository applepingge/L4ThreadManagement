theory L4_State
  imports "L4_Config"
begin
section\<open>Formal Specification\<close>
subsection\<open>Base Component\<close>

type_synonym addr_t = nat
type_synonym vaddr_t = nat
type_synonym paddr_t = nat
type_synonym byte = nat

datatype error_t = eNoError | eSendTimeout | eSendNonExistingPartner | eSendCancelled | eRecvTimeout |
eRecvNonExistingPartner | eRecvCancelled | eMsgOverflow | eXferTimeoutSender | eXferTimeoutReceiver |
eAborted | eNoPrivilege | eUnavailableThread | eInvalidSpace | eInvalidScheduler | eOutOfMemory |
eInvalidThread | eInvalidUtcbLocation | eInvalidUtcbArea | eInvalidKipArea | eInvalidParameter

datatype timeout_t =  eFiniteTimeout (GetTimeout:int) | eInfiniteTimeout

datatype perms_t = pfRead | pfWrite | pfExecute
definition "PERMS = {pfRead,pfWrite,pfExecute}"

type_synonym fpage_t = "nat \<times> nat \<times> perms_t set" (*base, size, permission*)
definition "FPAGE = {(b,s,p). (b \<in> \<nat>) \<and> (s \<in> \<nat>) \<and> (p \<subseteq> PERMS)}"
datatype fpage_type = invalid_fpage | valid_fpage | complete_fpage | nil_fpage

type_synonym spaceName_t = nat
consts Sigma0Space         ::  spaceName_t
consts RootServerSpace     ::  spaceName_t
consts KernelSpace         ::  spaceName_t

axiomatization where SpaceDiff:"Sigma0Space \<noteq> RootServerSpace \<and>
 Sigma0Space \<noteq> KernelSpace \<and> RootServerSpace \<noteq> KernelSpace"

type_synonym v_page_t = nat
type_synonym r_page_t = nat
datatype page_t = Virtual (sp_name: spaceName_t) (vir_page: v_page_t) | Real r_page_t
type_synonym mapping = "v_page_t \<rightharpoonup> page_t \<times> perms_t set"

type_synonym asid = spaceName_t
datatype tlb_entry = PTE asid v_page_t r_page_t "perms_t set"
datatype lookup_type = Miss | Incon | Hit tlb_entry

datatype message_t = MAP fpage_t | GRANT fpage_t | STRING string| UNTYPED nat

datatype threadstate_t =
 tsAborted | tsRunning | tsWaitingForever | tsWaitingTimeout | tsPolling | tsHalted

type_synonym prio = nat
type_synonym globalid_t = nat
consts kSigma0              ::  "globalid_t"
consts kRootServer          ::  "globalid_t"
consts kIntThreads          ::  "globalid_t set"

consts idle                 ::  "globalid_t"

axiomatization where 
ThreadIDDiff:"kSigma0 \<noteq> kRootServer \<and> kSigma0 \<notin> kIntThreads \<and> kRootServer \<notin> kIntThreads" and
IdleDiff:"idle \<noteq> kSigma0 \<and> idle \<noteq> kRootServer \<and> idle \<notin> kIntThreads" and
IntThreadsNotNull:"kIntThreads \<noteq> {} \<and> card kIntThreads = 5"

datatype threadid_t = Global (TidToGno:globalid_t) | NILTHREAD | ANYTHREAD

\<comment>\<open>8         7     6       5     4  3  2    1    0\<close>
\<comment>\<open>HALTFLAG, PAGER,UHANDLE,FLAGS,IP,SP,SEND,RECV,HALT\<close>
datatype control_t = ex_h | ex_p | ex_u | ex_f | ex_i | ex_s | ex_S | ex_R | ex_H

definition "EXREGS_FLAGS = { ex_h, ex_p, ex_u, ex_f, ex_i, ex_s, ex_S, ex_R, ex_H }"

subsection\<open> System Configuration \<close>
record Sys_Config =
MaxThreadsPerSpace          ::  "nat"
Threads_Gno                 ::  "globalid_t set"
Address_Space               ::  "spaceName_t set"

subsection\<open> System State \<close>
record State=
current_thread              ::  "globalid_t"
current_time                ::  "int"

threads                     ::  "globalid_t set"
active_threads              ::  "globalid_t set"
thread_space                ::  "globalid_t \<rightharpoonup> spaceName_t"
thread_scheduler            ::  "globalid_t \<rightharpoonup> globalid_t"
thread_state                ::  "globalid_t \<rightharpoonup> threadstate_t"

thread_pager                ::  "globalid_t \<rightharpoonup> threadid_t"
thread_handler              ::  "globalid_t \<rightharpoonup> threadid_t"
thread_message              ::  "globalid_t \<rightharpoonup> message_t"
thread_rcvWindow            ::  "globalid_t \<rightharpoonup> fpage_t"
thread_error                ::  "globalid_t \<rightharpoonup> error_t"

thread_priority             ::  "globalid_t \<rightharpoonup> prio"
thread_total_quantum        ::  "globalid_t \<rightharpoonup> int"
thread_timeslice_length     ::  "globalid_t \<rightharpoonup> int"
thread_current_timeslice    ::  "globalid_t \<rightharpoonup> int"

wait_queuing                ::  "globalid_t list"
ready_queuing               ::  "prio \<Rightarrow> globalid_t list"
current_timeslice           ::  "int"

initialised_spaces          ::  "spaceName_t set"
space_threads               ::  "spaceName_t \<rightharpoonup> globalid_t set"
space_mapping               ::  "spaceName_t \<rightharpoonup> mapping"

thread_ipc_partner          ::  "globalid_t \<rightharpoonup> threadid_t"
thread_ipc_timeout          ::  "globalid_t \<rightharpoonup> timeout_t"
thread_incoming             ::  "globalid_t \<rightharpoonup> globalid_t list"

\<comment>\<open>
allocated_mem               ::  "r_page_t \<Rightarrow> bool"
free_block                  ::  "nat"
 allocated_mem = (\<lambda>r. False),
 free_block = Real_Block SysConf,
\<close>

definition "spaces s = dom (space_mapping s)"

subsection\<open> Events \<close>
datatype Event = eThreadControl threadid_t threadid_t threadid_t threadid_t

subsection\<open> Auxiliary Functions \<close>
subsubsection\<open> Tool Functions \<close>
definition "cond = (SOME b. b \<in> {True, False})"

definition dom'::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set" where
"dom' f = {a. \<exists>b. f a = b }"

definition dom_set::"('a \<Rightarrow> 'b set) \<Rightarrow> 'a set" where
"dom_set f = {a. f a \<noteq> {}}"

definition ran' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set" where
"ran' f = {b. \<exists>a. f a = b}"

subsubsection\<open> Config \<close>
definition MaxThreads::"Sys_Config \<Rightarrow> nat" where
"MaxThreads conf = card ((Threads_Gno conf))"

definition MaxAddressSpaces::"Sys_Config \<Rightarrow> nat" where
"MaxAddressSpaces conf = card (Address_Space conf)"

subsubsection\<open> Error \<close>
definition "dIpcFailures = { eMsgOverflow, eXferTimeoutSender, eXferTimeoutReceiver, eAborted }"

definition SetThreadError::"State \<Rightarrow> globalid_t \<Rightarrow> error_t \<Rightarrow> State" where
"SetThreadError s gno error = s\<lparr>thread_error:=(thread_error s)(gno:=Some error)\<rparr>"

definition GetThreadError::"State \<Rightarrow> globalid_t \<Rightarrow> error_t" where
"GetThreadError s gno = the (thread_error s gno)"

definition SetError::"State \<Rightarrow> globalid_t \<Rightarrow> error_t \<Rightarrow> State" where
"SetError s gno error = 
(if (gno \<in> active_threads s) \<and> (gno \<notin> kIntThreads)
 then SetThreadError s gno error
 else s)"

subsubsection\<open> Timeout \<close>
definition isInfinite::"timeout_t \<Rightarrow> bool" where
"isInfinite t = (t = eInfiniteTimeout)"

definition isFinite::"timeout_t \<Rightarrow> bool" where
"isFinite t = (t \<noteq> eFiniteTimeout 0 \<and> t \<noteq> eInfiniteTimeout)"

definition isNoTimeout::"timeout_t \<Rightarrow> bool" where
"isNoTimeout t = (t = eFiniteTimeout 0)"

definition isTimeout::"timeout_t \<Rightarrow> bool" where
"isTimeout t = (t\<noteq>eFiniteTimeout 0)"

end