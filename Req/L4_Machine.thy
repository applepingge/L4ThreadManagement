theory L4_Machine
  imports L4_Init
begin

section\<open> Instantiation and Its Proofs of Security Model  \<close>

consts SysConf :: "Sys_Config" 

definition sys_config_witness :: Sys_Config 
where 
"sys_config_witness \<equiv> \<lparr> MaxThreadsPerSpace = 6, 
                        Threads_Gno = {kSigma0, kRootServer} \<union> kIntThreads,
                        Address_Space = {Sigma0Space,RootServerSpace,KernelSpace} \<rparr>" 
lemma spaceconflemma:"Sigma0Space \<in> Address_Space sys_config_witness \<and>
 KernelSpace \<in> Address_Space sys_config_witness \<and>
RootServerSpace \<in> Address_Space sys_config_witness \<and> Sigma0Space \<noteq> KernelSpace \<and>
              Sigma0Space \<noteq> RootServerSpace \<and> KernelSpace \<noteq> RootServerSpace \<and> MaxAddressSpaces sys_config_witness \<ge>3"
  apply (simp add: sys_config_witness_def MaxAddressSpaces_def)
  using SpaceDiff by auto

lemma threadconflemma:"idle \<notin> Threads_Gno sys_config_witness \<and> kSigma0 \<in> Threads_Gno sys_config_witness \<and> kRootServer \<in> Threads_Gno sys_config_witness \<and>
kIntThreads \<noteq> {} \<and> kSigma0 \<noteq> kRootServer \<and> kSigma0 \<notin> kIntThreads \<and> kRootServer \<notin> kIntThreads \<and>
 card kIntThreads \<le> MaxThreadsPerSpace sys_config_witness \<and> MaxThreads sys_config_witness \<ge> 2 "
  apply (simp add:IntThreadsNotNull sys_config_witness_def MaxThreads_def ThreadIDDiff IdleDiff)
  using IntThreadsNotNull card.infinite card_mono finite_insert le_0_eq subset_insertI subset_insertI2
  by (smt dual_order.trans numeral_le_iff semiring_norm(68) semiring_norm(72))

lemma  intthreadconflemma:" kIntThreads \<subset> Threads_Gno sys_config_witness "
  using sys_config_witness_def ThreadIDDiff
  by (metis (no_types, lifting) Sys_Config.select_convs(2) Un_insert_left insert_iff sup.right_idem sup.strict_order_iff)

specification (SysConf)
  PriSpacesConfigLemma: "RootServerSpace \<in> Address_Space SysConf \<and>
  Sigma0Space \<in> Address_Space SysConf \<and> KernelSpace \<in> Address_Space SysConf \<and>
  Sigma0Space \<noteq> KernelSpace \<and>Sigma0Space \<noteq> RootServerSpace \<and> KernelSpace \<noteq> RootServerSpace"
  PriThreadsConfigLemma: "idle \<notin> Threads_Gno SysConf \<and> kSigma0 \<in> Threads_Gno SysConf \<and> kRootServer \<in> Threads_Gno SysConf \<and>
  kIntThreads \<subset> Threads_Gno SysConf \<and> kIntThreads \<noteq> {} \<and> card kIntThreads \<le> MaxThreadsPerSpace SysConf \<and> 
  kSigma0 \<noteq> kRootServer \<and> kSigma0 \<notin> kIntThreads \<and> kRootServer \<notin> kIntThreads"
  KIPConfigLemma: "MaxThreads SysConf \<ge> 2 \<and> MaxAddressSpaces SysConf \<ge> 3"
  using sys_config_witness_def spaceconflemma threadconflemma intthreadconflemma
  by auto

consts s0_req :: State
definition s0_req_witness :: State
  where "s0_req_witness \<equiv> System_Init SysConf"

specification (s0_req) 
  S0ReqInit: "s0_req = System_Init SysConf"
  by simp

definition step::"State \<Rightarrow> Event \<Rightarrow> State" where
"step S e \<equiv>
(case e of
            (eThreadControl destNo spaceSpec schedNo pagerNo)
                  \<Rightarrow> ThreadControl SysConf S destNo spaceSpec schedNo pagerNo)"

primrec run::"State \<Rightarrow> Event list \<Rightarrow> State" where
"run s [] = s" |
"run s (e#es) = run (step s e) es"

definition "Reachable s \<equiv> \<exists>es. run s0_req es = s"

lemma run_step:"\<forall>s. run s (es @ [e]) = step (run s es) e"
  apply(induction es)
  by auto

lemma Reach_step:"Reachable s \<Longrightarrow> Reachable (step s e)"
  using run_step unfolding Reachable_def
  by auto

end