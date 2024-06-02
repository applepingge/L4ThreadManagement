theory L4_Inv_Proof
  imports L4_Inv_WeakSyscall
begin

section\<open>Invariant Proofs\<close>

lemma s0_Inv:"Invariants s0_req"
  unfolding Invariants_def
  using s0_Inv_Current s0_Inv_Space s0_Inv_Thread
  by auto

lemma ThreadControl_Inv:
  assumes p1:"Invariants s"
      and p2:"s1 = ThreadControl SysConf s destNo spaceSpec schedNo pagerNo"
    shows "Invariants s1"
  unfolding ThreadControl_def p2
  using p1 ThreadControl_Cond_def WeakCreateThread_Inv
    WeakModifyThread_Inv WeakDeleteThread_Inv IntThreadControl_Inv SetError_Inv
  by simp

lemma SpaceControl_Inv:
  assumes p1:"Invariants s"
and p2:"s1 = SpaceControl SysConf s spaceSpec control KipArea UtcbArea"
shows "Invariants s1"
  unfolding p2 SpaceControl_def
  using p1 SetError_Inv InitialiseAddressSpace_Inv
  by auto

lemma step_Inv:
  assumes p1:"Invariants s"
      and p2:"s' = step s a"
    shows "Invariants s'"
proof(cases a)
  case (eThreadControl x11 x12 x13 x14)
  then show ?thesis using p1 p2 step_def ThreadControl_Inv
    by simp
qed

lemma Run_Inv:
  assumes "Invariants s"
  shows "Invariants (run s es)"
  using assms
proof(induction es arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then have "Invariants (step s a)" using step_Inv by simp
  then have "Invariants (run (step s a) es)" using Cons by simp
  then show ?case by simp
qed

lemma Reach_Inv:
  assumes a1:"Reachable s"
  shows "Invariants s"
proof-
  have h1:"\<exists>es. s = run s0_req es" using assms Reachable_def by auto
  then obtain es where h2:"s = run s0_req es" by blast
  then show ?thesis using s0_Inv Run_Inv by auto
qed

end