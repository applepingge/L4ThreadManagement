theory L4_Abs
imports Main
begin
locale M_abs =
fixes reachable :: "'s \<Rightarrow> bool"

fixes step :: "'s \<Rightarrow> 'e \<Rightarrow> 's"

fixes s0 :: "'s"

fixes CONFIG :: 'config

fixes SPACES :: "'config \<Rightarrow> 'space set"

fixes THREADS :: "'config \<Rightarrow> 'gid set"

fixes idle :: 'gid

fixes sigma0 :: 'gid

fixes rootserver :: 'gid

fixes anythread :: "'tid"

fixes nilthread :: "'tid"

fixes intthreads :: "'gid set"

fixes sigma0space :: 'space

fixes rootserverspace :: 'space

fixes kernelspace :: 'space

fixes spaces :: "'s \<Rightarrow> 'space set"

fixes threads :: "'s \<Rightarrow> 'gid set"

fixes active :: "'s \<Rightarrow> 'gid set"

fixes space :: "'s \<Rightarrow> 'gid \<rightharpoonup> 'space"

fixes scheduler :: "'s \<Rightarrow> 'gid \<rightharpoonup> 'gid"

fixes pager :: "'s \<Rightarrow> 'gid \<rightharpoonup> 'tid"

fixes status :: "'s \<Rightarrow> 'gid \<rightharpoonup> 'status"

fixes Create

fixes CreateActive 

fixes Activate

fixes Delete 

fixes SetPager 

fixes SetScheduler 

fixes SetStatus

fixes ActivateInterrupt

fixes DeactivateInterrupt

assumes
"reachable s0" and

"\<And>s e. reachable s \<Longrightarrow> reachable (step s e)" and

(*1*)
"reachable s \<Longrightarrow> threads s \<subseteq> THREADS CONFIG" and

(*2*)
"reachable s \<Longrightarrow> spaces s \<subseteq> SPACES CONFIG" and

(*3*)
"reachable s \<Longrightarrow> sigma0 \<in> active s" and

(*4*)
"reachable s \<Longrightarrow> rootserver \<in> active s" and 

(*5*)
"reachable s \<Longrightarrow> intthreads \<subseteq> active s" and 

(*6*)
"reachable s \<Longrightarrow> active s \<subseteq> threads s" and

(*7*)
"reachable s \<Longrightarrow> space s idle = Some kernelspace" and

(*8*)
"reachable s \<Longrightarrow> space s sigma0 = Some sigma0space" and

(*9*)
"reachable s \<Longrightarrow> space s rootserver = Some rootserverspace" and

(*10*)
"reachable s \<Longrightarrow> x \<in> intthreads \<Longrightarrow> space s x = Some kernelspace" and

(*11*)
"reachable s \<Longrightarrow> t \<in> threads s \<Longrightarrow> \<exists>sche. sche \<in> threads s \<and> scheduler s t = Some sche" and

(*12*)
"reachable s \<Longrightarrow> t \<in> threads s \<Longrightarrow> \<exists>sp. sp \<in> spaces s \<and> space s t = Some sp" and

(*13*)
"reachable s \<Longrightarrow> t \<in> THREADS CONFIG - threads s \<Longrightarrow> space s t = None" and

(*14*)
"reachable s \<Longrightarrow> t \<in> THREADS CONFIG - threads s \<Longrightarrow> scheduler s t = None" and

(*15*)
"reachable s \<Longrightarrow> t \<in> THREADS CONFIG - threads s \<Longrightarrow> status s t = None" and

(*16*)
"reachable s \<Longrightarrow> t \<in> threads s \<Longrightarrow> t \<notin> active s \<Longrightarrow> pager s t = None" and

(*17*)
"reachable s \<Longrightarrow> t \<in> active s \<Longrightarrow> t \<notin> intthreads \<Longrightarrow> pager s t \<noteq> None"

(*18*)
"reachable s \<Longrightarrow> t \<in> active s \<Longrightarrow> t \<in> intthreads \<Longrightarrow> pager s t = None"

begin

end
end
