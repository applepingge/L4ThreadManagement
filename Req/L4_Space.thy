theory L4_Space
imports L4_State
begin

section\<open> Address Space and Mapping\<close>
definition "pgsize = (10::nat)"

definition "page_size = (2 ^ pgsize::vaddr_t)"

definition "pgmaxnum = 32 - pgsize"

definition "page_maxnum = (2 ^ pgmaxnum::vaddr_t)"

definition vaddr_to_vpage::"vaddr_t \<Rightarrow> v_page_t" where
"vaddr_to_vpage vaddr = (vaddr div page_size)"

definition vpage_to_vaddr::"v_page_t \<Rightarrow> vaddr_t" where
"vpage_to_vaddr vpage = vpage * page_size"

definition paddr_to_rpage::"paddr_t \<Rightarrow> r_page_t" where
"paddr_to_rpage paddr = (paddr div page_size)"

definition rpage_to_paddr::"r_page_t \<Rightarrow> paddr_t" where
"rpage_to_paddr rpage = rpage * page_size"

subsection\<open> Fpage \<close>
definition fp_base::"fpage_t \<Rightarrow> nat" where
"fp_base fp = fst fp"

definition fp_size::"fpage_t \<Rightarrow> nat" where
"fp_size fp = fst (snd fp)"

definition fp_perms::"fpage_t \<Rightarrow> perms_t set" where
"fp_perms fp = snd (snd fp)"

definition fpage_type::"fpage_t \<Rightarrow> fpage_type" where
"fpage_type fp =
(if fp = (0,1,UNIV) then complete_fpage else
 if fp = (0,0,{})    then nil_fpage      else
 if fp_size fp \<ge> 10 \<and> (fp_base fp * page_size) mod 2 ^ (fp_size fp) = 0 \<and> fp_perms fp \<noteq> {}
 then valid_fpage
 else invalid_fpage)"

definition nat_to_fpage::"nat \<Rightarrow> fpage_t" where
"nat_to_fpage n = (let base = n div page_size;
                       size = (n mod page_size) div 2^4;
                       perms = (if (n mod 2^3) div 2^2 > 0 then {pfRead} else {}) \<union>
                               (if (n mod 2^2) div 2 > 0 then {pfWrite} else {}) \<union>
                               (if (n mod 2^1) > 0 then {pfExecute} else {})
                     in (base,size,perms))"

subsection\<open> Privileged Space \<close>
definition is_kSigma0Space::"spaceName_t \<Rightarrow> bool" where
"is_kSigma0Space s = (s = Sigma0Space)"

definition is_kRootServerSpace::"spaceName_t \<Rightarrow> bool" where
"is_kRootServerSpace s = (s = RootServerSpace)"

definition dIsPrivilegedSpace::"spaceName_t \<Rightarrow> bool" where
"dIsPrivilegedSpace s = (is_kSigma0Space s \<or> is_kRootServerSpace s)"

subsection\<open> Operation \<close>

subsubsection\<open> Path \<close>

definition get_perms::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set" where
"get_perms s sp v_page = snd (the (the (space_mapping s sp) v_page))"

definition "get_perms1 s x \<equiv> case x of Virtual sp v \<Rightarrow> snd(the (the (space_mapping s sp) v))"

lemma get_perms_auxi:"x = Virtual sp v \<Longrightarrow> get_perms s sp v = get_perms1 s x"
  unfolding get_perms_def get_perms1_def
  by simp

definition direct_path::"State \<Rightarrow> page_t \<Rightarrow> page_t \<Rightarrow> bool"  ("(_\<turnstile>_\<leadsto>\<^sup>1_)"[1000,1000,1000]) where
"s \<turnstile> p1 \<leadsto>\<^sup>1 p2 = (\<exists>sp v m perms. p1 = Virtual sp v \<and> space_mapping s sp = Some m \<and> m v = Some (p2,perms))"

lemma direct_def:"s \<turnstile> (Virtual sp v) \<leadsto>\<^sup>1 p2 \<longrightarrow> (\<exists>m perms. space_mapping s sp = Some m \<and> m v = Some (p2, perms))"
  by (simp add:direct_path_def)

lemma SonIsNoReal:"(s \<turnstile> p1 \<leadsto>\<^sup>1 p2) \<longrightarrow> (\<nexists>r. p1 = Real r)"
  by (auto simp add:direct_path_def)

lemma FatherIsVirtual:"(s \<turnstile> p1 \<leadsto>\<^sup>1 p2) \<longrightarrow> (\<exists>sp v. p1 = Virtual sp v)"
  by (auto simp add:direct_path_def)

inductive tran_path::"State \<Rightarrow> page_t \<Rightarrow> page_t \<Rightarrow> bool" ("(_\<turnstile>_\<leadsto>\<^sup>+_)"[1000,1000,1000]) for s where
one_path:"s \<turnstile> x \<leadsto>\<^sup>1 y \<Longrightarrow> s \<turnstile> x \<leadsto>\<^sup>+ y"|
tran_path:"s \<turnstile> x \<leadsto>\<^sup>1 y \<Longrightarrow> s \<turnstile> y \<leadsto>\<^sup>+ z \<Longrightarrow> s \<turnstile> x \<leadsto>\<^sup>+ z"

inductive rtran_path::"State \<Rightarrow> page_t \<Rightarrow> page_t \<Rightarrow> bool" ("(_\<turnstile>_\<leadsto>\<^sup>*_)"[1000,1000,1000]) for s where
refl_path:"s \<turnstile> x \<leadsto>\<^sup>* x"|
refl_tran:"s \<turnstile> x \<leadsto>\<^sup>1 y \<Longrightarrow> s \<turnstile> y \<leadsto>\<^sup>* z \<Longrightarrow> s \<turnstile> x \<leadsto>\<^sup>* z"

lemma rtran_tran:
  "s \<turnstile> p1 \<leadsto>\<^sup>* p2 \<longleftrightarrow> p1 = p2 \<or> s \<turnstile> p1 \<leadsto>\<^sup>+ p2"
proof(rule iffI)
  show "s\<turnstile>p1\<leadsto>\<^sup>*p2 \<Longrightarrow> p1 = p2 \<or> s\<turnstile>p1\<leadsto>\<^sup>+p2"
    apply(induct rule: rtran_path.induct)
    by(auto simp add:tran_path.intros)
next
  show "p1 = p2 \<or> s\<turnstile>p1\<leadsto>\<^sup>+p2 \<Longrightarrow> s\<turnstile>p1\<leadsto>\<^sup>*p2"
    apply auto
     apply(rule rtran_path.intros)
    apply(induct rule:tran_path.induct)
    by(auto simp add:rtran_path.intros)
qed

subsubsection\<open> Unmap \<close>
definition sys_unmap::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> State" where
"sys_unmap s sp v_page del_perms =
s\<lparr>space_mapping:= 
    \<lambda>sp'. (if space_mapping s sp' = None then None else
           Some (\<lambda>v_page1. if the (space_mapping s sp') v_page1 = None then None else 
                                if s \<turnstile> (Virtual sp' v_page1) \<leadsto>\<^sup>+ (Virtual sp v_page) 
                                then
                                        if snd (the (the (space_mapping s sp') v_page1)) \<subseteq> del_perms 
                                        then None
                                        else Some (fst (the (the (space_mapping s sp') v_page1)),
                                                   snd (the (the (space_mapping s sp') v_page1)) - del_perms)
                                else the (space_mapping s sp') v_page1
                      ))\<rparr>"

subsubsection\<open> Flush \<close>
definition sys_flush::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> State" where
"sys_flush s sp v_page del_perms \<equiv>
if (sp \<noteq> Sigma0Space)
then s\<lparr>space_mapping:= 
      \<lambda>sp'. (if space_mapping s sp' = None then None else
             Some (\<lambda>v_page1. if the (space_mapping s sp') v_page1 = None then None else 
                                  if s \<turnstile> (Virtual sp' v_page1) \<leadsto>\<^sup>* (Virtual sp v_page) 
                                  then
                                          if snd (the (the (space_mapping s sp') v_page1)) \<subseteq> del_perms 
                                          then None
                                          else Some (fst (the (the (space_mapping s sp') v_page1)),
                                                     snd (the (the (space_mapping s sp') v_page1)) - del_perms)
                                  else the (space_mapping s sp') v_page1
                        ))\<rparr>
else s"

subsubsection\<open> Mapping \<close>
definition valid_page::"State \<Rightarrow> page_t \<Rightarrow> bool"  ("(_\<turnstile>_)" [1000,1000])where
"valid_page s page = (case page of Virtual sp v_page \<Rightarrow> (\<exists>p. s \<turnstile> page \<leadsto>\<^sup>1 p)| Real r \<Rightarrow> True)"

lemma FatherIsValid:"s \<turnstile> x \<leadsto>\<^sup>1 y \<longrightarrow> s \<turnstile> x \<and> (\<forall>r. x \<noteq> Real r)"
  unfolding direct_path_def valid_page_def
  by force

lemma ValidExSon:"s \<turnstile> x \<and> (\<forall>r. x \<noteq> Real r) \<longrightarrow> (\<exists>y. s \<turnstile> x \<leadsto>\<^sup>1 y)"
  using direct_path_def valid_page_def page_t.simps(5) page_t.exhaust
  by smt

lemma FatherEqValid:"(\<exists>y. s \<turnstile> x \<leadsto>\<^sup>1 y) \<longleftrightarrow> s \<turnstile> x \<and> (\<forall>r. x \<noteq> Real r)"
  using FatherIsValid ValidExSon by auto

lemma ValidInTran:"s \<turnstile> x \<and> (\<forall>r. x \<noteq> Real r) \<longrightarrow> (\<exists>y. s \<turnstile> x \<leadsto>\<^sup>+ y)"
  using ValidExSon tran_path.intros(1)
  by blast

lemma ValidInRTran:"s \<turnstile> x \<and> (\<forall>r. x \<noteq> Real r) \<longrightarrow> (\<exists>y. s \<turnstile> x \<leadsto>\<^sup>* y)"
  using ValidInTran rtran_tran
  by blast

lemma ValidVpageHasSon:"s \<turnstile> (Virtual sp vpage) = (\<exists>y. s \<turnstile> (Virtual sp vpage) \<leadsto>\<^sup>1 y)"
  using FatherEqValid
  by simp

lemma ValidVpageInTran:"x = Virtual sp vpage \<Longrightarrow> s \<turnstile> x \<longrightarrow> (\<exists>y. s \<turnstile> x \<leadsto>\<^sup>+ y)"
  using ValidInTran
  by simp

lemma ValidVpageInRTran:"x = Virtual sp vpage \<Longrightarrow> s \<turnstile> x \<longrightarrow> (\<exists>y. s \<turnstile> x \<leadsto>\<^sup>* y)"
  using ValidInRTran
  by simp

lemma ValidVpageMappingNotNone:"s \<turnstile> (Virtual sp vpage) = (space_mapping s sp \<noteq> None \<and> (the (space_mapping s sp)) vpage \<noteq> None)"
  using ValidVpageHasSon direct_path_def
  by auto

lemma ValidVpageMappingEx:"s \<turnstile> (Virtual sp vpage) = (\<exists>m p2 perms. space_mapping s sp = Some m \<and> m vpage = Some (p2, perms))"
  using ValidVpageHasSon direct_path_def
  by auto

definition sys_map::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> State" where
"sys_map s sp_from v_from sp_to v_to perms =
(if (sp_to \<noteq> Sigma0Space) 
 then 
    (if perms \<noteq> {} \<and> s \<turnstile> (Virtual sp_from v_from) \<and> perms \<subseteq> get_perms s sp_from v_from \<and> sp_from \<noteq> sp_to \<and>
       (\<forall>v. \<not>s \<turnstile> (Virtual sp_from v_from) \<leadsto>\<^sup>+ (Virtual sp_to v)) \<and> space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum
     then s\<lparr>space_mapping:= 
      \<lambda>sp'. (if space_mapping s sp' = None then None else
             Some (\<lambda>v_page1. if the (space_mapping s sp') v_page1 = None \<and> 
                                Virtual sp' v_page1 \<noteq> Virtual sp_to v_to then None else 
                                    if s \<turnstile> (Virtual sp' v_page1) \<leadsto>\<^sup>* (Virtual sp_to v_to) 
                                    then
                                          if (Virtual sp' v_page1) = (Virtual sp_to v_to)
                                          then Some ((Virtual sp_from v_from),perms)
                                          else None
                                    else the (space_mapping s sp') v_page1
                        ))\<rparr>
     else s)
 else s)"

subsubsection\<open> Grant \<close>
(*sp_to can not be sigma0*)
definition sys_grant::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> State" where
"sys_grant s sp_from v_from sp_to v_to perms =
(if (sp_to \<noteq> Sigma0Space) 
 then 
    (if perms \<noteq> {} \<and> s \<turnstile> (Virtual sp_from v_from) \<and> sp_from \<noteq> sp_to \<and> perms \<subseteq> get_perms s sp_from v_from \<and> 
        (\<forall>v. \<not>s \<turnstile>(fst (the (the (space_mapping s sp_from) v_from))) \<leadsto>\<^sup>* (Virtual sp_to v)) \<and> 
         space_mapping s sp_to \<noteq> None \<and> v_to < page_maxnum
     then s\<lparr>space_mapping:= 
      \<lambda>sp'. (if space_mapping s sp' = None then None else
             Some (\<lambda>v_page1. if the (space_mapping s sp') v_page1 = None \<and> 
                                Virtual sp' v_page1 \<noteq> Virtual sp_to v_to then None else 
                                  if s \<turnstile> (Virtual sp' v_page1) \<leadsto>\<^sup>* (Virtual sp_to v_to) \<or>
                                     s \<turnstile> (Virtual sp' v_page1) \<leadsto>\<^sup>* (Virtual sp_from v_from) 
                                  then
                                        if (Virtual sp' v_page1) = (Virtual sp_to v_to)
                                        then Some (fst (the (the (space_mapping s sp_from) v_from)),perms)
                                        else None
                                  else the (space_mapping s sp') v_page1
                        ))\<rparr>
     else s)
 else s)"

subsection\<open> Important Function\<close>
fun Map_fpage::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> nat \<Rightarrow> State" where
"Map_fpage s sp1 v1 sp2 v2 perms 0 = s"|
"Map_fpage s sp1 v1 sp2 v2 perms (Suc n) =
    (sys_map (Map_fpage s sp1 v1 sp2 v2 perms n) sp1 (v1+n) sp2 (v2+n) perms)"

fun Grant_fpage::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> nat \<Rightarrow> State" where
"Grant_fpage s sp1 v1 sp2 v2 perms 0 = s"|
"Grant_fpage s sp1 v1 sp2 v2 perms (Suc n) =
    (sys_grant (Grant_fpage s sp1 v1 sp2 v2 perms n) sp1 (v1+n) sp2 (v2+n) perms)"

fun Unmap_fpage::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> nat \<Rightarrow> State" where
"Unmap_fpage s sp v perms 0 = s"|
"Unmap_fpage s sp v perms (Suc n) =
    (sys_unmap (Unmap_fpage s sp v perms n) sp (v+n) perms)"

fun Flush_fpage::"State \<Rightarrow> spaceName_t \<Rightarrow> v_page_t \<Rightarrow> perms_t set \<Rightarrow> nat \<Rightarrow> State" where
"Flush_fpage s sp v perms 0 = s"|
"Flush_fpage s sp v perms (Suc n) =
    (sys_flush (Flush_fpage s sp v perms n) sp (v+n) perms)"

subsection\<open> Create Space \<close>
definition CreateAddressSpace::"Sys_Config \<Rightarrow> State \<Rightarrow> spaceName_t \<Rightarrow> State" where
"CreateAddressSpace config s sp = 
(if sp \<in> (Address_Space config) \<and> sp \<notin> spaces s 
 then s\<lparr>
        space_threads:= (space_threads s)(sp := Some {}),
        space_mapping:= (space_mapping s)(sp := Some (\<lambda>v_page. None))\<rparr>
 else s)"

subsection\<open> Initialise Space \<close>
definition InitialiseAddressSpace::"State \<Rightarrow> spaceName_t \<Rightarrow> State" where
"InitialiseAddressSpace s sp =
(if sp \<in> spaces s 
then s\<lparr>initialised_spaces:= (initialised_spaces s \<union> {sp})\<rparr>
else s)"

subsection\<open> Delete Space \<close>
definition DeleteAddressSpace::"State \<Rightarrow> spaceName_t \<Rightarrow> State" where
"DeleteAddressSpace s sp =
(if sp \<in> spaces s \<and> \<not> dIsPrivilegedSpace sp 
then 
  let s1 = Unmap_fpage s sp 0 UNIV page_maxnum   \<comment> \<open>Unmap everything; complete fpage\<close>
   in s1\<lparr>
         initialised_spaces:= initialised_spaces s1 - {sp},
         space_threads:= (space_threads s1)(sp:= None),
         space_mapping:= (space_mapping s1)(sp:= None)\<rparr>
else s)"

end