theory Preflow_Push_Impl
imports 
  "../../../../isafol/DRAT/Synth_Definition"
  "../../../../isafol/DRAT/DRAT_Misc"
  Preflow Graph_Impl
  "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin

(* TODO: Move *)  
  
thm WHILEIT_rule  
  
lemma monadic_WHILEIT_refine[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le>\<Down>bool_rel (b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; nofail (b s); inres (b s) True \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (monadic_WHILEIT I b f s)"
  unfolding monadic_WHILEIT_def
  by (refine_rcg bind_refine'; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILEIT[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s \<rbrakk> \<Longrightarrow> I' s'"  
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s' \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; I s; I' s'; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT I' b' f' s' \<le>\<Down>R (WHILEIT I b f s)"
  unfolding WHILEIT_to_monadic
  by (refine_vcg; assumption?; auto)
  
lemma monadic_WHILEIT_refine_WHILET[refine]:  
  assumes [refine]: "(s',s) \<in> R"
  assumes [THEN order_trans,refine_vcg]: "\<And>s' s. \<lbrakk> (s',s)\<in>R \<rbrakk> \<Longrightarrow> b' s' \<le> SPEC (\<lambda>r. r = b s)"
  assumes [refine]: "\<And>s' s. \<lbrakk> (s',s)\<in>R; b s \<rbrakk> \<Longrightarrow> f' s' \<le>\<Down>R (f s)"
  shows "monadic_WHILEIT (\<lambda>_. True) b' f' s' \<le>\<Down>R (WHILET b f s)"
  unfolding WHILET_def
  by (refine_vcg; assumption?)  

lemma monadic_WHILEIT_pat[def_pat_rules]:
  "monadic_WHILEIT$I \<equiv> UNPROTECT (monadic_WHILEIT I)"
  by auto  
    
lemma id_monadic_WHILEIT[id_rules]: 
  "PR_CONST (monadic_WHILEIT I) ::\<^sub>i TYPE(('a \<Rightarrow> bool nres) \<Rightarrow> ('a \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> 'a nres)"
  by simp
    
lemma monadic_WHILEIT_arities[sepref_monadify_arity]:
  "PR_CONST (monadic_WHILEIT I) \<equiv> \<lambda>\<^sub>2b f s. SP (PR_CONST (monadic_WHILEIT I))$(\<lambda>\<^sub>2s. b$s)$(\<lambda>\<^sub>2s. f$s)$s"
  by (simp)

lemma monadic_WHILEIT_comb[sepref_monadify_comb]:
  "PR_CONST (monadic_WHILEIT I)$b$f$s \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. 
      SP (PR_CONST (monadic_WHILEIT I))$b$f$s
    )"
  by (simp)

  
(*locale Network_with_Adjm = Network c s t for c :: "'capacity::linordered_idom flow" and s t +
  fixes am assumes am_is_adj_map: "is_adj_map am"
begin  

  lemma am_in_rel: "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
    using am_is_adj_map unfolding is_adj_map_def
    by (auto simp: adjacent_nodes_def list_set_rel_def in_br_conv)  
  
  lemma am_out_V_empty[simp]: "v\<notin>V \<Longrightarrow> am v = []"
    using am_is_adj_map[unfolded is_adj_map_def, THEN spec, of v] E_ss_VxV by auto
*)
  
context Network 
begin  
  
(* Custom operations *)  
  
(* Residual Graph *)  
  
definition cf_get :: "'capacity flow \<Rightarrow> edge \<Rightarrow> 'capacity nres" 
  where "cf_get cf e \<equiv> do {
    assert (e\<in>E \<union> E\<inverse>);
    return (cf e)
  }"  
  
definition cf_set :: "'capacity flow \<Rightarrow> edge \<Rightarrow> 'capacity \<Rightarrow> 'capacity flow nres" 
  where "cf_set cf e x \<equiv> do {
    assert (e\<in>E \<union> E\<inverse>);
    return (cf (e:=x))
  }"  
  
definition cf_init :: "'capacity flow nres" where "cf_init \<equiv> return (op_mtx_new c)"

(* Excess *)  
definition x_init :: "(node \<Rightarrow> 'capacity) nres" where "x_init \<equiv> return (\<lambda>_. 0)"
definition x_get :: "(node \<Rightarrow> 'capacity) \<Rightarrow> node \<Rightarrow> 'capacity nres" 
  where "x_get x u \<equiv> do {
    assert (u\<in>V);
    return (x u)
  }"
definition x_add :: "(node \<Rightarrow> 'capacity) \<Rightarrow> node \<Rightarrow> 'capacity \<Rightarrow> (node \<Rightarrow> 'capacity) nres"  
  where "x_add x u \<Delta> \<equiv> do {
    assert (u\<in>V);
    return (x(u := x u + \<Delta>))
  }"

(* Adjacency map *)
definition am_get :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> node list nres"    
  where "am_get am u \<equiv> do {
    assert (u\<in>V);
    return (am u)
  }"
    
definition am_is_in_V :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> bool nres"
  where "am_is_in_V am u \<equiv> do {
    return (am u \<noteq> [])
  }"

lemma am_is_in_V_correct[THEN order_trans, refine_vcg]: 
  assumes "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
  shows "am_is_in_V am u \<le> (spec x. x \<longleftrightarrow> u\<in>V)"
proof -
  have "u\<in>V \<longleftrightarrow> adjacent_nodes u \<noteq> {}" unfolding V_def adjacent_nodes_def by auto
  also have "\<dots> \<longleftrightarrow> am u \<noteq> []" using fun_relD[OF assms IdI[of u]] by (auto simp: list_set_rel_def in_br_conv)
  finally show ?thesis unfolding am_is_in_V_def by refine_vcg auto
qed    
    
(* Neighbor lists *)
definition n_init :: "(node \<Rightarrow> node list) \<Rightarrow> (node \<Rightarrow> node list) nres" 
  where "n_init am \<equiv> return (am( s := [], t := []) )"
  
definition n_at_end :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> bool nres" 
  where "n_at_end n u \<equiv> do {
    assert (u\<in>V-{s,t});
    return (n u = [])
  }"
    
definition n_get_hd :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> node nres"    
  where "n_get_hd n u \<equiv> do {
    assert (u\<in>V-{s,t} \<and> n u \<noteq> []);
    return (hd (n u))
  }"

definition n_move_next :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> (node \<Rightarrow> node list) nres"
  where "n_move_next n u \<equiv> do {
    assert (u\<in>V-{s,t} \<and> n u \<noteq> []);
    return (n (u := tl (n u)))
  }"
    
definition n_reset :: "(node \<Rightarrow> node list) \<Rightarrow> (node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> (node \<Rightarrow> node list) nres"
  where "n_reset am n u \<equiv> do {
    assert (u\<in>V-{s,t});
    return (n (u := am u))
  }"
    
(* Labeling *)    
definition l_init :: "nat \<Rightarrow> (node \<Rightarrow> nat) nres"
  where "l_init C \<equiv> return ((\<lambda>_. 0)(s := C))"
    
definition l_get :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat nres"    
  where "l_get l u \<equiv> do {
    assert (u \<in> V);
    return (l u)
  }"

definition l_set :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> (node \<Rightarrow> nat) nres"    
  where "l_set l u a \<equiv> do {
    assert (u\<in>V);
    return (l(u := a))
  }"
    
  
(* Compute excess explicitly *)  

definition "xf_rel \<equiv> { ((excess f,cf_of f),f) | f. True }"
  
definition "pp_init_x \<equiv> \<lambda>u. (if u=s then (\<Sum>(u,v)\<in>outgoing s. - c(u,v)) else c (s,u))"
  
lemma excess_pp_init_f[simp]: "excess pp_init_f = pp_init_x"  
  apply (intro ext)  
  subgoal for u  
    unfolding excess_def pp_init_f_def pp_init_x_def
    apply (cases "u=s")  
    subgoal
      unfolding outgoing_def incoming_def    
      by (auto intro: sum.cong simp: sum_negf)
    subgoal proof -
      assume [simp]: "u\<noteq>s"
      have [simp]: "(case e of (u, v) \<Rightarrow> if u = s then c (u, v) else 0) = 0" if "e\<in>outgoing u" for e
        using that by (auto simp: outgoing_def)
      have [simp]: "(case e of (u, v) \<Rightarrow> if u = s then c (u, v) else 0) 
        = (if e = (s,u) then c (s,u) else 0)" 
        if "e\<in>incoming u" for e
        using that by (auto simp: incoming_def split: if_splits)
      show ?thesis by (simp add: sum.delta) (simp add: incoming_def)
    qed 
    done  
  done  
    
definition "pp_init_cf \<equiv> \<lambda>(u,v). if (v=s) then c (v,u) else if u=s then 0 else c (u,v)"
lemma cf_of_pp_init_f[simp]: "cf_of pp_init_f = pp_init_cf"
  apply (intro ext)  
  unfolding pp_init_cf_def pp_init_f_def residualGraph_def
  using no_parallel_edge  
  by auto  
    
  
lemma pp_init_x_rel: "((pp_init_x, pp_init_cf), pp_init_f) \<in> xf_rel"
  unfolding xf_rel_def by auto
  
(* Algorithms for init and mininum adjacent label computation *)  
  
definition "pp_init_xcf2_aux \<equiv> do {
  let x=(\<lambda>_. 0);
  let cf=c;

  foreach (adjacent_nodes s) (\<lambda>v (x,cf). do {
    assert ((s,v)\<in>E);
    assert (s \<noteq> v);
    let a = cf (s,v);
    assert (x v = 0);
    let x = x( s := x s - a, v := a );
    let cf = cf( (s,v) := 0, (v,s) := a);
    return (x,cf)
  }) (x,cf)
}"

(* TODO: Move *)  
lemma adjacent_not_self[simp, intro!]: "v \<notin> adjacent_nodes v"
  unfolding adjacent_nodes_def using no_self_loop 
  by auto
  
  
lemma pp_init_xcf2_aux_spec: 
  shows "pp_init_xcf2_aux \<le> SPEC (\<lambda>(x,cf). x=pp_init_x \<and> cf = pp_init_cf)"
proof -
  have ADJ_S_AUX: "adjacent_nodes s = {v . (s,v)\<in>E}"
    unfolding adjacent_nodes_def using no_incoming_s by auto
    
  have CSU_AUX: "c (s,u) = 0" if "u\<notin>adjacent_nodes s" for u
    using that unfolding adjacent_nodes_def by auto
      
  show ?thesis
    unfolding pp_init_xcf2_aux_def
    apply (refine_vcg FOREACH_rule[where I="\<lambda>it (x,cf). 
        x s = (\<Sum>v\<in>adjacent_nodes s - it. - c(s,v)) 
      \<and> (\<forall>v\<in>adjacent_nodes s. x v = (if v\<in>it then 0 else c (s,v)))
      \<and> (\<forall>v\<in>-insert s (adjacent_nodes s). x v = 0)
      \<and> (\<forall>v\<in>adjacent_nodes s. if v\<notin>it then cf (s,v) = 0 \<and> cf (v,s) = c (s,v) else cf (s,v) = c (s,v) \<and> cf (v,s) = c (v,s))
      \<and> (\<forall>u v. u\<noteq>s \<and> v\<noteq>s \<longrightarrow> cf (u,v) = c (u,v) )
      \<and> (\<forall>u. u\<notin>adjacent_nodes s \<longrightarrow> cf (u,s) = 0 \<and> cf (s,u) = 0)
    "])
    apply (vc_solve simp: it_step_insert_iff simp: CSU_AUX)
    subgoal for v it by (auto simp: ADJ_S_AUX) 
    subgoal for u it _ v by (auto split: if_splits)
    subgoal by (auto simp: ADJ_S_AUX)    
    subgoal by (auto simp: ADJ_S_AUX)    
    subgoal by (auto split: if_splits)    
    (* TODO: This proof is still a bit fragile *)    
    subgoal for x
      unfolding pp_init_x_def
      apply (intro ext)  
      subgoal for u  
        apply (clarsimp simp: ADJ_S_AUX outgoing_def; intro conjI)  
        applyS (auto intro!: sum.reindex_cong[where l=snd] intro: inj_onI)
        applyS (metis (mono_tags, lifting) Compl_iff Graph.zero_cap_simp insertE mem_Collect_eq)  
        done
      done  
    subgoal for x cf    
      unfolding pp_init_cf_def
      apply (intro ext)  
      apply (clarsimp; auto simp: CSU_AUX)
      done  
    done  
qed      
    
definition "pp_init_xcf2 am \<equiv> do {
  x \<leftarrow> x_init;
  cf \<leftarrow> cf_init;

  assert (s\<in>V);
  adj \<leftarrow> am_get am s;
  nfoldli adj (\<lambda>_. True) (\<lambda>v (x,cf). do {
    assert ((s,v)\<in>E);
    assert (s \<noteq> v);
    a \<leftarrow> cf_get cf (s,v);
    x \<leftarrow> x_add x s (-a);
    x \<leftarrow> x_add x v a;
    cf \<leftarrow> cf_set cf (s,v) 0; 
    cf \<leftarrow> cf_set cf (v,s) a; 
    return (x,cf)
  }) (x,cf)
}"
  
lemma pp_init_xcf2_refine_aux:
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  shows "pp_init_xcf2 am \<le> \<Down>Id (pp_init_xcf2_aux)"
  unfolding pp_init_xcf2_def pp_init_xcf2_aux_def
  unfolding x_init_def cf_init_def am_get_def cf_get_def cf_set_def x_add_def  
  apply (simp only: nres_monad_laws)
  supply LFO_refine[OF fun_relD[OF AM IdI[of s]], refine]
  apply refine_rcg  
  using E_ss_VxV  
  by auto
  
  
lemma pp_init_xcf2_refine[refine2]: 
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  shows "pp_init_xcf2 am \<le>\<Down>xf_rel (RETURN pp_init_f)"
  using pp_init_xcf2_refine_aux[OF AM] pp_init_xcf2_aux_spec pp_init_x_rel
  by (auto simp: pw_le_iff refine_pw_simps)  
    

lemma n_init_refine[refine2]: 
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  shows "n_init am \<le> (spec c. (c, rtf_init_n) \<in> (nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel))"
proof -
  have[simp]: "am v = []" if "v\<notin>V" for v
  proof -
    from that have "adjacent_nodes v = {}" unfolding adjacent_nodes_def using E_ss_VxV by auto
    thus ?thesis using fun_relD[OF AM IdI[of v]] by (auto simp: list_set_rel_def in_br_conv)
  qed
  show ?thesis      
    unfolding n_init_def rtf_init_n_def 
    by (auto simp: pw_le_iff refine_pw_simps list_set_autoref_empty fun_relD[OF AM])
qed  
    
definition augment_edge_cf :: "'capacity flow \<Rightarrow> _" where 
  "augment_edge_cf cf \<equiv> \<lambda>(u,v) \<Delta>. (cf)( (u,v) := cf (u,v) - \<Delta>, (v,u) := cf (v,u) + \<Delta>)"
  
lemma cf_of_augment_edge[simp]:
  assumes A: "(u,v)\<in>cfE_of f" 
  assumes "Labeling c s t f l"
  shows "cf_of (augment_edge f (u,v) \<Delta>) = augment_edge_cf (cf_of f) (u,v) \<Delta>"  
proof -  
  interpret Labeling c s t f l by fact
  
  show "cf_of (augment_edge f (u, v) \<Delta>) = augment_edge_cf cf (u, v) \<Delta>"
    by (simp add: augment_edge_cf_def A)
qed      
    
    
    
    
definition "push2_aux x cf \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  assert ( u \<noteq> v );
  let \<Delta> = min (x u) (cf (u,v));
  return (x( u := x u - \<Delta>, v := x v + \<Delta> ),augment_edge_cf cf (u,v) \<Delta>)
}"
    
lemma push2_aux_refine: "\<lbrakk>((x,cf),f)\<in>xf_rel; (ei,e)\<in>Id\<times>\<^sub>rId\<rbrakk> \<Longrightarrow> push2_aux x cf ei \<le> \<Down>xf_rel (push f l e)"
  unfolding push_def push2_aux_def
  apply refine_vcg  
  apply (vc_solve simp: xf_rel_def no_self_loop)
  subgoal for u v 
    unfolding push_precond_def using cfE_of_ss_invE by auto
  subgoal for u v 
    apply (rule conjI)
    subgoal proof -
      assume "Labeling c s t f l"
      then interpret Labeling c s t f l .
          thm cfE_ss_invE
      assume "push_precond f l (u, v)"    
      then interpret l': push_effect_locale c s t f l u v by unfold_locales
      from l'.excess'_if show ?thesis by (auto simp: l'.\<Delta>_def push_effect_def)
    qed
    subgoal unfolding push_effect_def push_precond_def by auto
    done  
  done

definition "push2 x cf \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  xu \<leftarrow> x_get x u;
  cfuv \<leftarrow> cf_get cf (u,v);
  cfvu \<leftarrow> cf_get cf (v,u);
  let \<Delta> = min xu cfuv;
  x \<leftarrow> x_add x u (-\<Delta>);
  x \<leftarrow> x_add x v \<Delta>;

  cf \<leftarrow> cf_set cf (u,v) (cfuv - \<Delta>);
  cf \<leftarrow> cf_set cf (v,u) (cfvu + \<Delta>);
  
  return (x,cf)
}"
    
lemma push2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel" "(ei,e)\<in>Id\<times>\<^sub>rId"
  shows "push2 x cf ei \<le> \<Down>xf_rel (push f l e)"
proof -
  have "push2 x cf ei \<le> \<Down>Id (push2_aux x cf ei)"  
    unfolding push2_def push2_aux_def
    unfolding x_get_def x_add_def cf_get_def cf_set_def
    unfolding augment_edge_cf_def  
    apply (simp only: nres_monad_laws)  
    apply refine_rcg  
    using E_ss_VxV  
    by auto  
  also note push2_aux_refine[OF assms]    
  finally show ?thesis . 
qed  
    
definition (in Network) "min_adj_label_aux cf l u \<equiv> do {
  assert (u\<in>V);
  x \<leftarrow> foreach (adjacent_nodes u) (\<lambda>v x. do {
    assert ((u,v)\<in>E\<union>E\<inverse>);
    assert (v\<in>V);
    if (cf (u,v) \<noteq> 0) then 
      case x of 
        None \<Rightarrow> return (Some (l v)) 
      | Some xx \<Rightarrow> return (Some (min (l v) (xx)))
    else
      return x
  }) None;

  assert (x\<noteq>None);
  return (the x)
}"
    
(* TODO: Move *)  
lemma (in Network) adjacent_nodes_ss_V: "adjacent_nodes u \<subseteq> V"  
  unfolding adjacent_nodes_def using E_ss_VxV by auto

lemma (in -) set_filter_xform_aux: 
  "{ f x | x. ( x = a \<or> x\<in>S \<and> x\<notin>it ) \<and> P x } = (if P a then {f a} else {}) \<union> {f x | x. x\<in>S-it \<and> P x}"    
  by auto
    
lemma (in Labeling) min_adj_label_aux_spec: 
  assumes PRE: "relabel_precond f l u"
  shows "min_adj_label_aux cf l u \<le> SPEC (\<lambda>x. x = Min { l v | v. (u,v)\<in>cf.E })"
proof -
  have AUX: "cf (u,v) \<noteq> 0 \<longleftrightarrow> (u,v)\<in>cf.E" for v unfolding cf.E_def by auto
  
  have EQ: "{ l v | v. (u,v)\<in>cf.E } = { l v | v. v\<in>adjacent_nodes u \<and> cf (u,v)\<noteq>0 }"
    unfolding AUX
    using cfE_ss_invE
    by (auto simp: adjacent_nodes_def)
  
  define Min_option :: "nat set \<rightharpoonup> nat" where "Min_option X \<equiv> if X={} then None else Some (Min X)" for X
      
  from PRE active_has_cf_outgoing have "cf.outgoing u \<noteq> {}" unfolding relabel_precond_def by auto
  hence [simp]: "u\<in>V" unfolding cf.outgoing_def using cfE_of_ss_VxV by auto
  from \<open>cf.outgoing u \<noteq> {}\<close> have AUX2: "\<exists>v. v \<in> adjacent_nodes u \<and> cf (u, v) \<noteq> 0"
    by (smt AUX Collect_empty_eq Image_singleton_iff UnCI adjacent_nodes_def cf.outgoing_def cf_def converse_iff prod.simps(2))
      
  show ?thesis unfolding min_adj_label_aux_def EQ   
    apply (refine_vcg 
        FOREACH_rule[where I="\<lambda>it x. x = Min_option { l v | v. v\<in>adjacent_nodes u - it \<and> cf (u,v)\<noteq>0 }"]
        )  
    apply (vc_solve simp: Min_option_def it_step_insert_iff set_filter_xform_aux split: if_splits)
    subgoal unfolding adjacent_nodes_def by auto  
    subgoal unfolding adjacent_nodes_def by auto  
    subgoal using adjacent_nodes_ss_V by auto  
    subgoal using adjacent_nodes_ss_V by auto
    subgoal by (auto simp: Min.insert_remove)
    subgoal using AUX2 by auto
    done    
qed        

definition "min_adj_label am cf l u \<equiv> do {
  assert (u\<in>V);
  adj \<leftarrow> am_get am u;
  x \<leftarrow> nfoldli adj (\<lambda>_. True) (\<lambda>v x. do {
    assert ((u,v)\<in> E \<union> E\<inverse>);
    assert (v\<in>V);
    cfuv \<leftarrow> cf_get cf (u,v);
    if (cfuv \<noteq> 0) then do {
      lv \<leftarrow> l_get l v;
      case x of 
        None \<Rightarrow> return (Some lv) 
      | Some xx \<Rightarrow> return (Some (min lv xx))
    } else
      return x
  }) None;

  assert (x\<noteq>None);
  return (the x)
}"

lemma min_adj_label_refine[THEN order_trans, refine_vcg]:
  assumes "Labeling c s t f l"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes PRE: "relabel_precond f l u"
  assumes [simp]: "cf = cf_of f"  
  shows "min_adj_label am cf l u \<le> SPEC (\<lambda>x. x = Min { l v | v. (u,v)\<in>cfE_of f })"  
proof - 
  interpret Labeling c s t f l by fact

  have "min_adj_label am (cf_of f) l u \<le> \<Down>Id (min_adj_label_aux (cf_of f) l u)"  
    unfolding min_adj_label_def min_adj_label_aux_def Let_def
    unfolding am_get_def cf_get_def l_get_def  
    apply (simp only: nres_monad_laws)  
    supply LFO_refine[OF fun_relD[OF AM IdI] _ IdI, refine]
    apply (refine_rcg)
    by auto  
  also note min_adj_label_aux_spec[OF PRE]    
  finally show ?thesis by simp  
qed      
  
  
    
definition "relabel2 am cf l u \<equiv> do {
  assert (u\<in>V - {s,t});
  nl \<leftarrow> min_adj_label am cf l u;
  l \<leftarrow> l_set l u (nl+1);
  return l
}"

lemma relabel2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(li,l)\<in>Id" "(ui,u)\<in>Id"
  shows "relabel2 am cf li ui \<le> \<Down>Id (relabel f l u)"    
proof -
  have [simp]: "{l v |v. v \<in> V \<and> cf_of f (u, v) \<noteq> 0} = {l v |v. cf_of f (u, v) \<noteq> 0}"
    using cfE_of_ss_VxV[of f] 
    by (auto simp: Graph.E_def)
  
  show ?thesis
    using assms
    unfolding relabel2_def relabel_def
    unfolding l_set_def  
    apply (refine_vcg AM)
    apply (vc_solve simp: xf_rel_def relabel_effect_def)
    apply auto  
    done
qed
    
definition "discharge2 am x cf l n u \<equiv> do {  
  assert (u \<in> V);
  monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>((x,cf),l,n). do { xu \<leftarrow> x_get x u; return (xu \<noteq> 0) } ) 
    (\<lambda>((x,cf),l,n). do {
      at_end \<leftarrow> n_at_end n u;
      if at_end then do {
        l \<leftarrow> relabel2 am cf l u;
        n \<leftarrow> n_reset am n u;
        return ((x,cf),l,n)
      } else do {
        v \<leftarrow> n_get_hd n u;
        cfuv \<leftarrow> cf_get cf (u,v);
        lu \<leftarrow> l_get l u;
        lv \<leftarrow> l_get l v;
        if (cfuv \<noteq> 0 \<and> lu = lv + 1) then do {
          (x,cf) \<leftarrow> push2 x cf (u,v);
          return ((x,cf),l,n)
        } else do {
          n \<leftarrow> n_move_next n u;
          return ((x,cf),l,n)
        }
      }
    }) ((x,cf),l,n)
}"

lemma discharge_structure_refine_aux:
  assumes SR: "(ni,n)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
  assumes SU: "(ui,u)\<in>Id"  
  assumes fNR: "fNi \<le> \<Down>R fN"
  assumes UIV: "u\<in>V-{s,t}"  
  assumes fSR: "\<And>v vi vs. \<lbrakk> (vi,v)\<in>Id; v\<in>n u; ni u = v#vs; (v#vs,n u)\<in>\<langle>nat_rel\<rangle>list_set_rel \<rbrakk> 
    \<Longrightarrow> fSi vi \<le> \<Down>R (fS v)"
  shows
  "( do {
    at_end \<leftarrow> n_at_end ni ui;
    if at_end then fNi
    else do {
      v \<leftarrow> n_get_hd ni ui;
      fSi v
    }
  } ) \<le> \<Down>R (

  do {
    v \<leftarrow> selectp v. v\<in>n u;
    case v of
      None \<Rightarrow> fN
    | Some v \<Rightarrow> fS v
  })" (is "?lhs \<le>\<Down>R ?rhs")
  unfolding n_at_end_def n_get_hd_def
  apply (simp only: nres_monad_laws)  
  apply (cases "ni u")
  subgoal
    using fun_relD[OF SR SU] SU UIV fNR
    by (auto simp: list_set_rel_def in_br_conv pw_le_iff refine_pw_simps)
    
  subgoal for v vs
    using fun_relD[OF SR SU] SU UIV
    using fSR[OF IdI[of v], of vs]  
    apply (clarsimp simp: list_set_rel_def in_br_conv pw_le_iff refine_pw_simps split: option.splits)
    by fastforce  
  done    
  
lemma xf_rel_RELATES[refine_dref_RELATES]: "RELATES xf_rel" by (auto simp: RELATES_def)
  
lemma discharge2_refine[refine]:     
  assumes A: "((x,cf),f) \<in> xf_rel"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(li,l)\<in>Id" "(ui,u)\<in>Id"
  assumes NR: "(ni,n)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"  
  shows "discharge2 am x cf li ni ui \<le> \<Down>(xf_rel \<times>\<^sub>r Id \<times>\<^sub>r (nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel)) (discharge f l n u)"  
  unfolding discharge2_def discharge_def
  apply (rewrite in "monadic_WHILEIT _ _ \<hole> _" vcg_intro_frame)  
  apply refine_rcg  
  apply (vc_solve simp: A NR)
  subgoal by (simp add: xf_rel_def x_get_def)  
  subgoal for f l n x cf ni   
    apply (subst vcg_rem_frame)
    unfolding n_reset_def cf_get_def l_get_def n_move_next_def  
    apply (simp only: nres_monad_laws)  
    apply (rule discharge_structure_refine_aux; (refine_vcg AM)?; (assumption)?)  
    apply (vc_solve simp: fun_relD fun_relD[OF AM])  
    subgoal for v vs unfolding xf_rel_def Graph.E_def by auto
    subgoal for v vs by (auto simp: list_set_rel_def in_br_conv)  
    done
  done
    
(* Algorithm to determine card V and initial queue *)    
    
lemma V_is_adj_nodes: "V = { v . adjacent_nodes v \<noteq> {} }"
  unfolding V_def adjacent_nodes_def by auto
    
definition "init_CQ N am \<equiv> do {
  let cardV=0;
  let Q=[];
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v (cardV,Q). do {
    assert (v<N);
    inV \<leftarrow> am_is_in_V am v;
    if inV then do {
      let cardV = cardV + 1;
      if v\<noteq>s \<and> v\<noteq>t then
        return (cardV,v#Q)
      else 
        return (cardV,Q)
    } else
      return (cardV,Q)
  }) (cardV,Q)
}"    

lemma init_CQ_correct[THEN order_trans, refine_vcg]:
  assumes V_ss: "V \<subseteq> {0..<N}"
  assumes AMR: "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"  
  shows "init_CQ N am \<le> SPEC (\<lambda>(C,Q). C = card V \<and> distinct Q \<and> set Q = V-{s,t})"
  unfolding init_CQ_def  
  apply (refine_vcg 
      nfoldli_rule[where I="\<lambda>l1 _ (C,Q). C = card (V\<inter>set l1) \<and> distinct Q \<and> set Q = (V\<inter>set l1)-{s,t} "]
      AMR
      )  
  apply clarsimp_all  
  using V_ss  
  apply (auto simp: upt_eq_lel_conv Int_absorb2)  
  done    
    
definition "relabel_to_front2 N am \<equiv> do {
  (cardV, L_right) \<leftarrow> init_CQ N am;

  xcf \<leftarrow> pp_init_xcf2 am;
  l \<leftarrow> l_init cardV;
  n \<leftarrow> n_init am;

  let L_left=[];

  ((x,cf),l,n,L_left,L_right) \<leftarrow> while\<^sub>T (\<lambda>((x,cf),l,n,L_left,L_right). L_right \<noteq> []) (\<lambda>((x,cf),l,n,L_left,L_right). do {
    assert (L_right \<noteq> []);
    let u = hd L_right;
    old_lu \<leftarrow> l_get l u;

    ((x,cf),l,n) \<leftarrow> discharge2 am x cf l n u;

    lu \<leftarrow> l_get l u;
    if (lu \<noteq> old_lu) then do {
      (* Move u to front of l, and restart scanning L. The cost for rev_append is amortized by going to next node in L *)
      let (L_left,L_right) = ([u],rev_append L_left (tl L_right));
      return ((x,cf),l,n,L_left,L_right)
    } else do {
      (* Goto next node in L *)
      let (L_left,L_right) = (u#L_left, tl L_right);
      return ((x,cf),l,n,L_left,L_right)
    }

  }) (xcf,l,n,L_left,L_right);

  return cf
}"
  
(* TODO: Move to Refine_Basic convenience *)  
lemma (in -) refine2spec_aux:
  "a \<le> \<Down>R b \<longleftrightarrow> ( (nofail b \<longrightarrow> a \<le> SPEC ( \<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )) )"
  by (auto simp: pw_le_iff refine_pw_simps)
  
lemma (in -) refine2specI:
  assumes "nofail b \<Longrightarrow> a \<le> SPEC (\<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )"
  shows "a \<le> \<Down>R b"  
  using assms by (simp add: refine2spec_aux)  
  
    
lemma relabel_to_front2_refine[refine]: 
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes V_ss: "V \<subseteq> {0..<N}"
  shows "relabel_to_front2 N am \<le> \<Down>(br (flow_of_cf) (RPreGraph c s t)) relabel_to_front"
proof -
  define s_rel :: "(_ \<times> ( 'capacity flow * (nat\<Rightarrow>nat) * (node\<Rightarrow>node set) * node list * node list)) set"
    where "s_rel \<equiv> xf_rel \<times>\<^sub>r Id \<times>\<^sub>r (nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel) \<times>\<^sub>r br rev (\<lambda>_. True) \<times>\<^sub>r Id"
  
  have [refine_dref_RELATES]: "RELATES s_rel" unfolding RELATES_def ..
      
  {
    fix f l n
    assume "neighbor_invar c s t f l n"
    then interpret neighbor_invar c s t f l n .  
    have G1: "flow_of_cf cf = f" by (rule fo_rg_inv)
    have G2: "RPreGraph c s t cf" by (rule is_RPreGraph)
    note G1 G2    
  } note AUX1=this   
      
  have AUXR: "do {
      (cardV, L_right) \<leftarrow> init_CQ N am;
      xcf \<leftarrow> pp_init_xcf2 am;
      l \<leftarrow> l_init cardV;
      n \<leftarrow> n_init am;
      Fi L_right xcf l n
    }
    \<le> \<Down>R (do {
      L_right \<leftarrow> spec l. distinct l \<and> set l = V - {s, t};
      F L_right
    })
  " 
  if "\<And>L_right xcf n. \<lbrakk> (xcf,pp_init_f)\<in>xf_rel; (n,rtf_init_n) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel \<rbrakk> 
    \<Longrightarrow> Fi L_right xcf pp_init_l n \<le> \<Down>R (F L_right)"
  for Fi F R
    unfolding l_init_def
    apply (rule refine2specI)
    supply pp_init_xcf2_refine[OF AM, unfolded conc_fun_RETURN, THEN order_trans, refine_vcg]  
    supply n_init_refine[OF AM,THEN order_trans, refine_vcg]  
    apply (refine_vcg AM V_ss)
    apply clarsimp  
    subgoal for L_right x cf n
      using that[of "(x,cf)" n L_right]
      unfolding pp_init_l_def  
      by (clarsimp simp: pw_le_iff refine_pw_simps; meson)  
    done  
  show ?thesis
    unfolding relabel_to_front2_def relabel_to_front_def Let_def l_get_def
    apply (simp only: nres_monad_laws)  
    apply (rule AUXR)  
    apply (refine_rcg AM)
    apply refine_dref_type
    unfolding s_rel_def
    apply (vc_solve simp: in_br_conv rev_append_eq xf_rel_def AUX1 fun_relD)
    done  
qed  
  
end -- \<open>Network\<close>  
  
  
definition "fun_rel'\<equiv> fun_rel"
    
lemma fun_rel'_id[simp,fcomp_norm_unfold]:
  "\<langle>Id,Id\<rangle>fun_rel' = Id" unfolding fun_rel'_def by auto 
  
  
context
  notes [simp] = IS_PRES_EQ_def fun_rel'_def
begin
  sepref_decl_op fun_apply: "\<lambda>f x. f x" :: "(\<langle>A,B\<rangle>fun_rel') \<rightarrow> A \<rightarrow> B" .
  sepref_decl_op fun_update: fun_upd :: "(\<langle>A,B\<rangle>fun_rel') \<rightarrow> A \<rightarrow> B \<rightarrow> \<langle>A,B\<rangle>fun_rel'" where "IS_PRES_EQ A" .
  sepref_decl_op fun_const: "\<lambda>c _. c" :: "B \<rightarrow> \<langle>A,B\<rangle>fun_rel'" .

  lemma fun_fixed_const_fref: 
    "\<lbrakk> (ci,c)\<in>B \<rbrakk> \<Longrightarrow> (uncurry0 (return (\<lambda>_. ci)), uncurry0 (return (\<lambda>_. c))) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>\<langle>A,B\<rangle>fun_rel'\<rangle>nres_rel"
    by (auto intro!: frefI nres_relI)
      
end

(* TODO: Move *)  
  
lemma uminus_hnr[sepref_import_param]: "(uminus,uminus)\<in>int_rel \<rightarrow> int_rel" by auto  
  
  
(* TODO: Duplicated from EdmondsKarp_Impl! *)  
locale Network_Impl = Network c s t for c :: "capacity_impl graph" and s t +
  fixes N :: nat
  assumes V_ss: "V\<subseteq>{0..<N}"
begin  
  lemma nwi_this: "Network_Impl c s t N" by unfold_locales
  
  lemma E_ss: "E \<subseteq> {0..<N}\<times>{0..<N}" using E_ss_VxV V_ss by auto

      
  (* Simp setup for side-condition discharging *)    
  lemma mtx_nonzero_iff[simp]: "mtx_nonzero c = E" unfolding E_def by (auto simp: mtx_nonzero_def)

  lemma mtx_nonzeroN: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<N}" using E_ss by simp

  lemma [simp]: "(u,v) \<in> mtx_nonzero c \<Longrightarrow> u<N \<and> v<N" using mtx_nonzeroN by auto   
      
  lemma [simp]: "v\<in>V \<Longrightarrow> v<N" using V_ss by auto
  
  lemma [simp]: "e\<in>E \<or> e\<in>E\<inverse> \<Longrightarrow> case e of (u,v) \<Rightarrow> u<N \<and> v<N"    
    using E_ss by auto
  lemmas [simp] = nested_case_prod_simp
      
  text \<open>Declare some variables to Sepref. \<close>
  lemmas [id_rules] = 
    itypeI[Pure.of N "TYPE(nat)"]  
    itypeI[Pure.of s "TYPE(node)"]  
    itypeI[Pure.of t "TYPE(node)"]  
    itypeI[Pure.of c "TYPE(capacity_impl graph)"]  
  text \<open>Instruct Sepref to not refine these parameters. This is expressed
    by using identity as refinement relation.\<close>
  lemmas [sepref_import_param] = 
    IdI[of N]
    IdI[of s]
    IdI[of t]
    (*IdI[of c]*)

  lemma [sepref_fr_rules]: 
    "(uncurry0 (return c),uncurry0 (RETURN c))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
    by (sepref_to_hoare) sep_auto 
    
  abbreviation cap_assn :: "capacity_impl \<Rightarrow> _" where "cap_assn \<equiv> id_assn"  
  definition "cf_assn \<equiv> asmtx_assn N cap_assn"  
  abbreviation "edge_assn \<equiv> nat_assn \<times>\<^sub>a nat_assn"  
  abbreviation (input) "node_assn \<equiv> nat_assn"  
    
  text \<open>Implementing the basic operations\<close>
  sepref_register cf_get cf_set cf_init 
  sepref_thm cf_get_impl is "uncurry (PR_CONST cf_get)" :: "cf_assn\<^sup>k *\<^sub>a edge_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn"  
    unfolding cf_get_def cf_assn_def PR_CONST_def
    by sepref
  concrete_definition (in -) cf_get_impl uses Network_Impl.cf_get_impl.refine_raw is "(uncurry ?f,_)\<in>_"
      
  sepref_thm cf_set_impl is "uncurry2 (PR_CONST cf_set)" :: "cf_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k *\<^sub>a cap_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn"  
    unfolding cf_set_def cf_assn_def PR_CONST_def by sepref
  concrete_definition (in -) cf_set_impl uses Network_Impl.cf_set_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"

  sepref_thm cf_init_impl is "uncurry0 (PR_CONST cf_init)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
    unfolding PR_CONST_def cf_assn_def cf_init_def 
    apply (rewrite amtx_fold_custom_new[of N N])
    by sepref  
  concrete_definition (in -) cf_init_impl uses Network_Impl.cf_init_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = cf_get_impl.refine[OF nwi_this] cf_set_impl.refine[OF nwi_this] cf_init_impl.refine[OF nwi_this]
      
  text \<open>Function from nodes, with default value\<close>
  definition "is_nf dflt f a \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(length l = N \<and> (\<forall>i<N. l!i = f i) \<and> (\<forall>i\<ge>N. f i = dflt))"
    
  lemma nf_init_rule[sep_heap_rules]: "<emp> Array.new N dflt <is_nf dflt (\<lambda>_. dflt)>"
    unfolding is_nf_def by sep_auto

  lemma nf_copy_rule[sep_heap_rules]: "<is_nf dflt f a> array_copy a <\<lambda>r. is_nf dflt f a * is_nf dflt f r>"
    unfolding is_nf_def by sep_auto
    
  lemma nf_lookup_rule[sep_heap_rules]: "v<N \<Longrightarrow> <is_nf dflt f a> Array.nth a v <\<lambda>r. is_nf dflt f a *\<up>(r = f v)>"
    unfolding is_nf_def by sep_auto
    
  lemma nf_update_rule[sep_heap_rules]: "v<N \<Longrightarrow> <is_nf dflt f a> Array.upd v x a <is_nf dflt (f(v:=x))>"  
    unfolding is_nf_def by sep_auto

  definition "am_assn \<equiv> is_nf ([]::nat list)"    
  sepref_register am_get  
  lemma [sepref_fr_rules]: "(uncurry Array.nth, uncurry (PR_CONST am_get)) \<in> am_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"  
    unfolding am_assn_def am_get_def list_assn_pure_conv
    by sepref_to_hoare (sep_auto simp: refine_pw_simps)

      
  definition (in -) "am_is_in_V_impl am u \<equiv> do {
    amu \<leftarrow> Array.nth am u;
    return (\<not>is_Nil amu)
  }"    
  sepref_register am_is_in_V    
  lemma [sepref_fr_rules]: "(uncurry am_is_in_V_impl, uncurry (am_is_in_V)) 
    \<in> [\<lambda>(_,v). v<N]\<^sub>a am_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow> bool_assn"  
    unfolding am_assn_def am_is_in_V_def am_is_in_V_impl_def
    apply sepref_to_hoare 
    apply (sep_auto simp: refine_pw_simps split: list.split)
    done
      
  definition "n_assn \<equiv> is_nf ([]::nat list)"    
      
  definition (in -) "n_init_impl s t am \<equiv> do {
    n \<leftarrow> array_copy am;
    n \<leftarrow> Array.upd s [] n;
    n \<leftarrow> Array.upd t [] n;
    return n
  }"      
      
  sepref_register n_init  
  lemma [sepref_fr_rules]: "(n_init_impl s t,PR_CONST n_init) \<in> am_assn\<^sup>k \<rightarrow>\<^sub>a n_assn" 
    apply sepref_to_hoare
    unfolding am_assn_def n_assn_def n_init_impl_def n_init_def
    by (sep_auto)  
      
  definition (in -) "n_at_end_impl n u \<equiv> do {
    nu \<leftarrow> Array.nth n u;
    return (is_Nil nu)
  }"
      
  sepref_register n_at_end
  lemma [sepref_fr_rules]: "(uncurry n_at_end_impl, uncurry (PR_CONST n_at_end)) \<in> n_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
    apply sepref_to_hoare unfolding n_at_end_impl_def n_at_end_def n_assn_def
    by (sep_auto simp: refine_pw_simps split: list.split)
    
  definition (in -) "n_get_hd_impl n u \<equiv> do {
    nu \<leftarrow> Array.nth n u;
    return (hd nu)
  }"      
  sepref_register n_get_hd
  lemma [sepref_fr_rules]: "(uncurry n_get_hd_impl, uncurry (PR_CONST n_get_hd)) \<in> n_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a node_assn"  
    apply sepref_to_hoare unfolding n_get_hd_impl_def n_get_hd_def n_assn_def
    by (sep_auto simp: refine_pw_simps)
    
  definition (in -) "n_move_next_impl n u \<equiv> do {
    nu \<leftarrow> Array.nth n u;
    n \<leftarrow> Array.upd u (tl nu) n;
    return n
  }" 
  sepref_register n_move_next
  lemma [sepref_fr_rules]: "(uncurry n_move_next_impl, uncurry (PR_CONST n_move_next)) \<in> n_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a n_assn"  
    apply sepref_to_hoare unfolding n_move_next_impl_def n_move_next_def n_assn_def
    by (sep_auto simp: refine_pw_simps)
    
  definition (in -) "n_reset_impl am n u \<equiv> do {
    nu \<leftarrow> Array.nth am u;
    n \<leftarrow> Array.upd u nu n;
    return n
  }"
  sepref_register n_reset
  lemma [sepref_fr_rules]: "(uncurry2 n_reset_impl, uncurry2 (PR_CONST n_reset)) \<in> am_assn\<^sup>k *\<^sub>a n_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a n_assn"  
    apply sepref_to_hoare unfolding n_reset_impl_def n_reset_def n_assn_def am_assn_def
    by (sep_auto simp: refine_pw_simps)
    
  definition "x_assn \<equiv> is_nf (0::capacity_impl)"    
    
  lemma [sepref_fr_rules]: "(uncurry0 (Array.new N 0), uncurry0 x_init) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a x_assn"  
    apply sepref_to_hoare unfolding x_assn_def x_init_def by sep_auto
      
  sepref_register x_get    
  lemma [sepref_fr_rules]: "(uncurry Array.nth, uncurry (PR_CONST x_get)) \<in> x_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn"
    apply sepref_to_hoare unfolding x_assn_def x_get_def by (sep_auto simp: refine_pw_simps)
      
  definition (in -) "x_add_impl x u \<Delta> \<equiv> do {
    xu \<leftarrow> Array.nth x u;
    x \<leftarrow> Array.upd u (xu+\<Delta>) x;
    return x
  }"  
  sepref_register x_add
  lemma [sepref_fr_rules]: "(uncurry2 x_add_impl, uncurry2 (PR_CONST x_add)) \<in> x_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a cap_assn\<^sup>k \<rightarrow>\<^sub>a x_assn"  
    apply sepref_to_hoare unfolding x_assn_def x_add_impl_def x_add_def by (sep_auto simp: refine_pw_simps)

  definition "l_assn \<equiv> is_nf (0::nat)"    
  definition (in -) "l_init_impl N s cardV \<equiv> do {
    l \<leftarrow> Array.new N (0::nat);
    l \<leftarrow> Array.upd s cardV l;
    return l
  }"  
  sepref_register l_init  
  lemma [sepref_fr_rules]: "(l_init_impl N s, (PR_CONST l_init)) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"  
    apply sepref_to_hoare unfolding l_assn_def l_init_def l_init_impl_def by sep_auto
      
  sepref_register l_get    
  lemma [sepref_fr_rules]: "(uncurry Array.nth, uncurry (PR_CONST l_get)) \<in> l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    apply sepref_to_hoare unfolding l_assn_def l_get_def by (sep_auto simp: refine_pw_simps)
      
  sepref_register l_set
  lemma [sepref_fr_rules]: "(uncurry2 (\<lambda>a i x. Array.upd i x a), uncurry2 (PR_CONST l_set)) \<in> l_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"
    apply sepref_to_hoare unfolding l_assn_def l_set_def by (sep_auto simp: refine_pw_simps split: prod.split)

  abbreviation "xcf_assn \<equiv>  x_assn \<times>\<^sub>a cf_assn"    
      
  term pp_init_xcf2
  sepref_register pp_init_xcf2    
  sepref_thm pp_init_xcf_impl is "PR_CONST pp_init_xcf2" :: "am_assn\<^sup>k \<rightarrow>\<^sub>a xcf_assn"
    unfolding pp_init_xcf2_def PR_CONST_def
    by sepref  
  concrete_definition (in -) pp_init_xcf_impl uses Network_Impl.pp_init_xcf_impl.refine_raw
  lemmas [sepref_fr_rules] = pp_init_xcf_impl.refine[OF nwi_this]
      
  sepref_register push2  
  sepref_thm push_impl is "uncurry2 (PR_CONST push2)" :: "x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k \<rightarrow>\<^sub>a xcf_assn"  
    unfolding push2_def PR_CONST_def
    by sepref
  concrete_definition (in -) push_impl uses Network_Impl.push_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = push_impl.refine[OF nwi_this]
    
  sepref_register min_adj_label
  sepref_thm min_adj_label_impl is "uncurry3 (PR_CONST min_adj_label)" :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"  
    unfolding min_adj_label_def PR_CONST_def
    by sepref  
  concrete_definition (in -) min_adj_label_impl uses Network_Impl.min_adj_label_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = min_adj_label_impl.refine[OF nwi_this]    
    
  sepref_register relabel2
  sepref_thm relabel_impl is "uncurry3 (PR_CONST relabel2)" :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a l_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"  
    unfolding relabel2_def PR_CONST_def
    by sepref  
  concrete_definition (in -) relabel_impl uses Network_Impl.relabel_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = relabel_impl.refine[OF nwi_this]    
    
  sepref_register discharge2
  sepref_thm discharge_impl is "uncurry5 (PR_CONST discharge2)" 
    :: "am_assn\<^sup>k *\<^sub>a x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a l_assn\<^sup>d *\<^sub>a n_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a xcf_assn \<times>\<^sub>a l_assn \<times>\<^sub>a n_assn"  
    unfolding discharge2_def PR_CONST_def
    by sepref  
  concrete_definition (in -) discharge_impl uses Network_Impl.discharge_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = discharge_impl.refine[OF nwi_this]    
  
  sepref_register "init_CQ"
    
  sepref_thm init_CQ_impl is "uncurry (PR_CONST init_CQ)" 
    :: "[\<lambda>(x,_). x=N]\<^sub>a nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k \<rightarrow> nat_assn \<times>\<^sub>a list_assn nat_assn"
    unfolding init_CQ_def PR_CONST_def
    apply (rewrite HOL_list.fold_custom_empty)
    by sepref
  concrete_definition (in -) init_CQ_impl uses Network_Impl.init_CQ_impl.refine_raw is "(uncurry ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = init_CQ_impl.refine[OF nwi_this]    
    
    
  (* TODO: Move *)  
  lemma (in -) rev_append_hnr[param,sepref_import_param]:
    "(rev_append, rev_append) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
    unfolding rev_append_def by parametricity
    
  sepref_register relabel_to_front2
  sepref_thm relabel_to_front_impl is 
    "uncurry (PR_CONST relabel_to_front2)" :: "[\<lambda>(x,_). x=N]\<^sub>a nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k \<rightarrow> cf_assn"  
    unfolding relabel_to_front2_def PR_CONST_def
    supply [[goals_limit = 1]]  
    apply (rewrite in "Let [] _" HOL_list.fold_custom_empty)
    apply (rewrite in "[_]" HOL_list.fold_custom_empty)
    by sepref  
  concrete_definition (in -) relabel_to_front_impl uses Network_Impl.relabel_to_front_impl.refine_raw is "(uncurry ?f,_)\<in>_"
  lemmas [sepref_fr_rules] = relabel_to_front_impl.refine[OF nwi_this]
      
      
end  
  
export_code relabel_to_front_impl in SML_imp module_name Relabel_To_Front
  
thm relabel_to_front_impl_def  
  
context Network_Impl begin
  (*xxx, ctd here: Move this to Network locale! Define xxx_assn outside locales!?*)
  
  theorem relabel_to_front_impl_correct: 
    assumes VN: "Graph.V c \<subseteq> {0..<N}"
    assumes ABS_PS: "is_adj_map am"
    shows "
      <am_assn am ami> 
        relabel_to_front_impl c s t N N ami
      <\<lambda>cfi. \<exists>\<^sub>Acf. cf_assn cf cfi * \<up>(isMaxFlow (flow_of_cf cf))>\<^sub>t"
  proof -
    have AM: "(am, adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
      using ABS_PS
      unfolding is_adj_map_def adjacent_nodes_def list_set_rel_def
      by (auto simp: in_br_conv)
        
    note relabel_to_front2_refine[OF AM VN]    
    also note relabel_to_front_correct
    finally have R1: "relabel_to_front2 N am \<le> \<Down> (br flow_of_cf (RPreGraph c s t)) (SPEC isMaxFlow)" .  

    have [simp]: "nofail (\<Down>R (RES X))" for R X by (auto simp: refine_pw_simps)
        
    note R2 = relabel_to_front_impl.refine[OF nwi_this, to_hnr, OF refl, unfolded autoref_tag_defs]
    note R3 = hn_refine_ref[OF R1 R2, of ami N]  
    note R4 = R3[unfolded hn_ctxt_def pure_def, THEN hn_refineD, simplified]
      
    show ?thesis  
      by (sep_auto heap: R4 simp: pw_le_iff refine_pw_simps in_br_conv)
  qed
end    


  
  
  
  
end
