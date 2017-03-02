section \<open>Efficient Implementation of the FIFO Push-Relabel Algorithm\<close>
theory Fifo_Push_Relabel_Impl
imports 
  Fifo_Push_Relabel
  "../Lib/DRAT_Misc"
  "$AFP/Refine_Imperative_HOL/IICF/IICF"
  "../Flow_Networks/Graph_Impl" 
  "../Net_Check/NetCheck"
begin  

subsection \<open>Locale for Implementing Networks\<close>  
text \<open>We define a locale that fixes the type of the capacities to be integers,
  and assumes that the nodes are natural numbers in the 
  range @{term "{0..<N}"}.\<close>  
  
type_synonym flow_impl = "capacity_impl flow"  
type_synonym excess_impl = "node \<Rightarrow> capacity_impl"  
  
  
(* TODO: Duplicated from EdmondsKarp_Impl! Merge! *)  
locale Network_Impl = Network c s t for c :: "capacity_impl graph" and s t +
  fixes N :: nat
  assumes V_ss: "V\<subseteq>{0..<N}"
begin  
  lemma nwi_this: "Network_Impl c s t N" by unfold_locales
  
  lemma E_ss: "E \<subseteq> {0..<N}\<times>{0..<N}" using E_ss_VxV V_ss by auto

      
  (* Simp setup for side-condition discharging *)    
  lemma mtx_nonzero_iff[simp]: "mtx_nonzero c = E" 
    unfolding E_def by (auto simp: mtx_nonzero_def)

  lemma mtx_nonzeroN: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<N}" using E_ss by simp

  lemma in_mtx_nonzeroN[simp]: "(u,v) \<in> mtx_nonzero c \<Longrightarrow> u<N \<and> v<N" 
    using mtx_nonzeroN by auto   
      
  lemma inV_less_N[simp]: "v\<in>V \<Longrightarrow> v<N" using V_ss by auto
  
  lemma inEIE_lessN[simp]: "e\<in>E \<or> e\<in>E\<inverse> \<Longrightarrow> case e of (u,v) \<Rightarrow> u<N \<and> v<N"    
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

  lemma c_hnr[sepref_fr_rules]: 
    "(uncurry0 (return c),uncurry0 (RETURN c))
      \<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
    by (sepref_to_hoare) sep_auto 
    
  abbreviation cap_assn :: "capacity_impl \<Rightarrow> _" where "cap_assn \<equiv> id_assn"  
  abbreviation "edge_assn \<equiv> nat_assn \<times>\<^sub>a nat_assn"  
  abbreviation (input) "node_assn \<equiv> nat_assn"  
  
end --\<open>Network Impl. Locale\<close>
  
subsection \<open>Basic Operations\<close>  
text \<open>We explicitly define the basic operations of the algorithm\<close>  
  
context Network_Impl 
begin  
  subsubsection \<open>Residual Graph\<close>
  text \<open>Get the residual capacity of an edge.\<close>  
  definition cf_get :: "flow_impl \<Rightarrow> edge \<Rightarrow> capacity_impl nres" 
    where "cf_get cf e \<equiv> do {
      assert (e\<in>E \<union> E\<inverse>);
      return (cf e)
    }"  
    
  text \<open>Update the residual capacity of an edge.\<close>    
  definition cf_set :: "flow_impl \<Rightarrow> edge \<Rightarrow> capacity_impl \<Rightarrow> flow_impl nres" 
    where "cf_set cf e x \<equiv> do {
      assert (e\<in>E \<union> E\<inverse>);
      return (cf (e:=x))
    }"  
  
  text \<open>Obtain the initial residual graph.\<close>    
  definition cf_init :: "flow_impl nres" 
    where "cf_init \<equiv> return (op_mtx_new c)"
  
  subsubsection \<open>Excess Map\<close>    
  text \<open>Obtain an excess map with all nodes mapped to zero.\<close>  
  definition x_init :: "excess_impl nres" where "x_init \<equiv> return (\<lambda>_. 0)"
  text \<open>Get the excess of a node.\<close>  
  definition x_get :: "excess_impl \<Rightarrow> node \<Rightarrow> capacity_impl nres" 
    where "x_get x u \<equiv> do {
      assert (u\<in>V);
      return (x u)
    }"
  text \<open>Add a capacity to the excess of a node.\<close>    
  definition x_add :: "excess_impl \<Rightarrow> node \<Rightarrow> capacity_impl \<Rightarrow> excess_impl nres"  
    where "x_add x u \<Delta> \<equiv> do {
      assert (u\<in>V);
      return (x(u := x u + \<Delta>))
    }"
  
  subsubsection \<open>Adjacency Map\<close>
  text \<open>Obtain the list of adjacent nodes for a specified node.\<close>  
  definition am_get :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> node list nres"    
    where "am_get am u \<equiv> do {
      assert (u\<in>V);
      return (am u)
    }"
      
  text \<open>Test whether a node identifier is actually a node. 
    As not all numbers in the range @{term \<open>{0..<N}\<close>} must identify nodes, 
    this function uses the adjacency map to check whether there are adjacent
    edges. Due to the network constraints, all nodes have adjacent edges.
  \<close>    
  definition am_is_in_V :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> bool nres"
    where "am_is_in_V am u \<equiv> do {
      return (am u \<noteq> [])
    }"
  
  lemma am_is_in_V_correct[THEN order_trans, refine_vcg]: 
    assumes "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
    shows "am_is_in_V am u \<le> (spec x. x \<longleftrightarrow> u\<in>V)"
  proof -
    have "u\<in>V \<longleftrightarrow> adjacent_nodes u \<noteq> {}" 
      unfolding V_def adjacent_nodes_def by auto
    also have "\<dots> \<longleftrightarrow> am u \<noteq> []" 
      using fun_relD[OF assms IdI[of u]] 
      by (auto simp: list_set_rel_def in_br_conv)
    finally show ?thesis unfolding am_is_in_V_def by refine_vcg auto
  qed    
    
      
  subsubsection \<open>Labeling\<close>
  text \<open>Obtain the initial labeling: All nodes are zero, except the 
    source which is labeled by \<open>|V|\<close>. The exact cardinality of \<open>V\<close> is passed
    as a parameter.
  \<close>  
  definition l_init :: "nat \<Rightarrow> (node \<Rightarrow> nat) nres"
    where "l_init C \<equiv> return ((\<lambda>_. 0)(s := C))"

  text \<open>Get the label of a node.\<close>    
  definition l_get :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat nres"    
    where "l_get l u \<equiv> do {
      assert (u \<in> V);
      return (l u)
    }"
  
  text \<open>Set the label of a node.\<close>    
  definition l_set :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> (node \<Rightarrow> nat) nres"    
    where "l_set l u a \<equiv> do {
      assert (u\<in>V);
      assert (a < 2*card V);
      return (l(u := a))
    }"

  subsubsection \<open>Queue\<close>    
  text \<open>Obtain the empty queue.\<close>  
  definition q_empty :: "node list nres" where
    "q_empty \<equiv> return []"
  
  text \<open>Check whether a queue is empty.\<close>  
  definition q_is_empty :: "node list \<Rightarrow> bool nres" where
    "q_is_empty Q \<equiv> return ( Q = [] )"
    
  text \<open>Enqueue a node.\<close>  
  definition q_enqueue :: "node \<Rightarrow> node list \<Rightarrow> node list nres" where
    "q_enqueue v Q \<equiv> do {
      assert (v\<in>V);
      return (Q@[v])
    }"

  text \<open>Dequeue a node.\<close>  
  definition q_dequeue :: "node list \<Rightarrow> (node \<times> node list) nres" where
    "q_dequeue Q \<equiv> do {
      assert (Q\<noteq>[]);
      return (hd Q, tl Q)
    }"
    
  subsubsection \<open>Label Frequency Counts\<close>
  text \<open>Obtain the frequency counts for the initial labeling.
    Again, the cardinality of \<open>|V|\<close>, which is required to determine the label
    of the source node, is passed as an explicit parameter.
  \<close>  
  definition cnt_init :: "nat \<Rightarrow> (nat \<Rightarrow> nat) nres"
    where "cnt_init C \<equiv> do {
      assert (C<2*N);
      return ((\<lambda>_. 0)(0 := C - 1, C := 1))
    }"

  text \<open>Get the count for a label value.\<close>    
  definition cnt_get :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat nres"    
    where "cnt_get cnt lv \<equiv> do {
      assert (lv < 2*N);
      return (cnt lv)
    }"
  
  text \<open>Increment the count for a label value by one.\<close>    
  definition cnt_incr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) nres"    
    where "cnt_incr cnt lv \<equiv> do {
      assert (lv < 2*N);
      return (cnt ( lv := cnt lv + 1 ))
    }"

  text \<open>Decrement the count for a label value by one.\<close>    
  definition cnt_decr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) nres"    
    where "cnt_decr cnt lv \<equiv> do {
      assert (lv < 2*N \<and> cnt lv > 0);
      return (cnt ( lv := cnt lv - 1 ))
    }"
    
end --\<open>Network Impl. Locale\<close>

subsection \<open>Refinements to Basic Operations\<close>  
  
context Network_Impl 
begin  
text \<open>In this section, we refine the algorithm to actually use the 
 basic operations.
\<close>
  
subsubsection \<open>Explicit Computation of the Excess\<close>  
definition "xf_rel \<equiv> { ((excess f,cf_of f),f) | f. True }"
lemma xf_rel_RELATES[refine_dref_RELATES]: "RELATES xf_rel" 
  by (auto simp: RELATES_def)
  
definition "pp_init_x 
  \<equiv> \<lambda>u. (if u=s then (\<Sum>(u,v)\<in>outgoing s. - c(u,v)) else c (s,u))"
  
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
      have [simp]: 
        "(case e of (u, v) \<Rightarrow> if u = s then c (u, v) else 0) = 0" 
        if "e\<in>outgoing u" for e
        using that by (auto simp: outgoing_def)
      have [simp]: "(case e of (u, v) \<Rightarrow> if u = s then c (u, v) else 0) 
        = (if e = (s,u) then c (s,u) else 0)" 
        if "e\<in>incoming u" for e
        using that by (auto simp: incoming_def split: if_splits)
      show ?thesis by (simp add: sum.delta) (simp add: incoming_def)
    qed 
    done  
  done  
    
definition "pp_init_cf 
  \<equiv> \<lambda>(u,v). if (v=s) then c (v,u) else if u=s then 0 else c (u,v)"
lemma cf_of_pp_init_f[simp]: "cf_of pp_init_f = pp_init_cf"
  apply (intro ext)  
  unfolding pp_init_cf_def pp_init_f_def residualGraph_def
  using no_parallel_edge  
  by auto  
    
  
lemma pp_init_x_rel: "((pp_init_x, pp_init_cf), pp_init_f) \<in> xf_rel"
  unfolding xf_rel_def by auto

subsubsection \<open>Algorithm to Compute Initial Excess and Flow\<close>    
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
      \<and> (\<forall>v\<in>adjacent_nodes s. 
            if v\<notin>it then cf (s,v) = 0 \<and> cf (v,s) = c (s,v) 
            else cf (s,v) = c (s,v) \<and> cf (v,s) = c (v,s))
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
  
subsubsection \<open>Computing the Minimal Adjacent Label\<close>  
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
    

lemma (in -) set_filter_xform_aux: 
  "{ f x | x. ( x = a \<or> x\<in>S \<and> x\<notin>it ) \<and> P x } 
  = (if P a then {f a} else {}) \<union> {f x | x. x\<in>S-it \<and> P x}"    
  by auto
    
lemma (in Labeling) min_adj_label_aux_spec: 
  assumes PRE: "relabel_precond f l u"
  shows "min_adj_label_aux cf l u \<le> SPEC (\<lambda>x. x = Min { l v | v. (u,v)\<in>cf.E })"
proof -
  have AUX: "cf (u,v) \<noteq> 0 \<longleftrightarrow> (u,v)\<in>cf.E" for v unfolding cf.E_def by auto
  
  have EQ: "{ l v | v. (u,v)\<in>cf.E } 
    = { l v | v. v\<in>adjacent_nodes u \<and> cf (u,v)\<noteq>0 }"
    unfolding AUX
    using cfE_ss_invE
    by (auto simp: adjacent_nodes_def)
  
  define Min_option :: "nat set \<rightharpoonup> nat" 
    where "Min_option X \<equiv> if X={} then None else Some (Min X)" for X
      
  from PRE active_has_cf_outgoing have "cf.outgoing u \<noteq> {}" 
    unfolding relabel_precond_def by auto
  hence [simp]: "u\<in>V" unfolding cf.outgoing_def using cfE_of_ss_VxV by auto
  from \<open>cf.outgoing u \<noteq> {}\<close> 
  have AUX2: "\<exists>v. v \<in> adjacent_nodes u \<and> cf (u, v) \<noteq> 0"
    by (smt AUX Collect_empty_eq Image_singleton_iff UnCI adjacent_nodes_def 
            cf.outgoing_def cf_def converse_iff prod.simps(2))
      
  show ?thesis unfolding min_adj_label_aux_def EQ   
    apply (refine_vcg 
        FOREACH_rule[where 
          I="\<lambda>it x. x = Min_option 
                          { l v | v. v\<in>adjacent_nodes u - it \<and> cf (u,v)\<noteq>0 }"]
        )  
    apply (vc_solve 
        simp: Min_option_def it_step_insert_iff set_filter_xform_aux 
        split: if_splits)
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
  assumes "Height_Bounded_Labeling c s t f l"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes PRE: "relabel_precond f l u"
  assumes [simp]: "cf = cf_of f"  
  shows "min_adj_label am cf l u \<le> SPEC (\<lambda>x. x 
        = Min { l v | v. (u,v)\<in>cfE_of f })"  
proof - 
  interpret Height_Bounded_Labeling c s t f l by fact

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
  
subsubsection \<open>Adding frequency counters to labeling\<close>
      
definition "l_invar l \<equiv> \<forall>v. l v \<noteq> 0 \<longrightarrow> v\<in>V"  

definition "clc_invar \<equiv> \<lambda>(cnt,l). 
  (\<forall>lv. cnt lv = card { u\<in>V . l u = lv }) 
\<and> (\<forall>u. l u < 2*N) \<and> l_invar l"
definition "clc_rel \<equiv> br snd clc_invar"    
    
definition "clc_init C \<equiv> do {
  l \<leftarrow> l_init C;
  cnt \<leftarrow> cnt_init C;
  return (cnt,l)
}"
  
definition "clc_get \<equiv> \<lambda>(cnt,l) u. l_get l u"
definition "clc_set \<equiv> \<lambda>(cnt,l) u a. do {
  assert (a<2*N);
  lu \<leftarrow> l_get l u;
  cnt \<leftarrow> cnt_decr cnt lu;
  l \<leftarrow> l_set l u a;
  lu \<leftarrow> l_get l u;
  cnt \<leftarrow> cnt_incr cnt lu;
  return (cnt,l)
}"  

definition "clc_has_gap \<equiv> \<lambda>(cnt,l) lu. do {
  nlu \<leftarrow> cnt_get cnt lu;
  return (nlu = 0)
}"
    
lemma cardV_le_N: "card V \<le> N" using card_mono[OF _ V_ss] by auto
lemma N_not_Z: "N \<noteq> 0" using card_V_ge2 cardV_le_N by auto
lemma N_ge_2: "2\<le>N" using card_V_ge2 cardV_le_N by auto
  
lemma clc_init_refine[refine]:
  assumes [simplified,simp]: "(Ci,C)\<in>nat_rel" 
  assumes [simp]: "C = card V" 
  shows "clc_init Ci \<le>\<Down>clc_rel (l_init C)"  
proof -
  have AUX: "{u. u \<noteq> s \<and> u \<in> V} = V-{s}" by auto
  
  show ?thesis
    unfolding clc_init_def l_init_def cnt_init_def
    apply refine_vcg
    unfolding clc_rel_def clc_invar_def
    using cardV_le_N N_not_Z
    by (auto simp: in_br_conv V_not_empty AUX l_invar_def)  
qed  

lemma clc_get_refine[refine]: 
  "\<lbrakk> (clc,l)\<in>clc_rel; (ui,u)\<in>nat_rel \<rbrakk> \<Longrightarrow> clc_get clc ui \<le>\<Down>Id (l_get l u)"
  unfolding clc_get_def clc_rel_def
  by (auto simp: in_br_conv split: prod.split)  

definition l_get_rlx :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat nres"    
  where "l_get_rlx l u \<equiv> do {
    assert (u < N);
    return (l u)
  }"
definition "clc_get_rlx \<equiv> \<lambda>(cnt,l) u. l_get_rlx l u"
  
lemma clc_get_rlx_refine[refine]: 
  "\<lbrakk> (clc,l)\<in>clc_rel; (ui,u)\<in>nat_rel \<rbrakk> 
  \<Longrightarrow> clc_get_rlx clc ui \<le>\<Down>Id (l_get_rlx l u)"
  unfolding clc_get_rlx_def clc_rel_def
  by (auto simp: in_br_conv split: prod.split)  
    
lemma card_insert_disjointI: 
  "\<lbrakk> finite Y; X = insert x Y; x\<notin>Y \<rbrakk> \<Longrightarrow> card X = Suc (card Y)"    
  by auto
  
lemma clc_set_refine[refine]:
  "\<lbrakk> (clc,l) \<in> clc_rel; (ui,u)\<in>nat_rel; (ai,a)\<in>nat_rel \<rbrakk> \<Longrightarrow>
    clc_set clc ui ai \<le>\<Down>clc_rel (l_set l u a)"
  unfolding clc_set_def l_set_def l_get_def cnt_decr_def cnt_incr_def
  apply refine_vcg  
  apply vc_solve
  unfolding clc_rel_def in_br_conv clc_invar_def l_invar_def
  subgoal using cardV_le_N by auto
  applyS auto  
  applyS (auto simp: simp: card_gt_0_iff)
    
  subgoal for cnt ll 
    apply clarsimp  
    apply (intro impI conjI; clarsimp?)
    subgoal  
      apply (subst le_imp_diff_is_add; simp)
      apply (rule card_insert_disjointI[where x=u])
      by auto
    subgoal     
      apply (rule card_insert_disjointI[where x=u, symmetric])
      by auto
    subgoal
      by (auto intro!: arg_cong[where f=card])
    done
  done    

lemma clc_has_gap_correct[THEN order_trans, refine_vcg]:
  "\<lbrakk>(clc,l)\<in>clc_rel; k<2*N\<rbrakk> 
  \<Longrightarrow> clc_has_gap clc k \<le> (spec r. r \<longleftrightarrow> gap_precond l k)"
  unfolding clc_has_gap_def cnt_get_def gap_precond_def
  apply refine_vcg  
  unfolding clc_rel_def clc_invar_def in_br_conv
  by auto  
  

subsubsection \<open>Refinement of Push\<close>  
definition "fifo_push2_aux x cf Q \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  assert ( u \<noteq> v );
  let \<Delta> = min (x u) (cf (u,v));
  let Q = (if v\<noteq>s \<and> v\<noteq>t \<and> x v = 0 then Q@[v] else Q);
  return ((x( u := x u - \<Delta>, v := x v + \<Delta> ),augment_edge_cf cf (u,v) \<Delta>),Q)
}"
    
  
lemma fifo_push2_aux_refine: 
  "\<lbrakk>((x,cf),f)\<in>xf_rel; (ei,e)\<in>Id\<times>\<^sub>rId; (Qi,Q)\<in>Id\<rbrakk> 
    \<Longrightarrow> fifo_push2_aux x cf Qi ei \<le> \<Down>(xf_rel \<times>\<^sub>r Id) (fifo_push f l Q e)"
  unfolding fifo_push_def fifo_push2_aux_def
  apply refine_vcg  
  apply (vc_solve simp: xf_rel_def no_self_loop)
  subgoal for u v 
    unfolding push_precond_def using cfE_of_ss_invE by auto
  subgoal for u v 
  proof -
    assume [simp]: "Labeling c s t f l"
    then interpret Labeling c s t f l .
        thm cfE_ss_invE
    assume "push_precond f l (u, v)"    
    then interpret l': push_effect_locale c s t f l u v by unfold_locales
    show ?thesis 
      apply (safe intro!: ext)
      using l'.excess'_if l'.\<Delta>_def l'.cf'_alt \<open>u\<noteq>v\<close>
      by (auto)  
  qed
  done  

definition "fifo_push2 x cf Q \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  xu \<leftarrow> x_get x u;
  xv \<leftarrow> x_get x v;
  cfuv \<leftarrow> cf_get cf (u,v);
  cfvu \<leftarrow> cf_get cf (v,u);
  let \<Delta> = min xu cfuv;
  x \<leftarrow> x_add x u (-\<Delta>);
  x \<leftarrow> x_add x v \<Delta>;

  cf \<leftarrow> cf_set cf (u,v) (cfuv - \<Delta>);
  cf \<leftarrow> cf_set cf (v,u) (cfvu + \<Delta>);

  if v\<noteq>s \<and> v\<noteq>t \<and> xv = 0 then do {
    Q \<leftarrow> q_enqueue v Q;
    return ((x,cf),Q)
  } else
    return ((x,cf),Q)
}"
    
lemma fifo_push2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel" "(ei,e)\<in>Id\<times>\<^sub>rId" "(Qi,Q)\<in>Id"
  shows "fifo_push2 x cf Qi ei \<le> \<Down>(xf_rel \<times>\<^sub>r Id) (fifo_push f l Q e)"
proof -
  have "fifo_push2 x cf Qi ei \<le> (fifo_push2_aux x cf Qi ei)"  
    unfolding fifo_push2_def fifo_push2_aux_def
    unfolding x_get_def x_add_def cf_get_def cf_set_def q_enqueue_def
    unfolding augment_edge_cf_def  
    apply (simp only: nres_monad_laws)  
    apply refine_vcg  
    using E_ss_VxV  
    by auto  
  also note fifo_push2_aux_refine[OF assms]    
  finally show ?thesis . 
qed  
  
subsubsection \<open>Refinement of Gap-Relabel\<close>    
definition "gap_aux C l k \<equiv> do {
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v l. do {
    lv \<leftarrow> l_get_rlx l v;
    if (k < lv \<and> lv < C) then do {
      assert (C+1 < 2*N);
      l \<leftarrow> l_set l v (C+1);
      return l
    } else return l
  }) l
}"
  
lemma gap_effect_invar[simp]: "l_invar l \<Longrightarrow> l_invar (gap_effect l k)"   
  unfolding gap_effect_def l_invar_def
  by auto  
  
lemma relabel_effect_invar[simp]: "\<lbrakk>l_invar l; u\<in>V\<rbrakk> \<Longrightarrow> l_invar (relabel_effect f l u)"    
  unfolding relabel_effect_def l_invar_def by auto
    
lemma gap_aux_correct[THEN order_trans, refine_vcg]: 
  "\<lbrakk>l_invar l; C=card V\<rbrakk> \<Longrightarrow> gap_aux C l k \<le> SPEC (\<lambda>r. r=gap_effect l k)"
  unfolding gap_aux_def l_get_rlx_def l_set_def
  apply (simp only: nres_monad_laws)  
  apply (refine_vcg nfoldli_rule[where I = "\<lambda>it1 it2 l'. \<forall>u. if u\<in>set it2 then l' u = l u else l' u = gap_effect l k u"])
  apply (vc_solve simp: upt_eq_lel_conv)
  subgoal
    apply (frule gap_effect_invar[where k=k])
    unfolding l_invar_def using V_ss by force 
  subgoal using N_not_Z cardV_le_N by auto
  subgoal unfolding l_invar_def by auto  
  subgoal unfolding gap_effect_def by auto
  subgoal for v l' u
    apply (drule spec[where x=u])
    by (auto split: if_splits simp: gap_effect_def)
  subgoal by auto
  done  
  
definition "relabel f l u \<equiv> do {
  assert (Height_Bounded_Labeling c s t f l);
  assert (relabel_precond f l u);
  assert (u\<in>V-{s,t});
  return (relabel_effect f l u)
}"
    
definition "fifo_gap_relabel_aux C f l Q u \<equiv> do {
  Q \<leftarrow> q_enqueue u Q;
  lu \<leftarrow> l_get l u;
  l \<leftarrow> relabel f l u;
  if gap_precond l lu then do {
    l \<leftarrow> gap_aux C l lu;
    return (l,Q)
  } else return (l,Q)
}"  

lemma fifo_gap_relabel_aux_refine: 
  assumes [simp]: "C = card V" "l_invar l"
  shows "fifo_gap_relabel_aux C f l Q u \<le> fifo_gap_relabel f l Q u"  
  unfolding fifo_gap_relabel_aux_def fifo_gap_relabel_def relabel_def 
    gap_relabel_effect_def l_get_def q_enqueue_def
  apply (simp only: Let_def nres_monad_laws)  
  apply refine_vcg  
  by auto  
  
definition "gap2 C clc k \<equiv> do {
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v clc. do {
    lv \<leftarrow> clc_get_rlx clc v;
    if (k < lv \<and> lv < C) then do {
      clc \<leftarrow> clc_set clc v (C+1);
      return clc
    } else return clc
  }) clc
}"
    
lemma gap2_refine[refine]:  
  assumes [simplified,simp]: "(Ci,C)\<in>nat_rel" "(ki,k)\<in>nat_rel"
  assumes CLC: "(clc,l)\<in>clc_rel"  
  shows "gap2 Ci clc ki \<le>\<Down>clc_rel (gap_aux C l k)"
  unfolding gap2_def gap_aux_def  
  apply (refine_rcg CLC)
  apply refine_dref_type  
  by auto    
    
definition "min_adj_label_clc am cf clc u \<equiv> case clc of (_,l) \<Rightarrow> min_adj_label am cf l u"
    
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
    apply (vc_solve (nopre) simp: xf_rel_def relabel_effect_def solve: asm_rl)
    subgoal premises prems for a proof -   
      from prems interpret Height_Bounded_Labeling c s t f l by simp
      interpret l': Height_Bounded_Labeling c s t f "relabel_effect f l u"
        by (rule relabel_pres_height_bound) (rule prems)
      from prems have "u\<in>V" by simp
      from prems have "a + 1 = relabel_effect f l u u"
        by (auto simp: relabel_effect_def)
      also note l'.height_bound[THEN bspec, OF \<open>u\<in>V\<close>]
      finally show "a + 1 < 2 * card V" using card_V_ge2 by auto
    qed      
    done
qed
  
  
definition "fifo_relabel2 am cf clc u \<equiv> do {
  assert (u\<in>V - {s,t});
  nl \<leftarrow> min_adj_label_clc am cf clc u;
  clc \<leftarrow> clc_set clc u (nl+1);
  return clc
}"
    
lemma fifo_relabel2_refine[refine]: 
  assumes XF: "((x,cf),f)\<in>xf_rel"
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(ui,u)\<in>Id"
  shows "fifo_relabel2 am cf clc ui \<le> \<Down>clc_rel (relabel f l u)"    
proof -
  have "fifo_relabel2 am cf clc ui \<le>\<Down>clc_rel (relabel2 am cf l ui)"
    unfolding fifo_relabel2_def relabel2_def
    apply (refine_rcg)
    apply (refine_dref_type)  
    apply (vc_solve simp: CLC)
    subgoal 
      using CLC 
      unfolding clc_rel_def in_br_conv min_adj_label_clc_def 
      by (auto split: prod.split)
    done    
  also note relabel2_refine[OF XF AM, of l l ui u]
  finally show ?thesis by simp  
qed  
  
  
    
definition "fifo_gap_relabel2 C am cf clc Q u \<equiv> do {
  Q \<leftarrow> q_enqueue u Q;
  lu \<leftarrow> clc_get clc u;
  clc \<leftarrow> fifo_relabel2 am cf clc u;
  has_gap \<leftarrow> clc_has_gap clc lu;
  if has_gap then do {
    clc \<leftarrow> gap2 C clc lu;
    RETURN (clc,Q)
  } else 
    RETURN (clc,Q)
}"  
  
lemma fifo_gap_relabel2_refine_aux:
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(Ci,C)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  shows "fifo_gap_relabel2 Ci am cf clc Qi ui \<le> \<Down>(clc_rel \<times>\<^sub>r Id) (fifo_gap_relabel_aux C f l Q u)"  
  unfolding fifo_gap_relabel2_def fifo_gap_relabel_aux_def
  apply (refine_vcg XCF AM CLC if_bind_cond_refine bind_refine')
  apply refine_dref_type  
  apply (vc_solve solve: refl )
  subgoal for _ lu
    using CLC
    unfolding clc_get_def l_get_def clc_rel_def in_br_conv clc_invar_def
    by (auto simp: refine_pw_simps split: prod.splits)
  done    
    
lemma fifo_gap_relabel2_refine[refine]:
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"    
  assumes CC: "C = card V"  
  shows "fifo_gap_relabel2 C am cf clc Qi ui \<le>\<Down>(clc_rel \<times>\<^sub>r Id) (fifo_gap_relabel f l Q u)"
proof -
  from CLC have LINV: "l_invar l" unfolding clc_rel_def in_br_conv clc_invar_def by auto
  
  note fifo_gap_relabel2_refine_aux[OF XCF CLC AM IdI IdI IdI]
  also note fifo_gap_relabel_aux_refine[OF CC LINV]  
  finally show ?thesis by simp  
qed    
  
subsubsection \<open>Refinement of Discharge\<close>
context begin  
text \<open>
  Some lengthy, multi-step refinement of discharge, 
  changing the iteration to iteration over adjacent nodes with filter,
  and showing that we can do the filter wrt.\ the current state, rather than 
  the original state before the loop. 
\<close>  
  
lemma am_nodes_as_filter:
  assumes "is_adj_map am"
  shows "{v . (u,v)\<in>cfE_of f} = set (filter (\<lambda>v. cf_of f (u,v) \<noteq> 0) (am u))"
  using assms cfE_of_ss_invE 
  unfolding is_adj_map_def Graph.E_def
  by fastforce 
      
private lemma adjacent_nodes_iterate_refine1:   
  fixes ff u f
  assumes AMR: "(am,adjacent_nodes)\<in>Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  assumes CR: "\<And>s si. (si,s)\<in>Id \<Longrightarrow> cci si \<longleftrightarrow> cc s"  
  assumes FR: "\<And>v vi s si. \<lbrakk>(vi,v)\<in>Id; v\<in>V; (u,v)\<in>E\<union>E\<inverse>; (si,s)\<in>Id\<rbrakk> \<Longrightarrow> 
    ffi vi si \<le> \<Down>Id (do {
                      if (cf_of f (u,v) \<noteq> 0) then ff v s else RETURN s
                    })" (is "\<And>v vi s si. \<lbrakk>_;_;_;_\<rbrakk> \<Longrightarrow> _  \<le> \<Down>_ (?ff' v s)")
  assumes S0R: "(s0i,s0)\<in>Id"
  assumes UR: "(ui,u)\<in>Id"  
  shows "nfoldli (am ui) cci ffi s0i \<le>\<Down>Id (FOREACHc {v . (u,v)\<in>cfE_of f} cc ff s0)"
proof -
  from fun_relD[OF AMR] have AM: "is_adj_map am"
    unfolding is_adj_map_def
    by (auto simp: list_set_rel_def in_br_conv adjacent_nodes_def)  
  
  from AM have AM_SS_V: "set (am u) \<subseteq> V" "{u}\<times>set (am u) \<subseteq> E \<union> E\<inverse>"
    unfolding is_adj_map_def using E_ss_VxV by auto
      
  thm nfoldli_refine    
  have "nfoldli (am ui) cci ffi s0 \<le> \<Down>Id (nfoldli (am ui) cc ?ff' s0)"    
    apply (refine_vcg FR) 
    apply (rule list_rel_congD)  
    apply refine_dref_type 
    using CR  
    apply vc_solve
    using AM_SS_V UR by auto  
  also have "nfoldli (am ui) cc ?ff' s0 \<le>\<Down>Id (FOREACHc (adjacent_nodes u) cc ?ff' s0)"    
    by (rule LFOc_refine[OF fun_relD[OF AMR UR]]; simp)
  also have "FOREACHc (adjacent_nodes u) cc ?ff' s0 \<le> FOREACHc {v . (u,v)\<in>cfE_of f} cc ff s0"
    apply (subst am_nodes_as_filter[OF AM])  
    apply (subst FOREACHc_filter_deforestation2)  
    subgoal using AM unfolding is_adj_map_def by auto
    subgoal 
      apply (rule eq_refl) 
      apply ((fo_rule cong)+; (rule refl)?)
      subgoal using fun_relD[OF AMR IdI[of u]] by (auto simp: list_set_rel_def in_br_conv) 
      done    
    done
  finally show ?thesis using S0R by simp
qed    
    
private definition "dis_loop_aux am f\<^sub>0 l Q u \<equiv> do {
  assert (u\<in>V - {s,t});
  assert (distinct (am u));
  nfoldli (am u) (\<lambda>(f,l,Q). excess f u \<noteq> 0) (\<lambda>v (f,l,Q). do {
    assert ((u,v)\<in>E\<union>E\<inverse> \<and> v\<in>V);
    if (cf_of f\<^sub>0 (u,v) \<noteq> 0) then do {
      if (l u = l v + 1) then do {
        (f',Q) \<leftarrow> fifo_push f l Q (u,v);
        assert (\<forall>v'. v'\<noteq>v \<longrightarrow> cf_of f' (u,v') = cf_of f (u,v'));
        return (f',l,Q)
      } else return (f,l,Q)
    } else return (f,l,Q)
  }) (f\<^sub>0,l,Q)
}"
    
private definition "fifo_discharge_aux am f\<^sub>0 l Q \<equiv> do {  
  (u,Q) \<leftarrow> q_dequeue Q;
  assert (u\<in>V \<and> u\<noteq>s \<and> u\<noteq>t);

  (f,l,Q) \<leftarrow> dis_loop_aux am f\<^sub>0 l Q u;

  if excess f u \<noteq> 0 then do {
    (l,Q) \<leftarrow> fifo_gap_relabel f l Q u;
    return (f,l,Q)
  } else do {
    return (f,l,Q)
  }
}"
    
private lemma fifo_discharge_aux_refine:  
  assumes AM: "(am,adjacent_nodes)\<in>Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  assumes [simplified,simp]: "(fi,f)\<in>Id" "(li,l)\<in>Id" "(Qi,Q)\<in>Id"
  shows "fifo_discharge_aux am fi li Qi \<le> \<Down>Id (fifo_discharge f l Q)"
  unfolding fifo_discharge_aux_def fifo_discharge_def dis_loop_aux_def 
  unfolding q_dequeue_def  
  apply (simp only: nres_monad_laws)  
  apply (refine_rcg adjacent_nodes_iterate_refine1[OF AM])  
  apply refine_dref_type
  apply vc_solve  
  subgoal 
    using fun_relD[OF AM IdI[of "hd Q"]]  
    unfolding list_set_rel_def by (auto simp: in_br_conv)
  done  
    
private definition "dis_loop_aux2 am f\<^sub>0 l Q u \<equiv> do {
  assert (u\<in>V - {s,t});
  assert (distinct (am u));
  nfoldli (am u) (\<lambda>(f,l,Q). excess f u \<noteq> 0) (\<lambda>v (f,l,Q). do {
    assert ((u,v)\<in>E\<union>E\<inverse> \<and> v\<in>V);
    if (cf_of f (u,v) \<noteq> 0) then do {
      if (l u = l v + 1) then do {
        (f',Q) \<leftarrow> fifo_push f l Q (u,v);
        assert (\<forall>v'. v'\<noteq>v \<longrightarrow> cf_of f' (u,v') = cf_of f (u,v'));
        return (f',l,Q)
      } else return (f,l,Q)
    } else return (f,l,Q)
  }) (f\<^sub>0,l,Q)
}"
    
private lemma dis_loop_aux2_refine:
  shows "dis_loop_aux2 am f\<^sub>0 l Q u \<le>\<Down>Id (dis_loop_aux am f\<^sub>0 l Q u)"  
  unfolding dis_loop_aux2_def dis_loop_aux_def
  apply (intro ASSERT_refine_right ASSERT_refine_left; assumption?)  
  apply (rule nfoldli_invar_refine[where I="\<lambda>it1 it2 (f,_,_). \<forall>v\<in>set it2. cf_of f (u,v) = cf_of f\<^sub>0 (u,v)"])
  apply refine_dref_type  
  apply vc_solve
  apply (auto simp: pw_leof_iff refine_pw_simps fifo_push_def; metis) 
  done  
    
private definition "dis_loop_aux3 am x cf l Q u \<equiv> do {
  assert (u\<in>V \<and> distinct (am u));
  monadic_nfoldli (am u) 
    (\<lambda>((x,cf),l,Q). do { xu \<leftarrow> x_get x u; return (xu \<noteq> 0) }) 
    (\<lambda>v ((x,cf),l,Q). do {
      cfuv \<leftarrow> cf_get cf (u,v);
      if (cfuv \<noteq> 0) then do {
        lu \<leftarrow> l_get l u;
        lv \<leftarrow> l_get l v;
        if (lu = lv + 1) then do {
          ((x,cf),Q) \<leftarrow> fifo_push2 x cf Q (u,v);
          return ((x,cf),l,Q)
        } else return ((x,cf),l,Q)
      } else return ((x,cf),l,Q)
  }) ((x,cf),l,Q)
}"
    
private lemma dis_loop_aux3_refine:
  assumes [simplified,simp]: "(ami,am)\<in>Id" "(li,l)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  assumes XF: "((x,cf),f)\<in>xf_rel"
  shows "dis_loop_aux3 ami x cf li Qi ui \<le>\<Down>(xf_rel \<times>\<^sub>r Id \<times>\<^sub>r Id) (dis_loop_aux2 am f l Q u)"  
  unfolding dis_loop_aux3_def dis_loop_aux2_def
  unfolding x_get_def cf_get_def l_get_def  
  apply (simp only: nres_monad_laws nfoldli_to_monadic)  
  apply (refine_rcg)
  apply refine_dref_type  
  using XF  
  by (vc_solve simp: xf_rel_def in_br_conv)
    
definition "dis_loop2 am x cf clc Q u \<equiv> do {
  assert (distinct (am u));
  amu \<leftarrow> am_get am u;
  monadic_nfoldli amu
    (\<lambda>((x,cf),clc,Q). do { xu \<leftarrow> x_get x u; return (xu \<noteq> 0) }) 
    (\<lambda>v ((x,cf),clc,Q). do {
      cfuv \<leftarrow> cf_get cf (u,v);
      if (cfuv \<noteq> 0) then do {
        lu \<leftarrow> clc_get clc u;
        lv \<leftarrow> clc_get clc v;
        if (lu = lv + 1) then do {
          ((x,cf),Q) \<leftarrow> fifo_push2 x cf Q (u,v);
          return ((x,cf),clc,Q)
        } else return ((x,cf),clc,Q)
      } else return ((x,cf),clc,Q)
  }) ((x,cf),clc,Q)
}"
    
private lemma dis_loop2_refine_aux:
  assumes [simplified,simp]: "(xi,x)\<in>Id" "(cfi,cf)\<in>Id" "(ami,am)\<in>Id" "(li,l)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  assumes CLC: "(clc,l)\<in>clc_rel"
  shows "dis_loop2 ami xi cfi clc Qi ui \<le>\<Down>(Id \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (dis_loop_aux3 am x cf l Q u)"  
  unfolding dis_loop2_def dis_loop_aux3_def am_get_def
  apply (simp only: nres_monad_laws)  
  apply refine_rcg  
  apply refine_dref_type  
  apply (vc_solve simp: CLC)
  done
    
lemma dis_loop2_refine[refine]:
  assumes XF: "((x,cf),f)\<in>xf_rel"
  assumes CLC: "(clc,l)\<in>clc_rel"
  assumes [simplified,simp]: "(ami,am)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  shows "dis_loop2 ami x cf clc Qi ui \<le>\<Down>(xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (dis_loop_aux am f l Q u)"
proof -      
  have [simp]: "((Id \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) O (xf_rel \<times>\<^sub>r Id)) = xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id"
    by (auto simp: prod_rel_comp)
  
  note dis_loop2_refine_aux[OF IdI IdI IdI IdI IdI IdI CLC]
  also note dis_loop_aux3_refine[OF IdI IdI IdI IdI XF]
  also note dis_loop_aux2_refine  
  finally show ?thesis 
    by (auto simp: conc_fun_chain monoD[OF conc_fun_mono])
qed    
    
    
definition "fifo_discharge2 C am x cf clc Q \<equiv> do {  
  (u,Q) \<leftarrow> q_dequeue Q;
  assert (u\<in>V \<and> u\<noteq>s \<and> u\<noteq>t);

  ((x,cf),clc,Q) \<leftarrow> dis_loop2 am x cf clc Q u;

  xu \<leftarrow> x_get x u;
  if xu \<noteq> 0 then do {
    (clc,Q) \<leftarrow> fifo_gap_relabel2 C am cf clc Q u;
    return ((x,cf),clc,Q)
  } else do {
    return ((x,cf),clc,Q)
  }
}"
    
lemma fifo_discharge2_refine[refine]:
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes [simplified,simp]: "(Qi,Q)\<in>Id"  
  assumes CC: "C = card V"  
  shows "fifo_discharge2 C am x cf clc Qi \<le>\<Down>(xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (fifo_discharge f l Q)"
proof -
  have "fifo_discharge2 C am x cf clc Q \<le>\<Down>(xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (fifo_discharge_aux am f l Q)"
    unfolding fifo_discharge2_def fifo_discharge_aux_def  
    unfolding x_get_def  
    apply (simp only: nres_monad_laws)  
    apply (refine_rcg XCF CLC AM IdI)
    apply (vc_solve simp: CC) 
    subgoal unfolding xf_rel_def in_br_conv by auto  
    applyS assumption  
    done  
  also note fifo_discharge_aux_refine[OF AM IdI IdI IdI]
  finally show ?thesis by simp  
qed    
  
end -- \<open>Anonymous Context\<close>    

subsubsection \<open>Computing the Exact Number of Nodes\<close>  
definition "init_C am \<equiv> do {
  let cardV=0;
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v cardV. do {
    assert (v<N);
    inV \<leftarrow> am_is_in_V am v;
    if inV then do {
      return (cardV + 1)
    } else
      return cardV
  }) cardV
}"    

lemma init_C_correct:
  assumes AMR: "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"  
  shows "init_C am \<le> SPEC (\<lambda>C. C = card V)"
  unfolding init_C_def  
  apply (refine_vcg 
      nfoldli_rule[where I="\<lambda>l1 _ C. C = card (V\<inter>set l1)"]
      AMR
      )  
  apply clarsimp_all  
  using V_ss  
  apply (auto simp: upt_eq_lel_conv Int_absorb2)  
  done    
  
subsubsection \<open>Computing the Initial Queue\<close>  
definition "q_init am \<equiv> do {
  Q \<leftarrow> q_empty;
  ams \<leftarrow> am_get am s;
  nfoldli ams (\<lambda>_. True) (\<lambda>v Q. do {
    if v\<noteq>t then q_enqueue v Q else return Q
  }) Q
}"

lemma q_init_correct[THEN order_trans, refine_vcg]: 
  assumes AMR: "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"  
  shows "q_init am \<le> (spec l. distinct l \<and> set l = {v \<in> V - {s, t}. excess pp_init_f v \<noteq> 0})"  
proof -    
  from fun_relD[OF AMR IdI[of s]] have "set (am s) \<subseteq> V"
    using adjacent_nodes_ss_V
    by (auto simp: list_set_rel_def in_br_conv)
  hence "q_init am \<le> RETURN (filter (op \<noteq> t) (am s))"
    unfolding q_init_def q_empty_def q_enqueue_def am_get_def
    apply (refine_vcg nfoldli_rule[where I="\<lambda>l1 _ l. l = filter (op \<noteq> t) l1"])  
    by auto  
  also have "\<dots> \<le> (spec l. distinct l \<and> set l = {v \<in> V - {s, t}. excess pp_init_f v \<noteq> 0})"    
  proof -    
    from fun_relD[OF AMR IdI[of s]] have [simp]: "distinct (am s)" "set (am s) = adjacent_nodes s" 
      unfolding list_set_rel_def
      by (auto simp: in_br_conv)
    
    show ?thesis
      using E_ss_VxV
      apply (auto simp: pp_init_x_def adjacent_nodes_def)
      unfolding Graph.E_def by auto      
  qed
  finally show ?thesis .
qed    

subsubsection \<open>Refining the Main Algorithm\<close>  
definition "fifo_push_relabel_aux am \<equiv> do {
  cardV \<leftarrow> init_C am;
  assert (cardV = card V);
  let f = pp_init_f;
  l \<leftarrow> l_init cardV;

  Q \<leftarrow> q_init am;

  (f,l,_) \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>(f,l,Q). do {qe \<leftarrow> q_is_empty Q; return (\<not>qe)}) 
    (\<lambda>(f,l,Q). do {
      fifo_discharge f l Q
    }) 
    (f,l,Q);

  assert (Height_Bounded_Labeling c s t f l);
  return f
}"
  
lemma fifo_push_relabel_aux_refine:
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  shows "fifo_push_relabel_aux am \<le> \<Down>Id (fifo_push_relabel)"
  unfolding fifo_push_relabel_aux_def fifo_push_relabel_def
  unfolding l_init_def pp_init_l_def q_is_empty_def bind_to_let_conv
  apply (rule specify_left[OF init_C_correct[OF AM]])
  apply (refine_rcg q_init_correct[OF AM])
  apply refine_dref_type  
  apply vc_solve
  done    
    
  
definition "fifo_push_relabel2 am \<equiv> do {
  cardV \<leftarrow> init_C am;
  (x,cf) \<leftarrow> pp_init_xcf2 am;
  clc \<leftarrow> clc_init cardV;
  Q \<leftarrow> q_init am;

  ((x,cf),clc,Q) \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>((x,cf),clc,Q). do {qe \<leftarrow> q_is_empty Q; return (\<not>qe)}) 
    (\<lambda>((x,cf),clc,Q). do {
      fifo_discharge2 cardV am x cf clc Q
    }) 
    ((x,cf),clc,Q);

  return cf
}"

lemma fifo_push_relabel2_refine:
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  shows "fifo_push_relabel2 am \<le> \<Down>(br (flow_of_cf) (RPreGraph c s t)) fifo_push_relabel"
proof -
  {
    fix f l n
    assume "Height_Bounded_Labeling c s t f l"
    then interpret Height_Bounded_Labeling c s t f l .  
    have G1: "flow_of_cf cf = f" by (rule fo_rg_inv)
    have G2: "RPreGraph c s t cf" by (rule is_RPreGraph)
    note G1 G2    
  } note AUX1=this   
  
  
  have "fifo_push_relabel2 am \<le> \<Down>(br (flow_of_cf) (RPreGraph c s t)) (fifo_push_relabel_aux am)"
    unfolding fifo_push_relabel2_def fifo_push_relabel_aux_def
    apply (refine_rcg AM)  
    apply (refine_dref_type)      
    apply (vc_solve)   
    subgoal using AUX1 by (auto simp: in_br_conv xf_rel_def)
    done  
  also note fifo_push_relabel_aux_refine[OF AM]
  finally show ?thesis .  
qed      
  
end --\<open>Network Impl. Locale\<close>

subsection \<open>Separating out the Initialization of the Adjacency Matrix\<close>  
context Network_Impl
begin
  
text \<open>We split the algorithm into an initialization of the adjacency 
  matrix, and the actual algorithm. This way, the algorithm can handle 
  pre-initialized adjacency matrices.
\<close>  
 
definition "fifo_push_relabel_init2 \<equiv> cf_init"  
definition "pp_init_xcf2' am cf \<equiv> do {
  x \<leftarrow> x_init;

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
  
definition "fifo_push_relabel_run2 am cf \<equiv> do {
  cardV \<leftarrow> init_C am;
  (x,cf) \<leftarrow> pp_init_xcf2' am cf;
  clc \<leftarrow> clc_init cardV;
  Q \<leftarrow> q_init am;

  ((x,cf),clc,Q) \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>((x,cf),clc,Q). do {qe \<leftarrow> q_is_empty Q; return (\<not>qe)}) 
    (\<lambda>((x,cf),clc,Q). do {
      fifo_discharge2 cardV am x cf clc Q
    }) 
    ((x,cf),clc,Q);

  return cf
}"
  
lemma fifo_push_relabel2_alt:
  "fifo_push_relabel2 am = do {
    cf \<leftarrow> fifo_push_relabel_init2;
    fifo_push_relabel_run2 am cf
  }"  
  unfolding fifo_push_relabel_init2_def fifo_push_relabel_run2_def
    fifo_push_relabel2_def pp_init_xcf2_def pp_init_xcf2'_def
    cf_init_def (* Unfolding this b/c it's a return and thus can be inlined.*)
  by simp
  
  
  
end --\<open>Network Impl. Locale\<close>
  
subsection \<open>Refinement To Efficient Data Structures\<close>  
  
context Network_Impl
begin

subsubsection \<open>Residual Graph by Adjacency Matrix\<close>  
definition "cf_assn \<equiv> asmtx_assn N cap_assn"  
sepref_register cf_get cf_set cf_init 
sepref_thm cf_get_impl is "uncurry (PR_CONST cf_get)" 
  :: "cf_assn\<^sup>k *\<^sub>a edge_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn"  
  unfolding cf_get_def cf_assn_def PR_CONST_def
  by sepref
concrete_definition (in -) cf_get_impl 
  uses Network_Impl.cf_get_impl.refine_raw is "(uncurry ?f,_)\<in>_"
    
sepref_thm cf_set_impl is "uncurry2 (PR_CONST cf_set)" 
  :: "cf_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k *\<^sub>a cap_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn"  
  unfolding cf_set_def cf_assn_def PR_CONST_def by sepref
concrete_definition (in -) cf_set_impl 
  uses Network_Impl.cf_set_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"

sepref_thm cf_init_impl is "uncurry0 (PR_CONST cf_init)" 
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
  unfolding PR_CONST_def cf_assn_def cf_init_def 
  apply (rewrite amtx_fold_custom_new[of N N])
  by sepref  
concrete_definition (in -) cf_init_impl 
  uses Network_Impl.cf_init_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = 
  cf_get_impl.refine[OF nwi_this] 
  cf_set_impl.refine[OF nwi_this] 
  cf_init_impl.refine[OF nwi_this]
  
subsubsection \<open>Functions from Nodes by Arrays\<close>  
text \<open>
  We provide a template for implementing functions from nodes by arrays.
  Outside the node range, the abstract functions have a default value.

  This template is then used for refinement of various data structures.
\<close>  
definition "is_nf dflt f a 
  \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(length l = N \<and> (\<forall>i<N. l!i = f i) \<and> (\<forall>i\<ge>N. f i = dflt))"
  
lemma nf_init_rule[sep_heap_rules]: 
  "<emp> Array.new N dflt <is_nf dflt (\<lambda>_. dflt)>"
  unfolding is_nf_def by sep_auto

lemma nf_copy_rule[sep_heap_rules]: 
  "<is_nf dflt f a> array_copy a <\<lambda>r. is_nf dflt f a * is_nf dflt f r>"
  unfolding is_nf_def by sep_auto
  
lemma nf_lookup_rule[sep_heap_rules]: 
  "v<N \<Longrightarrow> <is_nf dflt f a> Array.nth a v <\<lambda>r. is_nf dflt f a *\<up>(r = f v)>"
  unfolding is_nf_def by sep_auto
  
lemma nf_update_rule[sep_heap_rules]: 
  "v<N \<Longrightarrow> <is_nf dflt f a> Array.upd v x a <is_nf dflt (f(v:=x))>"  
  unfolding is_nf_def by sep_auto
  
subsubsection \<open>Adjacency Map by Array\<close>  
definition "am_assn \<equiv> is_nf ([]::nat list)"    
sepref_register am_get  
lemma am_get_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST am_get)) 
  \<in> am_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"  
  unfolding am_assn_def am_get_def list_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: refine_pw_simps)

    
definition (in -) "am_is_in_V_impl am u \<equiv> do {
  amu \<leftarrow> Array.nth am u;
  return (\<not>is_Nil amu)
}"    
sepref_register am_is_in_V    
lemma am_is_in_V_hnr[sepref_fr_rules]: "(uncurry am_is_in_V_impl, uncurry (am_is_in_V)) 
  \<in> [\<lambda>(_,v). v<N]\<^sub>a am_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow> bool_assn"  
  unfolding am_assn_def am_is_in_V_def am_is_in_V_impl_def
  apply sepref_to_hoare 
  apply (sep_auto simp: refine_pw_simps split: list.split)
  done
    
subsubsection \<open>Excess by Array\<close>  
definition "x_assn \<equiv> is_nf (0::capacity_impl)"    
  
lemma x_init_hnr[sepref_fr_rules]: 
  "(uncurry0 (Array.new N 0), uncurry0 x_init) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a x_assn"  
  apply sepref_to_hoare unfolding x_assn_def x_init_def by sep_auto
    
sepref_register x_get    
lemma x_get_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST x_get)) 
  \<in> x_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn"
  apply sepref_to_hoare 
  unfolding x_assn_def x_get_def by (sep_auto simp: refine_pw_simps)
    
definition (in -) "x_add_impl x u \<Delta> \<equiv> do {
  xu \<leftarrow> Array.nth x u;
  x \<leftarrow> Array.upd u (xu+\<Delta>) x;
  return x
}"  
sepref_register x_add
lemma x_add_hnr[sepref_fr_rules]: 
  "(uncurry2 x_add_impl, uncurry2 (PR_CONST x_add)) 
  \<in> x_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a cap_assn\<^sup>k \<rightarrow>\<^sub>a x_assn"  
  apply sepref_to_hoare 
  unfolding x_assn_def x_add_impl_def x_add_def 
  by (sep_auto simp: refine_pw_simps)

subsubsection \<open>Labeling by Array\<close>      
definition "l_assn \<equiv> is_nf (0::nat)"    
definition (in -) "l_init_impl N s cardV \<equiv> do {
  l \<leftarrow> Array.new N (0::nat);
  l \<leftarrow> Array.upd s cardV l;
  return l
}"  
sepref_register l_init  
lemma l_init_hnr[sepref_fr_rules]: 
  "(l_init_impl N s, (PR_CONST l_init)) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"  
  apply sepref_to_hoare 
  unfolding l_assn_def l_init_def l_init_impl_def by sep_auto
    
sepref_register l_get    
lemma l_get_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST l_get)) 
  \<in> l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_to_hoare 
  unfolding l_assn_def l_get_def by (sep_auto simp: refine_pw_simps)
    
sepref_register l_get_rlx
lemma l_get_rlx_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST l_get_rlx)) 
  \<in> l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_to_hoare 
  unfolding l_assn_def l_get_rlx_def by (sep_auto simp: refine_pw_simps)
    
    
sepref_register l_set
lemma l_set_hnr[sepref_fr_rules]: 
  "(uncurry2 (\<lambda>a i x. Array.upd i x a), uncurry2 (PR_CONST l_set)) 
  \<in> l_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"
  apply sepref_to_hoare 
  unfolding l_assn_def l_set_def 
  by (sep_auto simp: refine_pw_simps split: prod.split)
      
    
subsubsection \<open>Label Frequency by Array\<close>  
  
definition "cnt_assn (f::node\<Rightarrow>nat) a \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(length l = 2*N \<and> (\<forall>i<2*N. l!i = f i) \<and> (\<forall>i\<ge>2*N. f i = 0))"
  
definition (in -) "cnt_init_impl N C \<equiv> do {
  a \<leftarrow> Array.new (2*N) (0::nat);
  a \<leftarrow> Array.upd 0 (C-1) a;
  a \<leftarrow> Array.upd C 1 a;
  return a
}"  

definition (in -) "cnt_incr_impl a k \<equiv> do {
  freq \<leftarrow> Array.nth a k;
  a \<leftarrow> Array.upd k (freq+1) a;
  return a
}"  

definition (in -) "cnt_decr_impl a k \<equiv> do {
  freq \<leftarrow> Array.nth a k;
  a \<leftarrow> Array.upd k (freq-1) a;
  return a
}"  
  
sepref_register cnt_init cnt_get cnt_incr cnt_decr 
lemma cnt_init_hnr[sepref_fr_rules]: "(cnt_init_impl N, PR_CONST cnt_init) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a cnt_assn"
  apply sepref_to_hoare
  unfolding cnt_init_def cnt_init_impl_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 

lemma cnt_get_hnr[sepref_fr_rules]: "(uncurry Array.nth, uncurry (PR_CONST cnt_get)) \<in> cnt_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"    
  apply sepref_to_hoare
  unfolding cnt_get_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 

lemma cnt_incr_hnr[sepref_fr_rules]: "(uncurry cnt_incr_impl, uncurry (PR_CONST cnt_incr)) \<in> cnt_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a cnt_assn"    
  apply sepref_to_hoare
  unfolding cnt_incr_def cnt_incr_impl_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 
    
lemma cnt_decr_hnr[sepref_fr_rules]: "(uncurry cnt_decr_impl, uncurry (PR_CONST cnt_decr)) \<in> cnt_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a cnt_assn"    
  apply sepref_to_hoare
  unfolding cnt_decr_def cnt_decr_impl_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 
  
subsubsection \<open>Queue by Two Stacks\<close>  
definition (in -) "q_\<alpha> \<equiv> \<lambda>(L,R). L@rev R"    
definition (in -) "q_empty_impl \<equiv> ([],[])"
definition (in -) "q_is_empty_impl \<equiv> \<lambda>(L,R). is_Nil L \<and> is_Nil R"
definition (in -) "q_enqueue_impl \<equiv> \<lambda>x (L,R). (L,x#R)"  
definition (in -) "q_dequeue_impl \<equiv> \<lambda>(x#L,R) \<Rightarrow> (x,(L,R)) | ([],R) \<Rightarrow> case rev R of (x#L) \<Rightarrow> (x,(L,[]))"  
    
lemma q_empty_impl_correct[simp]: "q_\<alpha> q_empty_impl = []" by (auto simp: q_\<alpha>_def q_empty_impl_def)
lemma q_enqueue_impl_correct[simp]: "q_\<alpha> (q_enqueue_impl x Q) = q_\<alpha> Q @ [x]" 
  by (auto simp: q_\<alpha>_def q_enqueue_impl_def split: prod.split)
  
lemma q_is_empty_impl_correct[simp]: "q_is_empty_impl Q \<longleftrightarrow> q_\<alpha> Q = []" 
  unfolding q_\<alpha>_def q_is_empty_impl_def
  by (cases Q) (auto split: list.splits)

    
lemma q_dequeue_impl_correct_aux: "\<lbrakk>q_\<alpha> Q = x#xs\<rbrakk> \<Longrightarrow> apsnd q_\<alpha> (q_dequeue_impl Q) = (x,xs)"
  unfolding q_\<alpha>_def q_dequeue_impl_def
  by (cases Q) (auto split!: list.split)  

lemma q_dequeue_impl_correct[simp]: 
  assumes "q_dequeue_impl Q = (x,Q')"
  assumes "q_\<alpha> Q \<noteq> []"
  shows "x = hd (q_\<alpha> Q)" and "q_\<alpha> Q' = tl (q_\<alpha> Q)"
  using assms q_dequeue_impl_correct_aux[of Q]
  by - (cases "q_\<alpha> Q"; auto)+
    
definition "q_assn \<equiv> pure (br q_\<alpha> (\<lambda>_. True))"

sepref_register q_empty q_is_empty q_enqueue q_dequeue  
  
lemma q_empty_impl_hnr[sepref_fr_rules]: "(uncurry0 (return q_empty_impl), uncurry0 q_empty) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a q_assn"  
  apply (sepref_to_hoare)
  unfolding q_assn_def q_empty_def pure_def
  by (sep_auto simp: in_br_conv) 
    
lemma q_is_empty_impl_hnr[sepref_fr_rules]: "(return o q_is_empty_impl, q_is_empty) \<in> q_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply (sepref_to_hoare)
  unfolding q_assn_def q_is_empty_def pure_def
  by (sep_auto simp: in_br_conv) 
  
lemma q_enqueue_impl_hnr[sepref_fr_rules]: 
  "(uncurry (return oo q_enqueue_impl), uncurry (PR_CONST q_enqueue)) \<in> nat_assn\<^sup>k *\<^sub>a q_assn\<^sup>d \<rightarrow>\<^sub>a q_assn"    
  apply (sepref_to_hoare)
  unfolding q_assn_def q_enqueue_def pure_def
  by (sep_auto simp: in_br_conv refine_pw_simps) 
  
lemma q_dequeue_impl_hnr[sepref_fr_rules]:    
  "(return o q_dequeue_impl, q_dequeue) \<in> q_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn \<times>\<^sub>a q_assn"
  apply (sepref_to_hoare)
  unfolding q_assn_def q_dequeue_def pure_def prod_assn_def
  by (sep_auto simp: in_br_conv refine_pw_simps split: prod.split) 
    
subsubsection \<open>Combined Frequency Count and Labeling\<close>    
definition "clc_assn \<equiv> cnt_assn \<times>\<^sub>a l_assn"
    
sepref_register clc_init clc_get clc_set clc_has_gap clc_get_rlx
sepref_thm clc_init_impl is "PR_CONST clc_init" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding clc_init_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_init_impl 
  uses Network_Impl.clc_init_impl.refine_raw
lemmas [sepref_fr_rules] = clc_init_impl.refine[OF nwi_this]
    
sepref_thm clc_get_impl is "uncurry (PR_CONST clc_get)" 
  :: "clc_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding clc_get_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_get_impl 
  uses Network_Impl.clc_get_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_get_impl.refine[OF nwi_this]
  
sepref_thm clc_get_rlx_impl is "uncurry (PR_CONST clc_get_rlx)" 
  :: "clc_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding clc_get_rlx_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_get_rlx_impl 
  uses Network_Impl.clc_get_rlx_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_get_rlx_impl.refine[OF nwi_this]
  
  
sepref_thm clc_set_impl is "uncurry2 (PR_CONST clc_set)" 
  :: "clc_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding clc_set_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_set_impl 
  uses Network_Impl.clc_set_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_set_impl.refine[OF nwi_this]
  
sepref_thm clc_has_gap_impl is "uncurry (PR_CONST clc_has_gap)" 
  :: "clc_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn" 
  unfolding clc_has_gap_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_has_gap_impl 
  uses Network_Impl.clc_has_gap_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_has_gap_impl.refine[OF nwi_this]
  
subsubsection \<open>Push\<close>   
sepref_register fifo_push2
sepref_thm fifo_push_impl is "uncurry3 (PR_CONST fifo_push2)" 
  :: "x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a q_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k \<rightarrow>\<^sub>a ((x_assn\<times>\<^sub>acf_assn)\<times>\<^sub>aq_assn)" 
  unfolding fifo_push2_def PR_CONST_def
  by sepref  
concrete_definition (in -) fifo_push_impl 
  uses Network_Impl.fifo_push_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_push_impl.refine[OF nwi_this]
  
subsubsection \<open>Gap-Relabel\<close>   
sepref_register gap2
sepref_thm gap_impl is "uncurry2 (PR_CONST gap2)" 
  :: "nat_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding gap2_def PR_CONST_def
  by sepref
concrete_definition (in -) gap_impl 
  uses Network_Impl.gap_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = gap_impl.refine[OF nwi_this]
  
sepref_register min_adj_label
sepref_thm min_adj_label_impl is "uncurry3 (PR_CONST min_adj_label)" 
  :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"  
  unfolding min_adj_label_def PR_CONST_def
  by sepref  
concrete_definition (in -) min_adj_label_impl 
  uses Network_Impl.min_adj_label_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = min_adj_label_impl.refine[OF nwi_this]    
  
sepref_register min_adj_label_clc
sepref_thm min_adj_label_clc_impl is "uncurry3 (PR_CONST min_adj_label_clc)" 
  :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding min_adj_label_clc_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) min_adj_label_clc_impl 
  uses Network_Impl.min_adj_label_clc_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = min_adj_label_clc_impl.refine[OF nwi_this]
  
sepref_register fifo_relabel2
sepref_thm fifo_relabel_impl is "uncurry3 (PR_CONST fifo_relabel2)" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding fifo_relabel2_def PR_CONST_def
  by sepref  
concrete_definition (in -) fifo_relabel_impl 
  uses Network_Impl.fifo_relabel_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_relabel_impl.refine[OF nwi_this]
  
sepref_register fifo_gap_relabel2
sepref_thm fifo_gap_relabel_impl is "uncurry5 (PR_CONST fifo_gap_relabel2)" 
    :: "nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a q_assn\<^sup>d *\<^sub>a node_assn\<^sup>k 
      \<rightarrow>\<^sub>a clc_assn \<times>\<^sub>a q_assn" 
  unfolding fifo_gap_relabel2_def PR_CONST_def
  by sepref  
concrete_definition (in -) fifo_gap_relabel_impl 
  uses Network_Impl.fifo_gap_relabel_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_gap_relabel_impl.refine[OF nwi_this]

subsubsection \<open>Discharge\<close>  
  
sepref_register dis_loop2
sepref_thm fifo_dis_loop_impl is "uncurry5 (PR_CONST dis_loop2)" 
    :: "am_assn\<^sup>k *\<^sub>a x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a clc_assn\<^sup>d *\<^sub>a q_assn\<^sup>d *\<^sub>a node_assn\<^sup>k 
      \<rightarrow>\<^sub>a (x_assn\<times>\<^sub>acf_assn)\<times>\<^sub>aclc_assn \<times>\<^sub>a q_assn" 
  unfolding dis_loop2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_dis_loop_impl 
  uses Network_Impl.fifo_dis_loop_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_dis_loop_impl.refine[OF nwi_this]
  
sepref_register fifo_discharge2
sepref_thm fifo_fifo_discharge_impl is "uncurry5 (PR_CONST fifo_discharge2)" 
    :: "nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k *\<^sub>a x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a clc_assn\<^sup>d *\<^sub>a q_assn\<^sup>d 
    \<rightarrow>\<^sub>a (x_assn\<times>\<^sub>acf_assn)\<times>\<^sub>aclc_assn \<times>\<^sub>a q_assn" 
  unfolding fifo_discharge2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_fifo_discharge_impl 
  uses Network_Impl.fifo_fifo_discharge_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_fifo_discharge_impl.refine[OF nwi_this]
  
subsubsection \<open>Computing the Initial State\<close>  
sepref_register init_C
sepref_thm fifo_init_C_impl is "(PR_CONST init_C)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding init_C_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_init_C_impl 
  uses Network_Impl.fifo_init_C_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_init_C_impl.refine[OF nwi_this]
  
sepref_register q_init
sepref_thm fifo_q_init_impl is "(PR_CONST q_init)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a q_assn" 
  unfolding q_init_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_q_init_impl 
  uses Network_Impl.fifo_q_init_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_q_init_impl.refine[OF nwi_this]

sepref_register pp_init_xcf2'
sepref_thm pp_init_xcf2'_impl is "uncurry (PR_CONST pp_init_xcf2')" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>d \<rightarrow>\<^sub>a x_assn \<times>\<^sub>a cf_assn" 
  unfolding pp_init_xcf2'_def PR_CONST_def
  by sepref
concrete_definition (in -) pp_init_xcf2'_impl 
  uses Network_Impl.pp_init_xcf2'_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = pp_init_xcf2'_impl.refine[OF nwi_this]

subsubsection \<open>Main Algorithm\<close>  
sepref_register fifo_push_relabel_run2
sepref_thm fifo_push_relabel_run_impl 
  is "uncurry (PR_CONST fifo_push_relabel_run2)" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>d \<rightarrow>\<^sub>a cf_assn" 
  unfolding fifo_push_relabel_run2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_push_relabel_run_impl 
  uses Network_Impl.fifo_push_relabel_run_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_push_relabel_run_impl.refine[OF nwi_this]
  
sepref_register fifo_push_relabel_init2
sepref_thm fifo_push_relabel_init_impl 
  is "uncurry0 (PR_CONST fifo_push_relabel_init2)" 
    :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
  unfolding fifo_push_relabel_init2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_push_relabel_init_impl 
  uses Network_Impl.fifo_push_relabel_init_impl.refine_raw 
    is "(uncurry0 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_push_relabel_init_impl.refine[OF nwi_this]

  
sepref_register fifo_push_relabel2
sepref_thm fifo_push_relabel_impl is "(PR_CONST fifo_push_relabel2)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
  unfolding fifo_push_relabel2_alt PR_CONST_def
  by sepref
concrete_definition (in -) fifo_push_relabel_impl 
  uses Network_Impl.fifo_push_relabel_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_push_relabel_impl.refine[OF nwi_this]
  
  
end --\<open>Network Impl. Locale\<close>
  
export_code fifo_push_relabel_impl checking SML_imp 
  
subsection \<open>Combining the Refinement Steps\<close>  
  
theorem (in Network_Impl) fifo_push_relabel_impl_correct[sep_heap_rules]: 
  assumes ABS_PS: "is_adj_map am"
  shows "
    <am_assn am ami> 
      fifo_push_relabel_impl c s t N ami
    <\<lambda>cfi. \<exists>\<^sub>Acf. 
        cf_assn cf cfi 
      * \<up>(isMaxFlow (flow_of_cf cf) \<and> RPreGraph c s t cf)>\<^sub>t"
proof -
  have AM: "(am, adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
    using ABS_PS
    unfolding is_adj_map_def adjacent_nodes_def list_set_rel_def
    by (auto simp: in_br_conv)
      
  note fifo_push_relabel2_refine[OF AM]    
  also note fifo_push_relabel_correct
  finally have R1: 
    "fifo_push_relabel2 am 
    \<le> \<Down> (br flow_of_cf (RPreGraph c s t)) (SPEC isMaxFlow)" .  

  have [simp]: "nofail (\<Down>R (RES X))" for R X by (auto simp: refine_pw_simps)

  note R2 = fifo_push_relabel_impl.refine[
              OF nwi_this, to_hnr, unfolded autoref_tag_defs]
  note R3 = hn_refine_ref[OF R1 R2, of ami]
  note R4 = R3[unfolded hn_ctxt_def pure_def, THEN hn_refineD, simplified]
    
  show ?thesis  
    by (sep_auto heap: R4 simp: pw_le_iff refine_pw_simps in_br_conv)
qed
  
  
subsection \<open>Combination with Network Checker and Main Correctness Theorem\<close>
  
definition "fifo_push_relabel_impl_tab_am c s t N am \<equiv> do {
  ami \<leftarrow> Array.make N am;  (* TODO/DUP: Called init_ps in Edmonds-Karp impl *)
  fifo_push_relabel_impl c s t N ami
}"  
  
  
theorem fifo_push_relabel_impl_tab_am_correct[sep_heap_rules]: 
  assumes NW: "Network c s t"
  assumes VN: "Graph.V c \<subseteq> {0..<N}"
  assumes ABS_PS: "Graph.is_adj_map c am"
  shows "
    <emp> 
      fifo_push_relabel_impl_tab_am c s t N am
    <\<lambda>cfi. \<exists>\<^sub>Acf. 
        asmtx_assn N id_assn cf cfi 
      * \<up>(Network.isMaxFlow c s t (Network.flow_of_cf c cf)
        \<and> RPreGraph c s t cf
        )>\<^sub>t"
proof -
  interpret Network c s t by fact
  interpret Network_Impl c s t N using VN by unfold_locales    
  
  from ABS_PS have [simp]: "am u = []" if "u\<ge>N" for u
    unfolding is_adj_map_def
    using E_ss_VxV VN that 
    apply (subgoal_tac "u\<notin>V") 
    by (auto simp del: inV_less_N)
  
  show ?thesis
    unfolding fifo_push_relabel_impl_tab_am_def 
    apply vcg
    apply (rule Hoare_Triple.cons_rule[
            OF _ _ fifo_push_relabel_impl_correct[OF ABS_PS]])
    subgoal unfolding am_assn_def is_nf_def by sep_auto
    subgoal unfolding cf_assn_def by sep_auto
    done  
qed        
  
  
definition "fifo_push_relabel el s t \<equiv> do {
  case prepareNet el s t of
    None \<Rightarrow> return None
  | Some (c,am,N) \<Rightarrow> do {
      cf \<leftarrow> fifo_push_relabel_impl_tab_am c s t N am;
      return (Some (c,am,N,cf))
  }
}"
export_code fifo_push_relabel checking SML_imp

  
(* TODO: Also generate correctness theorem for fifo_push_relabel_run!
  For this, push the split up to abstract level!
*)  
  
text \<open>
  Main correctness statement:
  If \<open>fifo_push_relabel\<close> returns \<open>None\<close>, the edge list was invalid or described an invalid network.
  If it returns \<open>Some (c,am,N,cfi)\<close>, then the edge list is valid and describes a valid network.
  Moreover, \<open>cfi\<close> is an integer square matrix of dimension \<open>N\<close>, which describes a valid residual graph
  in the network, whose corresponding flow is maximal.
  Finally, \<open>am\<close> is a valid adjacency map of the graph, and the nodes of the graph are integers less than \<open>N\<close>.
\<close>  
  
theorem fifo_push_relabel_correct:
  "<emp>
  fifo_push_relabel el s t
  <\<lambda>
    None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
  | Some (c,am,N,cfi) \<Rightarrow> 
      \<up>(c = ln_\<alpha> el \<and> ln_invar el \<and> Network c s t) 
    * (\<exists>\<^sub>Acf. asmtx_assn N int_assn cf cfi 
          * \<up>(RPreGraph c s t cf 
            \<and> Network.isMaxFlow c s t (Network.flow_of_cf c cf))) 
    * \<up>(Graph.is_adj_map c am \<and> Graph.V c \<subseteq> {0..<N})
  >\<^sub>t
  "
  unfolding fifo_push_relabel_def
  using prepareNet_correct[of el s t]
  by (sep_auto simp: ln_rel_def in_br_conv)
  

subsubsection \<open>Justification of Splitting into Prepare and Run Phase\<close>    
(* TODO: Show correctness theorems for both phases separately!  *)    
    
definition "fifo_push_relabel_prepare_impl el s t \<equiv> do {
  case prepareNet el s t of
    None \<Rightarrow> return None
  | Some (c,am,N) \<Rightarrow> do {
      ami \<leftarrow> Array.make N am;
      cfi \<leftarrow> fifo_push_relabel_init_impl c N;
      return (Some (N,am,ami,c,cfi))
    }
}"

theorem justify_fifo_push_relabel_prep_run_split:
  "fifo_push_relabel el s t = 
  do {
    pr \<leftarrow> fifo_push_relabel_prepare_impl el s t;
    case pr of
      None \<Rightarrow> return None
    | Some (N,am,ami,c,cf) \<Rightarrow> do {
        cf \<leftarrow> fifo_push_relabel_run_impl s t N ami cf;
        return (Some (c,am,N,cf))
      }
  }"  
  unfolding fifo_push_relabel_def fifo_push_relabel_prepare_impl_def
    fifo_push_relabel_impl_tab_am_def fifo_push_relabel_impl_def
  by (auto split: option.split)  
  
  
end
