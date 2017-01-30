theory Preflow_Push_Impl
imports 
  (*"../../../../isafol/DRAT/Array_Map_Default"*)
  Preflow Graph_Impl
  "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin


context Network 
begin

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
    
    
    
    
definition "push2 x cf \<equiv> \<lambda>(u,v). do {
  assert ( u\<in>V \<and> v\<in>V );
  let \<Delta> = min (x u) (cf (u,v));
  return (x( u := x u - \<Delta>, v := x v + \<Delta> ),augment_edge_cf cf (u,v) \<Delta>)
}"
    
lemma push2_refine[refine]: "\<lbrakk>((x,cf),f)\<in>xf_rel; (ei,e)\<in>Id\<times>\<^sub>rId\<rbrakk> \<Longrightarrow> push2 x cf ei \<le> \<Down>xf_rel (push f l e)"
  unfolding push_def push2_def
  apply refine_vcg  
  apply (vc_solve simp: xf_rel_def)
  subgoal for u v 
    unfolding push_precond_def using cfE_of_ss_VxV by auto
  subgoal for u v 
    unfolding push_precond_def using cfE_of_ss_VxV by auto
  subgoal for u v 
    apply (rule conjI)
    subgoal proof -
      assume "Labeling c s t f l"
      then interpret Labeling c s t f l .
      assume "push_precond f l (u, v)"    
      then interpret l': push_effect_locale c s t f l u v by unfold_locales
      from l'.excess'_if show ?thesis by (auto simp: l'.\<Delta>_def push_effect_def)
    qed
    subgoal unfolding push_effect_def push_precond_def by auto
    done  
  done
  
definition "relabel2 cf l u \<equiv> do {
  assert (u\<in>V - {s,t});
  let nl = Min { l v | v. v\<in>V \<and> cf (u,v)\<noteq>0 } + 1;
  return ( l( u := nl) )
}"

lemma relabel2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel"
  assumes [simplified,simp]: "(li,l)\<in>Id" "(ui,u)\<in>Id"
  shows "relabel2 cf li ui \<le> \<Down>Id (relabel f l u)"    
proof -
  have [simp]: "{l v |v. v \<in> V \<and> cf_of f (u, v) \<noteq> 0} = {l v |v. cf_of f (u, v) \<noteq> 0}"
    using cfE_of_ss_VxV[of f] 
    by (auto simp: Graph.E_def)
  
  show ?thesis
    using assms
    unfolding relabel2_def relabel_def
    apply refine_vcg  
    apply (vc_solve simp: xf_rel_def relabel_effect_def Graph.E_def)  
    done
qed    
    
definition "discharge2 x cf l n u \<equiv> do {  
  assert (u \<in> V);
  while\<^sub>T (\<lambda>((x,cf),l,n). x u \<noteq> 0) (\<lambda>((x,cf),l,n). do {
    v \<leftarrow> selectp v. v\<in>n u;
    case v of
      None \<Rightarrow> do {
        l \<leftarrow> relabel2 cf l u;
        return ((x,cf),l,n(u := adjacent_nodes u))
      }
    | Some v \<Rightarrow> do {
        assert (v\<in>V);
        if (cf (u,v) \<noteq> 0 \<and> l u = l v + 1) then do {
          (x,cf) \<leftarrow> push2 x cf (u,v);
          return ((x,cf),l,n)
        } else do {
          return ((x,cf),l,n( u := n u - {v} ))
        }
      }
  }) ((x,cf),l,n)
}"
    
lemma discharge2_refine[refine]:     
  assumes A: "((x,cf),f) \<in> xf_rel"
  assumes [simplified,simp]: "(li,l)\<in>Id" "(ni,n)\<in>Id" "(ui,u)\<in>Id"
  shows "discharge2 x cf li ni ui \<le> \<Down>(xf_rel \<times>\<^sub>r Id \<times>\<^sub>r Id) (discharge f l n u)"  
  unfolding discharge2_def discharge_def
  apply (refine_rcg)
  apply (vc_solve simp: A)
  subgoal by (simp add: xf_rel_def)  
  applyS assumption    
  subgoal by (auto simp: xf_rel_def Graph.E_def)
  done  
    
    
    
definition "relabel_to_front2 \<equiv> do {
  let xcf = (pp_init_x, pp_init_cf);
  let l = pp_init_l;
  let n = rtf_init_n;

  let L_left=[];
  L_right \<leftarrow> spec l. distinct l \<and> set l = V - {s,t};

  ((x,cf),l,n,L_left,L_right) \<leftarrow> while\<^sub>T (\<lambda>((x,cf),l,n,L_left,L_right). L_right \<noteq> []) (\<lambda>((x,cf),l,n,L_left,L_right). do {
    assert (L_right \<noteq> []);
    let u = hd L_right;
    let old_lu = l u;

    ((x,cf),l,n) \<leftarrow> discharge2 x cf l n u;

    if (l u \<noteq> old_lu) then do {
      (* Move u to front of l, and restart scanning L. The cost for rev_append is amortized by going to next node in L *)
      let (L_left,L_right) = ([u],rev_append L_left (tl L_right));
      return ((x,cf),l,n,L_left,L_right)
    } else do {
      (* Goto next node in L *)
      let (L_left,L_right) = (u#L_left, tl L_right);
      return ((x,cf),l,n,L_left,L_right)
    }

  }) (xcf,l,n,L_left,L_right);

  return (flow_of_cf cf)
}"

lemma relabel_to_front2_refine[refine]: "relabel_to_front2 \<le> \<Down>Id relabel_to_front"
proof -
  define s_rel :: "(_ \<times> ( 'capacity flow * (nat\<Rightarrow>nat) * (node\<Rightarrow>node set) * node list * node list)) set"
    where "s_rel \<equiv> xf_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r br rev (\<lambda>_. True) \<times>\<^sub>r Id"
  
  have [refine_dref_RELATES]: "RELATES s_rel" unfolding RELATES_def ..
      
  {
    fix f l n
    assume "neighbor_invar c s t f l n"
    then interpret neighbor_invar c s t f l n .  
    have "flow_of_cf cf = f" by (rule fo_rg_inv)
  } note AUX1=this   
      
  show ?thesis
    unfolding relabel_to_front2_def relabel_to_front_def
    apply refine_rcg  
    apply refine_dref_type
    unfolding s_rel_def
    apply (vc_solve simp: in_br_conv rev_append_eq pp_init_x_rel xf_rel_def AUX1)
    done  
qed  

end -- \<open>Network\<close>  
  
xxx, ctd here:
  Now we are working directly on residual graph!
  Insert algorithms for init, and min-computation, then sepref!
  Should have stuff done for flow_of_cf already!
  
  
(* TODO: Duplicated from EdmondsKarp_Impl! *)  
locale Network_Impl = Network c s t for c :: "capacity_impl graph" and s t +
  fixes N :: nat
  assumes V_ss: "V\<subseteq>{0..<N}"
begin  
  lemma E_ss: "E \<subseteq> {0..<N}\<times>{0..<N}" using E_ss_VxV V_ss by auto

  lemma mtx_nonzero_iff[simp]: "mtx_nonzero c = E" unfolding E_def by (auto simp: mtx_nonzero_def)

  lemma mtx_nonzeroN: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<N}" using E_ss by simp

  lemma [simp]: "v\<in>V \<Longrightarrow> v<N" using V_ss by auto
  
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
  
  text \<open>Function from nodes, with default value\<close>
    
  definition "is_nf dflt f a \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(length l = N \<and> (\<forall>i<N. l!i = f i) \<and> (\<forall>i\<ge>N. f i = dflt))"
    
  lemma nf_init_rule[sep_heap_rules]: "<emp> Array.new N dflt <is_nf dflt (\<lambda>_. dflt)>"
    unfolding is_nf_def by sep_auto
    
  lemma nf_lookup_rule[sep_heap_rules]: "v<N \<Longrightarrow> <is_nf dflt f a> Array.nth a v <\<lambda>r. is_nf dflt f a *\<up>(r = f v)>"
    unfolding is_nf_def by sep_auto
    
  lemma nf_update_rule[sep_heap_rules]: "v<N \<Longrightarrow> <is_nf dflt f a> Array.upd v x a <is_nf dflt (f(v:=x))>"  
    unfolding is_nf_def by sep_auto
    
  
      
      
      
      
end  

(*
  Data structures:
    flow, capacity: Matrix

    neighbor list: Array: node \<rightarrow> node list
    labeling: Array: node \<rightarrow> nat
    excess: Array: node \<rightarrow> capacity

    L_left, L_right: HOL list

*)  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
end
