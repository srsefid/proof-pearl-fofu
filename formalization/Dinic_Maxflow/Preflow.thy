theory Preflow
imports Augmenting_Path
  Refine_Add_Fofu
  Refine_Monadic_Syntax_Sugar
begin
     
context NPreflow 
begin  
  lemma excess_s_non_pos: "excess s \<le> 0"
    unfolding excess_def
    by (simp add: capacity_const sum_nonneg)  

end  
  
locale Labeling = NPreflow +
  fixes l :: "node \<Rightarrow> nat"
  assumes valid: "(u,v) \<in> cf.E \<Longrightarrow> l(u) \<le> l(v) + 1"
  assumes lab_src[simp]: "l s = card V"
  assumes lab_sink[simp]: "l t = 0"
begin
  text \<open>Generalizing validity to paths\<close>
  lemma gen_valid: "l(u) \<le> l(t) + length p" if "cf.isPath u p t"
    using that by (induction p arbitrary: u; fastforce dest: valid)
  
  text \<open>
    In a valid labeling, there cannot be an augmenting path.
    The proof works by contradiction, using the validity constraint 
    to show that any augmenting path would be too long for a simple path.
  \<close>
  lemma no_augmenting_path[simp, intro!]: "\<not>isAugmentingPath p"
  proof
    assume "isAugmentingPath p"  
    hence SP: "cf.isSimplePath s p t" unfolding isAugmentingPath_def .
    hence "cf.isPath s p t" unfolding cf.isSimplePath_def by auto
    from gen_valid[OF this] have "length p \<ge> card V" by auto
    with cf.simplePath_length_less_V[OF _ SP] show False by auto 
  qed
end

(*lemma "\<forall>x\<in>A. f x=(0::'a::comm_monoid_add) \<Longrightarrow> sum f A = 0"*)
  
  
context Network 
begin  
  
definition "pp_init_f \<equiv> \<lambda>(u,v). if (u=s) then c (u,v) else 0"
definition "pp_init_l \<equiv> (\<lambda>x. 0)(s := card V)"

  
lemma pp_init_invar: "Labeling c s t pp_init_f pp_init_l"
  apply (unfold_locales;
      ((auto simp: pp_init_f_def pp_init_l_def cap_non_negative; fail) 
        | (intro ballI)?))  
proof -  
  fix v
  assume "v\<in>V - {s,t}"
  hence "\<forall>e\<in>outgoing v. pp_init_f e = 0"
    by (auto simp: outgoing_def pp_init_f_def)
  hence [simp]: "sum pp_init_f (outgoing v) = 0" by auto
  have "0 \<le> pp_init_f e" for e
    by (auto simp: pp_init_f_def cap_non_negative split: prod.split)
  from sum_bounded_below[of "incoming v" 0 pp_init_f, OF this]
  have "0 \<le> sum pp_init_f (incoming v)" by auto
  thus "sum pp_init_f (outgoing v) \<le> sum pp_init_f (incoming v)"
    by auto
      
next
  fix u v
  assume "(u, v) \<in> Graph.E (residualGraph c pp_init_f)"  
  thus "pp_init_l u \<le> pp_init_l v + 1"
    unfolding pp_init_l_def Graph.E_def pp_init_f_def residualGraph_def
    by (auto split: if_splits)
      
qed    

end -- \<open>Network\<close>  
  
context NPreflow begin  
  lemma f_non_negative[simp]: "0 \<le> f e"
    using capacity_const by (cases e) auto
  
  definition "augment_edge \<equiv> \<lambda>(u,v) \<Delta>. 
    if (u,v)\<in>E then f( (u,v) := f (u,v) + \<Delta> )
    else if (v,u)\<in>E then f( (v,u) := f (v,u) - \<Delta> )
    else f"

  lemma augment_edge_zero[simp]: "augment_edge e 0 = f" 
    unfolding augment_edge_def by (auto split: prod.split) 
      
  lemma augment_edge_same[simp]: "e\<in>E \<Longrightarrow> augment_edge e \<Delta> e = f e + \<Delta>"
    unfolding augment_edge_def by (auto split!: prod.splits)
      
  lemma augment_edge_other[simp]:"\<lbrakk>e\<in>E; e'\<noteq>e \<rbrakk> \<Longrightarrow> augment_edge e \<Delta> e' = f e'"    
    unfolding augment_edge_def by (auto split!: prod.splits)

  lemma augment_edge_rev_same[simp]: "(v,u)\<in>E \<Longrightarrow> augment_edge (u,v) \<Delta> (v,u) = f (v,u) - \<Delta>"    
    using no_parallel_edge
    unfolding augment_edge_def by (auto split!: prod.splits)

  lemma augment_edge_rev_other[simp]: "\<lbrakk>(u,v)\<notin>E; e'\<noteq>(v,u)\<rbrakk> \<Longrightarrow> augment_edge (u,v) \<Delta> e' = f e'"    
    unfolding augment_edge_def by (auto split!: prod.splits)
      
  lemma augment_edge_preflow_preserve: 
    "\<lbrakk>0\<le>\<Delta>; \<Delta> \<le> cf (u,v); \<Delta> \<le> excess u\<rbrakk> \<Longrightarrow> Preflow c s t (augment_edge (u,v) \<Delta>)"  
    apply unfold_locales
    subgoal
      unfolding residualGraph_def augment_edge_def  
      using capacity_const
      by (fastforce split!: if_splits)
    subgoal
    proof (intro ballI; clarsimp)
      assume "0\<le>\<Delta>" "\<Delta> \<le> cf (u,v)" "\<Delta> \<le> excess u"
      fix v'
      assume V': "v'\<in>V" "v'\<noteq>s" "v'\<noteq>t"  
        
      show "sum (augment_edge (u, v) \<Delta>) (outgoing v')
              \<le> sum (augment_edge (u, v) \<Delta>) (incoming v')"  
      proof (cases)
        assume "\<Delta> = 0"
        with no_deficient_nodes show ?thesis using V' by auto 
      next
        assume "\<Delta> \<noteq> 0" with \<open>0\<le>\<Delta>\<close> have "0<\<Delta>" by auto
        with \<open>\<Delta> \<le> cf (u,v)\<close> have "(u,v)\<in>cf.E" unfolding Graph.E_def by auto
            
        show ?thesis
        proof (cases)    
          assume [simp]: "(u,v)\<in>E"
          hence AE: "augment_edge (u,v) \<Delta> = f ( (u,v) := f (u,v) + \<Delta> )"  
            unfolding augment_edge_def by auto
          have 1: "\<forall>e\<in>outgoing v'. augment_edge (u,v) \<Delta> e = f e" if "v'\<noteq>u"
            using that unfolding outgoing_def AE by auto
          have 2: "\<forall>e\<in>incoming v'. augment_edge (u,v) \<Delta> e = f e" if "v'\<noteq>v"
            using that unfolding incoming_def AE by auto

          from \<open>(u,v)\<in>E\<close> no_self_loop have "u\<noteq>v" by blast
              
          {
            assume "v' \<noteq> u" "v' \<noteq> v"
            with 1 2 V' no_deficient_nodes have ?thesis by auto
          } moreover {
            assume [simp]: "v'=v" 
            have "sum (augment_edge (u, v) \<Delta>) (outgoing v') = sum f (outgoing v)"  
              using 1 \<open>u\<noteq>v\<close> V' by auto
            also have "\<dots> \<le> sum f (incoming v)" using V' no_deficient_nodes by auto
            also have "\<dots> \<le> sum (augment_edge (u, v) \<Delta>) (incoming v)"
              apply (rule sum_mono)
              using \<open>0\<le>\<Delta>\<close>
              by (auto simp: incoming_def augment_edge_def split!: if_split)
            finally have ?thesis by simp
          } moreover {
            assume [simp]: "v'=u"
            have A1: "sum (augment_edge (u,v) \<Delta>) (incoming v') = sum f (incoming u)"  
              using 2 \<open>u\<noteq>v\<close> by auto
            have "(u,v) \<in> outgoing u" using \<open>(u,v)\<in>E\<close> by (auto simp: outgoing_def)
            note AUX = sum.remove[OF _ this, simplified]
            have A2: "sum (augment_edge (u,v) \<Delta>) (outgoing u) = sum f (outgoing u) + \<Delta>"
              using AUX[of "augment_edge (u,v) \<Delta>"] AUX[of "f"] by auto
            from A1 A2 \<open>\<Delta> \<le> excess u\<close> no_deficient_nodes V' have ?thesis 
              unfolding excess_def by auto
          } ultimately show ?thesis by blast
        next
          assume [simp]: \<open>(u,v)\<notin>E\<close> 
          hence [simp]: "(v,u)\<in>E" using cfE_ss_invE \<open>(u,v)\<in>cf.E\<close> by auto
          from \<open>(u,v)\<notin>E\<close> \<open>(v,u)\<in>E\<close> have "u\<noteq>v" by blast
          
          have AE: "augment_edge (u,v) \<Delta> = f ( (v,u) := f (v,u) - \<Delta> )"  
            unfolding augment_edge_def by simp
          have 1: "\<forall>e\<in>outgoing v'. augment_edge (u,v) \<Delta> e = f e" if "v'\<noteq>v"
            using that unfolding outgoing_def AE by auto
          have 2: "\<forall>e\<in>incoming v'. augment_edge (u,v) \<Delta> e = f e" if "v'\<noteq>u"
            using that unfolding incoming_def AE by auto

          {
            assume "v' \<noteq> u" "v' \<noteq> v"
            with 1 2 V' no_deficient_nodes have ?thesis by auto
          } moreover {
            assume [simp]: "v'=u" 
            have A1: "sum (augment_edge (u, v) \<Delta>) (outgoing v') = sum f (outgoing u)"  
              using 1 \<open>u\<noteq>v\<close> V' by auto
                
            have "(v,u) \<in> incoming u" using \<open>(v,u)\<in>E\<close> by (auto simp: incoming_def)
            note AUX = sum.remove[OF _ this, simplified]    
            have A2: "sum (augment_edge (u,v) \<Delta>) (incoming u) = sum f (incoming u) - \<Delta>"
              using AUX[of "augment_edge (u,v) \<Delta>"] AUX[of "f"] by auto
                
            from A1 A2 \<open>\<Delta> \<le> excess u\<close> no_deficient_nodes V' have ?thesis 
              unfolding excess_def by auto
          } moreover {
            assume [simp]: "v'=v"
            have "sum (augment_edge (u,v) \<Delta>) (outgoing v') \<le> sum f (outgoing v')"  
              apply (rule sum_mono)
              using \<open>0<\<Delta>\<close>  
              by (auto simp: augment_edge_def)  
            also have "\<dots> \<le> sum f (incoming v)" using no_deficient_nodes V' by auto
            also have "\<dots> \<le> sum (augment_edge (u,v) \<Delta>) (incoming v')"    
              using 2 \<open>u\<noteq>v\<close> by auto
            finally have ?thesis by simp
          } ultimately show ?thesis by blast
        qed      
      qed              
    qed          
    done            
      
  lemma augment_edge_cf[simp]: "(u,v)\<in>cf.E \<Longrightarrow> 
    residualGraph c (augment_edge (u,v) \<Delta>) = cf( (u,v) := cf (u,v) - \<Delta>, (v,u) := cf (v,u) + \<Delta>)"    
  proof -
    assume "(u,v)\<in>cf.E"
    hence "(u,v)\<in>E\<union>E\<inverse>" using cfE_ss_invE ..
    thus ?thesis
      apply (intro ext; cases "(u,v)\<in>E")
      subgoal for e' 
        apply (cases "e'=(u,v)")  
        applyS (simp split!: if_splits add: no_self_loop residualGraph_def)
        apply (cases "e'=(v,u)")  
        applyS (simp split!: if_splits add: no_parallel_edge residualGraph_def)
        applyS (simp split!: if_splits prod.splits add: residualGraph_def augment_edge_def)
        done
      subgoal for e'
        apply (cases "e'=(u,v)")  
        applyS (simp split!: if_splits add: no_self_loop residualGraph_def)
        apply (cases "e'=(v,u)")  
        applyS (simp split!: if_splits add: no_self_loop residualGraph_def)
        applyS (simp split!: if_splits prod.splits add: residualGraph_def augment_edge_def)
        done
      done
  qed
      
end  
  
context Labeling begin  

  
definition "push \<equiv> \<lambda>(u,v). do {
  assert (excess u > 0 \<and> (u,v)\<in>cf.E \<and> l u = l v + 1); (* Precondition: Active node, admissible edge *)
  let \<Delta> = min (excess u) (cf (u,v));
  return (augment_edge (u,v) \<Delta>, l)
}"
  
lemma cfE_augment_ss:
  assumes EDGE: "(u,v)\<in>cf.E"  
  shows "Graph.E (residualGraph c (augment_edge (u,v) \<Delta>)) \<subseteq> insert (v,u) cf.E"
  using EDGE  
  apply (clarsimp)
  unfolding Graph.E_def  
  apply (auto split: if_splits)  
  done
  
lemma push_invar:
  assumes ACTIVE: "excess u > 0"
  assumes EDGE: "(u,v)\<in>cf.E"  
  assumes ADM: "l u = l v + 1"
  shows "push (u,v) \<le> SPEC (\<lambda>(f',l'). l'=l \<and> Labeling c s t f' l)"
  unfolding push_def  
  apply refine_vcg
  apply (vc_solve simp: assms)
  subgoal 
  proof -
    let ?f' = "(augment_edge (u, v) (min (excess u) (cf (u, v))))"
      
    interpret cf': Preflow c s t ?f'
     apply (rule augment_edge_preflow_preserve)
     using ACTIVE resE_nonNegative  
     by auto
    show "Labeling c s t ?f' l"
      apply unfold_locales using valid
      using cfE_augment_ss[OF EDGE] ADM
      apply (fastforce)
      by auto  
  qed      
  done    
    
definition "relabel u \<equiv> do {
  (* Precondition: Active, non-sink node without any admissible edges. *)
  assert (u\<noteq>t \<and> excess u > 0 \<and> (\<forall>v. (u,v)\<in>cf.E \<longrightarrow> l u \<noteq> l v + 1));
  let lu = Min { l v | v. (u,v)\<in>cf.E } + 1;
  let l = l( u := lu );
  return (f,l)
}"

lemma sum_f_nonneg[simp]: "sum f X \<ge> 0" using capacity_const
  by (auto simp: sum_nonneg) 
  
lemma active_has_cf_outgoing: "excess u > 0 \<Longrightarrow> cf.outgoing u \<noteq> {}"  
  unfolding excess_def
proof -
  assume "0 < sum f (incoming u) - sum f (outgoing u)"
  hence "0 < sum f (incoming u)"
    by (metis diff_gt_0_iff_gt linorder_neqE_linordered_idom linorder_not_le sum_f_nonneg)
  then obtain v where "(v,u)\<in>E" "f (v,u) > 0"
    by (metis (no_types, lifting) f_non_negative le_neq_trans not_less sum.neutral sum_incoming_pointwise zero_flow_simp)
  hence "cf (u,v) > 0" unfolding residualGraph_def by auto
  thus ?thesis unfolding cf.outgoing_def cf.E_def by fastforce   
qed      
  
  
lemma relabel_invar:
  assumes NOT_SINK: "u\<noteq>t"
  assumes ACTIVE: "excess u > 0"
  assumes NO_ADM: "\<And>v. (u,v)\<in>cf.E \<Longrightarrow> l u \<noteq> l v + 1"
  shows "relabel u \<le> SPEC (\<lambda>(f',l'). f'=f \<and> Labeling c s t f l')"  
proof -
  from ACTIVE have [simp]: "s\<noteq>u" using excess_s_non_pos by auto
      
  have [simp, intro!]: "finite {l v |v. (u, v) \<in> cf.E}"    
  proof -
    have "{l v |v. (u, v) \<in> cf.E} = l`snd`cf.outgoing u"
      by (auto simp: cf.outgoing_def)
    moreover have "finite (l`snd`cf.outgoing u)" by auto
    ultimately show ?thesis by auto
  qed    
  from active_has_cf_outgoing[OF ACTIVE] have [simp]: "\<exists>v. (u, v) \<in> cf.E" 
    by (auto simp: cf.outgoing_def)
  
  from NO_ADM valid have "l u < l v + 1" if "(u,v)\<in>cf.E" for v
    by (simp add: nat_less_le that)
  hence "l u \<le> Min { l v | v. (u,v)\<in>cf.E }" 
    by (auto simp: less_Suc_eq_le)
  with valid have "\<forall>u'. (u',u)\<in>cf.E \<longrightarrow> l u' \<le> Min { l v | v. (u,v)\<in>cf.E } + 1"    
    by (smt ab_semigroup_add_class.add.commute add_le_cancel_left le_trans)
  moreover have "\<forall>v. (u,v)\<in>cf.E \<longrightarrow> Min { l v | v. (u,v)\<in>cf.E } + 1 \<le> l v + 1"
    using Min_le by auto
  ultimately show ?thesis
    unfolding relabel_def
    apply refine_vcg  
    using NO_ADM NOT_SINK 
    apply (vc_solve simp: ACTIVE)
    apply (unfold_locales)
    subgoal for u' v' using valid by auto
    subgoal by auto    
    subgoal by auto
    done
qed      
    
oops
next: if neither relabel nor push applies, we have computed a maximum flow.
* We have a flow (excess v = 0) for all nodes but sink
* We cannot have augmenting paths: thm no_augmenting_path  
  
oops  
preflow push works on labeling and flow.
  
Define initial flow  
Define push and relabel operations  
Show 
  * invariant preservation, 
  * termination implies maxflow  
  * termination
  
  
  
    
    
end
