theory Preflow
imports Ford_Fulkerson
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
  lemma no_augmenting_path: "\<not>isAugmentingPath p"
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

definition "push_precond \<equiv> \<lambda>(u,v). excess u > 0 \<and> (u,v)\<in>cf.E \<and> l u = l v + 1"
  -- \<open>Admissible edge from active node\<close>
  
definition "push \<equiv> \<lambda>(u,v). do {
  assert (push_precond (u,v)); 
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
  assumes "push_precond (u,v)"
  shows "push (u,v) \<le> SPEC (\<lambda>(f',l'). l'=l \<and> Labeling c s t f' l)"
  unfolding push_def  
  apply refine_vcg
  apply (vc_solve simp: assms)
  subgoal 
  proof -
    let ?f' = "(augment_edge (u, v) (min (excess u) (cf (u, v))))"
      
    from assms have   
      ACTIVE: "excess u > 0"
      and EDGE: "(u,v)\<in>cf.E"  
      and ADM: "l u = l v + 1"
      unfolding push_precond_def by auto
      
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

(* Saturating and non-saturating pushes *)    
definition "sat_push_precond \<equiv> \<lambda>(u,v). excess u > 0 \<and> excess u \<ge> cf (u,v) \<and> (u,v)\<in>cf.E \<and> l u = l v + 1"
definition "unsat_push_precond \<equiv> \<lambda>(u,v). excess u > 0 \<and> excess u < cf (u,v) \<and> (u,v)\<in>cf.E \<and> l u = l v + 1"

lemma push_precond_eq_sat_or_unsat: "push_precond (u,v) \<longleftrightarrow> sat_push_precond (u,v) \<or> unsat_push_precond (u,v)"  
  unfolding push_precond_def sat_push_precond_def unsat_push_precond_def
  by auto  
  
lemma sat_unsat_push_disj: 
  "sat_push_precond (u,v) \<Longrightarrow> \<not>unsat_push_precond (u,v)"
  "unsat_push_precond (u,v) \<Longrightarrow> \<not>sat_push_precond (u,v)"
  unfolding sat_push_precond_def unsat_push_precond_def
  by auto  
  
lemma sat_push_alt: "sat_push_precond (u,v) \<Longrightarrow> push (u,v) = return (augment_edge (u,v) (cf (u,v)),l)"
  unfolding push_def push_precond_eq_sat_or_unsat sat_push_precond_def 
  by (auto simp: min_absorb2)
    
lemma unsat_push_alt: "unsat_push_precond (u,v) \<Longrightarrow> push (u,v) = return (augment_edge (u,v) (excess u),l)"    
  unfolding push_def push_precond_eq_sat_or_unsat unsat_push_precond_def 
  by (auto simp: min_absorb1)
    
    
(* Relabel *)    
definition "relabel_precond u \<equiv> u\<noteq>t \<and> excess u > 0 \<and> (\<forall>v. (u,v)\<in>cf.E \<longrightarrow> l u \<noteq> l v + 1)"    
  -- \<open>Active, non-sink node without any admissible edges.\<close>
    
definition "relabel u \<equiv> do {
  assert (relabel_precond u);
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
  assumes PRE: "relabel_precond u"
  shows "relabel u \<le> SPEC (\<lambda>(f',l'). f'=f \<and> l' u > l u \<and> Labeling c s t f l')"  
proof -
  from PRE have  
        NOT_SINK: "u\<noteq>t"
    and ACTIVE: "excess u > 0"
    and NO_ADM: "\<And>v. (u,v)\<in>cf.E \<Longrightarrow> l u \<noteq> l v + 1"
  unfolding relabel_precond_def by auto
  
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
  hence LU_INCR: "l u \<le> Min { l v | v. (u,v)\<in>cf.E }" 
    by (auto simp: less_Suc_eq_le)
  with valid have "\<forall>u'. (u',u)\<in>cf.E \<longrightarrow> l u' \<le> Min { l v | v. (u,v)\<in>cf.E } + 1"    
    by (smt ab_semigroup_add_class.add.commute add_le_cancel_left le_trans)
  moreover have "\<forall>v. (u,v)\<in>cf.E \<longrightarrow> Min { l v | v. (u,v)\<in>cf.E } + 1 \<le> l v + 1"
    using Min_le by auto
  ultimately show ?thesis
    unfolding relabel_def
    apply refine_vcg  
    apply (vc_solve simp: PRE)
    subgoal using LU_INCR by (simp add: less_Suc_eq_le)
    apply (unfold_locales)
    subgoal for u' v' using valid by auto
    subgoal by auto    
    subgoal using NOT_SINK by auto
    done
qed      

lemma push_relabel_term_imp_maxflow:
  assumes no_push: "\<forall>(u,v)\<in>cf.E. \<not>push_precond (u,v)"
  assumes no_relabel: "\<forall>u. \<not>relabel_precond u"
  shows "isMaxFlow f"  
proof -
  from assms have "\<forall>u\<in>V-{t}. excess u \<le> 0"
    unfolding push_precond_def relabel_precond_def
    by force 
  with excess_non_negative have "\<forall>u\<in>V-{s,t}. excess u = 0" by force
  then interpret NFlow 
    apply unfold_locales 
    using no_deficient_nodes unfolding excess_def by auto
  from noAugPath_iff_maxFlow no_augmenting_path show "isMaxFlow f" by auto
qed      
      
(* Cormen 26.19 *) 
lemma excess_imp_source_path: 
  assumes "excess u > 0"
  obtains p where "cf.isSimplePath u p s"
  sorry  

end    
   
locale Height_Bounded_Labeling = Labeling +
  assumes height_bound: "\<forall>u\<in>V. l u \<le> 2*card V - 1"
begin    
  
end  
  
lemma (in Network) pp_init_height_bound: "Height_Bounded_Labeling c s t pp_init_f pp_init_l"
proof -
  interpret Labeling c s t pp_init_f pp_init_l by (rule pp_init_invar)
  show ?thesis by unfold_locales (auto simp: pp_init_l_def)  
qed    
    
(* TODO: Move *)  
lemma strengthen_SPEC': "m \<le> SPEC \<Phi> \<Longrightarrow> m \<le> SPEC(\<lambda>s. inres m s \<and> nofail m \<and> \<Phi> s)"
  -- "Strengthen SPEC by adding trivial upper bound for result"
  by (auto simp: pw_le_iff refine_pw_simps)
  
  
context Height_Bounded_Labeling
begin

(* Cormen 26.20 *)  
lemma relabel_pres_height_bound:
  assumes "relabel_precond u"
  shows "relabel u \<le> SPEC (\<lambda>(f',l'). f'=f \<and> l u < l' u \<and> Height_Bounded_Labeling c s t f l')"  
  apply (refine_vcg strengthen_SPEC'[OF relabel_invar[OF assms], THEN order_trans])  
  apply vc_solve
proof -    
  fix l'
  assume "Labeling c s t f l'"
  then interpret l': Labeling c s t f l' .

  assume "inres (relabel u) (f, l')" "nofail (relabel u)"   
  then obtain x where L'_EQ: "l' = l( u := x )"
    unfolding relabel_def by (auto simp: refine_pw_simps)
      
  from assms have "excess u > 0" unfolding relabel_precond_def by auto
  with l'.excess_imp_source_path obtain p where "cf.isSimplePath u p s" .
  have "l' u \<le> 2*card V - 1" sorry (* Extending valid-inequalities over path, which is length-bounded *)
  thus "Height_Bounded_Labeling c s t f l'" 
    apply unfold_locales
    using height_bound 
    by (auto simp: L'_EQ)
qed
  
(* Cormen 26.21 ... this limits the number of relabel operations. *)  
  
(* Cormen 26.22 ... also limits number of saturating pushes: Sat-push removes edge (u,v),
  and it can only be re-inserted by a push in the other direction, for which height of
  other node must increase, and, in turn, height of this node must increase before the
  next saturated push over this edge.
*)  
  
definition (in Labeling) "unsat_potential \<equiv> sum l {v. excess v > 0}"
  -- \<open>Sum of heights of all active nodes\<close>
  
lemma 
  assumes "unsat_push_precond (u,v)"
  shows "push (u,v) \<le> SPEC (\<lambda>(f',l'). l'=l \<and> unsat_potential < Labeling.unsat_potential c f' l)"  
  apply (rule strengthen_SPEC'[OF push_invar, THEN order_trans])
  unfolding unsat_push_alt[OF assms]
  subgoal using assms by (simp add: push_precond_eq_sat_or_unsat)
proof clarsimp    
  let ?f'="(augment_edge (u, v) (excess u))"
  assume "Labeling c s t ?f' l"
  then interpret l': Labeling c s t ?f' l .
  
  from assms have "(u,v) \<in> cf.E"    
    unfolding unsat_push_precond_def by auto
  hence UVE: "(u,v)\<in>E\<union>E\<inverse>" using cfE_ss_invE ..
      
  have "l'.excess u = 0"
    unfolding l'.excess_def
  proof -
    show "sum (augment_edge (u, v) (excess u)) (incoming u) 
          - sum (augment_edge (u, v) (excess u)) (outgoing u) = 0"
    proof (cases "(u,v)\<in>E")  
      case True hence UV_ONI:"(u,v)\<in>outgoing u - incoming u"
        by (auto simp: incoming_def outgoing_def no_self_loop)
      have 1: "sum (augment_edge (u, v) (excess u)) (incoming u) = sum f (incoming u)"    
        apply (rule sum.cong[OF refl])
        using True UV_ONI
        apply (subst augment_edge_other)
        by auto  
          
      have "sum (augment_edge (u, v) (excess u)) (outgoing u) 
        = sum f (outgoing u) + (\<Sum>x\<in>outgoing u. if x = (u, v) then excess u else 0)"     
        by (auto simp: augment_edge_def True sum.distrib[symmetric] intro: sum.cong)
      also have "\<dots> = sum f (outgoing u) + excess u" using UV_ONI by (auto simp: sum.delta)
      finally show ?thesis using 1 unfolding excess_def by simp 
    next  
      xxx, ctd here: Symmetric case ...
          
          
         
         apply (auto cong: sum.cong)
        thm sum.cong  
        thm augment_edge_other
          
          
      thus ?thesis using True
        unfolding augment_edge_def
        apply auto  
      
      
    apply (simp add: augment_edge_def)
      
oops      
    unfolding augment_edge_def  
    using UVE no_parallel_edge 
    apply auto  
    subgoal
      unfolding excess_def l'.excess_def
      
    apply (clarsimp split!: if_split)  
      
    apply (auto dest: no_parallel_edge UVE)
      
      
  
    
oops
  
Show 
  * termination
  
  
  
    
    
end
