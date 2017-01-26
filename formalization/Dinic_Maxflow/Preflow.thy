theory Preflow
imports Ford_Fulkerson
  Refine_Add_Fofu
  Refine_Monadic_Syntax_Sugar
begin
     
context Network begin
  
abbreviation "cf_of \<equiv> residualGraph c"
abbreviation "cfE_of f \<equiv> Graph.E (cf_of f)"

end
  
locale Labeling = NPreflow +
  fixes l :: "node \<Rightarrow> nat"
  assumes valid: "(u,v) \<in> cf.E \<Longrightarrow> l(u) \<le> l(v) + 1"
  assumes lab_src[simp]: "l s = card V"
  assumes lab_sink[simp]: "l t = 0"
begin
  text \<open>Generalizing validity to paths\<close>
  lemma gen_valid: "l(u) \<le> l(x) + length p" if "cf.isPath u p x"
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

  
definition augment_edge :: "'capacity flow \<Rightarrow> _" where "augment_edge f \<equiv> \<lambda>(u,v) \<Delta>. 
  if (u,v)\<in>E then f( (u,v) := f (u,v) + \<Delta> )
  else if (v,u)\<in>E then f( (v,u) := f (v,u) - \<Delta> )
  else f"
  
lemma augment_edge_zero[simp]: "augment_edge f e 0 = f" 
  unfolding augment_edge_def by (auto split: prod.split) 
    
lemma augment_edge_same[simp]: "e\<in>E \<Longrightarrow> augment_edge f e \<Delta> e = f e + \<Delta>"
  unfolding augment_edge_def by (auto split!: prod.splits)
    
lemma augment_edge_other[simp]:"\<lbrakk>e\<in>E; e'\<noteq>e \<rbrakk> \<Longrightarrow> augment_edge f e \<Delta> e' = f e'"    
  unfolding augment_edge_def by (auto split!: prod.splits)

lemma augment_edge_rev_same[simp]: "(v,u)\<in>E \<Longrightarrow> augment_edge f (u,v) \<Delta> (v,u) = f (v,u) - \<Delta>"    
  using no_parallel_edge
  unfolding augment_edge_def by (auto split!: prod.splits)

lemma augment_edge_rev_other[simp]: "\<lbrakk>(u,v)\<notin>E; e'\<noteq>(v,u)\<rbrakk> \<Longrightarrow> augment_edge f (u,v) \<Delta> e' = f e'"    
  unfolding augment_edge_def by (auto split!: prod.splits)
    
end -- \<open>Network\<close>  
  
context NPreflow begin  

lemma augment_edge_preflow_preserve: 
  "\<lbrakk>0\<le>\<Delta>; \<Delta> \<le> cf (u,v); \<Delta> \<le> excess f u\<rbrakk> \<Longrightarrow> Preflow c s t (augment_edge f (u,v) \<Delta>)"  
  apply unfold_locales
  subgoal
    unfolding residualGraph_def augment_edge_def  
    using capacity_const
    by (fastforce split!: if_splits)
  subgoal
  proof (intro ballI; clarsimp)
    assume "0\<le>\<Delta>" "\<Delta> \<le> cf (u,v)" "\<Delta> \<le> excess f u"
    fix v'
    assume V': "v'\<in>V" "v'\<noteq>s" "v'\<noteq>t"  
      
    show "sum (augment_edge f (u, v) \<Delta>) (outgoing v')
            \<le> sum (augment_edge f (u, v) \<Delta>) (incoming v')"  
    proof (cases)
      assume "\<Delta> = 0"
      with no_deficient_nodes show ?thesis using V' by auto 
    next
      assume "\<Delta> \<noteq> 0" with \<open>0\<le>\<Delta>\<close> have "0<\<Delta>" by auto
      with \<open>\<Delta> \<le> cf (u,v)\<close> have "(u,v)\<in>cf.E" unfolding Graph.E_def by auto
          
      show ?thesis
      proof (cases)    
        assume [simp]: "(u,v)\<in>E"
        hence AE: "augment_edge f (u,v) \<Delta> = f ( (u,v) := f (u,v) + \<Delta> )"  
          unfolding augment_edge_def by auto
        have 1: "\<forall>e\<in>outgoing v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>u"
          using that unfolding outgoing_def AE by auto
        have 2: "\<forall>e\<in>incoming v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>v"
          using that unfolding incoming_def AE by auto

        from \<open>(u,v)\<in>E\<close> no_self_loop have "u\<noteq>v" by blast
            
        {
          assume "v' \<noteq> u" "v' \<noteq> v"
          with 1 2 V' no_deficient_nodes have ?thesis by auto
        } moreover {
          assume [simp]: "v'=v" 
          have "sum (augment_edge f (u, v) \<Delta>) (outgoing v') = sum f (outgoing v)"  
            using 1 \<open>u\<noteq>v\<close> V' by auto
          also have "\<dots> \<le> sum f (incoming v)" using V' no_deficient_nodes by auto
          also have "\<dots> \<le> sum (augment_edge f (u, v) \<Delta>) (incoming v)"
            apply (rule sum_mono)
            using \<open>0\<le>\<Delta>\<close>
            by (auto simp: incoming_def augment_edge_def split!: if_split)
          finally have ?thesis by simp
        } moreover {
          assume [simp]: "v'=u"
          have A1: "sum (augment_edge f (u,v) \<Delta>) (incoming v') = sum f (incoming u)"  
            using 2 \<open>u\<noteq>v\<close> by auto
          have "(u,v) \<in> outgoing u" using \<open>(u,v)\<in>E\<close> by (auto simp: outgoing_def)
          note AUX = sum.remove[OF _ this, simplified]
          have A2: "sum (augment_edge f (u,v) \<Delta>) (outgoing u) = sum f (outgoing u) + \<Delta>"
            using AUX[of "augment_edge f (u,v) \<Delta>"] AUX[of "f"] by auto
          from A1 A2 \<open>\<Delta> \<le> excess f u\<close> no_deficient_nodes V' have ?thesis 
            unfolding excess_def by auto
        } ultimately show ?thesis by blast
      next
        assume [simp]: \<open>(u,v)\<notin>E\<close> 
        hence [simp]: "(v,u)\<in>E" using cfE_ss_invE \<open>(u,v)\<in>cf.E\<close> by auto
        from \<open>(u,v)\<notin>E\<close> \<open>(v,u)\<in>E\<close> have "u\<noteq>v" by blast
        
        have AE: "augment_edge f (u,v) \<Delta> = f ( (v,u) := f (v,u) - \<Delta> )"  
          unfolding augment_edge_def by simp
        have 1: "\<forall>e\<in>outgoing v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>v"
          using that unfolding outgoing_def AE by auto
        have 2: "\<forall>e\<in>incoming v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>u"
          using that unfolding incoming_def AE by auto

        {
          assume "v' \<noteq> u" "v' \<noteq> v"
          with 1 2 V' no_deficient_nodes have ?thesis by auto
        } moreover {
          assume [simp]: "v'=u" 
          have A1: "sum (augment_edge f (u, v) \<Delta>) (outgoing v') = sum f (outgoing u)"  
            using 1 \<open>u\<noteq>v\<close> V' by auto
              
          have "(v,u) \<in> incoming u" using \<open>(v,u)\<in>E\<close> by (auto simp: incoming_def)
          note AUX = sum.remove[OF _ this, simplified]    
          have A2: "sum (augment_edge f (u,v) \<Delta>) (incoming u) = sum f (incoming u) - \<Delta>"
            using AUX[of "augment_edge f (u,v) \<Delta>"] AUX[of "f"] by auto
              
          from A1 A2 \<open>\<Delta> \<le> excess f u\<close> no_deficient_nodes V' have ?thesis 
            unfolding excess_def by auto
        } moreover {
          assume [simp]: "v'=v"
          have "sum (augment_edge f (u,v) \<Delta>) (outgoing v') \<le> sum f (outgoing v')"  
            apply (rule sum_mono)
            using \<open>0<\<Delta>\<close>  
            by (auto simp: augment_edge_def)  
          also have "\<dots> \<le> sum f (incoming v)" using no_deficient_nodes V' by auto
          also have "\<dots> \<le> sum (augment_edge f (u,v) \<Delta>) (incoming v')"    
            using 2 \<open>u\<noteq>v\<close> by auto
          finally have ?thesis by simp
        } ultimately show ?thesis by blast
      qed      
    qed              
  qed          
  done            

lemma augment_edge_cf[simp]: "(u,v)\<in>cf.E \<Longrightarrow> 
  cf_of (augment_edge f (u,v) \<Delta>) = (cf)( (u,v) := cf (u,v) - \<Delta>, (v,u) := cf (v,u) + \<Delta>)"    
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
  
context Network begin  
definition "push_precond f l \<equiv> \<lambda>(u,v). excess f u > 0 \<and> (u,v)\<in>cfE_of f \<and> l u = l v + 1"
  -- \<open>Admissible edge from active node\<close>
  
definition "push_effect f \<equiv> \<lambda>(u,v). augment_edge f (u,v) (min (excess f u) (cf_of f (u,v)))"

(* Saturating and non-saturating pushes *)    
definition "sat_push_precond f l \<equiv> \<lambda>(u,v). excess f u > 0 \<and> excess f u \<ge> cf_of f (u,v) \<and> (u,v)\<in>cfE_of f \<and> l u = l v + 1"
definition "unsat_push_precond f l \<equiv> \<lambda>(u,v). excess f u > 0 \<and> excess f u < cf_of f (u,v) \<and> (u,v)\<in>cfE_of f \<and> l u = l v + 1"

lemma push_precond_eq_sat_or_unsat: "push_precond f l e \<longleftrightarrow> sat_push_precond f l e \<or> unsat_push_precond f l e"  
  unfolding push_precond_def sat_push_precond_def unsat_push_precond_def
  by auto  
  
lemma sat_unsat_push_disj: 
  "sat_push_precond f l e \<Longrightarrow> \<not>unsat_push_precond f l e"
  "unsat_push_precond f l e \<Longrightarrow> \<not>sat_push_precond f l e"
  unfolding sat_push_precond_def unsat_push_precond_def
  by auto  
  
lemma sat_push_alt: "sat_push_precond f l e \<Longrightarrow> push_effect f e = augment_edge f e (cf_of f e)"
  unfolding push_effect_def push_precond_eq_sat_or_unsat sat_push_precond_def 
  by (auto simp: min_absorb2)
    
lemma unsat_push_alt: "unsat_push_precond f l (u,v) \<Longrightarrow> push_effect f (u,v) = augment_edge f (u,v) (excess f u)"    
  unfolding push_effect_def push_precond_eq_sat_or_unsat unsat_push_precond_def 
  by (auto simp: min_absorb1)
  
(* Relabel *)    
definition "relabel_precond f l u \<equiv> u\<noteq>t \<and> excess f u > 0 \<and> (\<forall>v. (u,v)\<in>cfE_of f \<longrightarrow> l u \<noteq> l v + 1)"    
  -- \<open>Active, non-sink node without any admissible edges.\<close>

definition "relabel_effect f l u \<equiv> l( u := Min { l v | v. (u,v)\<in>cfE_of f } + 1 )"
    
end  
  
context Labeling begin  

  
lemma cfE_augment_ss:
  assumes EDGE: "(u,v)\<in>cf.E"  
  shows "cfE_of (augment_edge f (u,v) \<Delta>) \<subseteq> insert (v,u) cf.E"
  using EDGE  
  apply (clarsimp)
  unfolding Graph.E_def  
  apply (auto split: if_splits)  
  done

lemma push_pres_Labeling:
  assumes "push_precond f l e"
  shows "Labeling c s t (push_effect f e) l"
  unfolding push_effect_def  
proof (cases e; clarsimp)    
  fix u v
  assume [simp]: "e=(u,v)"
  let ?f' = "(augment_edge f (u, v) (min (excess f u) (cf (u, v))))"
    
  from assms have   
    ACTIVE: "excess f u > 0"
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
    

    
    
lemma active_has_cf_outgoing: "excess f u > 0 \<Longrightarrow> cf.outgoing u \<noteq> {}"  
  unfolding excess_def
proof -
  assume "0 < sum f (incoming u) - sum f (outgoing u)"
  hence "0 < sum f (incoming u)"
    by (metis diff_gt_0_iff_gt linorder_neqE_linordered_idom linorder_not_le sum_f_non_negative)
  then obtain v where "(v,u)\<in>E" "f (v,u) > 0"
    by (metis (no_types, lifting) f_non_negative le_neq_trans not_less sum.neutral sum_incoming_pointwise zero_flow_simp)
  hence "cf (u,v) > 0" unfolding residualGraph_def by auto
  thus ?thesis unfolding cf.outgoing_def cf.E_def by fastforce   
qed      
  
  
lemma 
  assumes PRE: "relabel_precond f l u"
  shows relabel_increase_u: "relabel_effect f l u u > l u" (is ?G1)
    and relabel_pres_Labeling: "Labeling c s t f (relabel_effect f l u)" (is ?G2)
proof -
  from PRE have  
        NOT_SINK: "u\<noteq>t"
    and ACTIVE: "excess f u > 0"
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
  ultimately show ?G1 ?G2
    unfolding relabel_effect_def
    apply (clarsimp_all simp: PRE)
    subgoal using LU_INCR by (simp add: less_Suc_eq_le)
    apply (unfold_locales)
    subgoal for u' v' using valid by auto
    subgoal by auto    
    subgoal using NOT_SINK by auto
    done
qed      

lemma relabel_preserve_other: "u\<noteq>v \<Longrightarrow> relabel_effect f l u v = l v" 
  unfolding relabel_effect_def by auto
  
lemma push_relabel_term_imp_maxflow:
  assumes no_push: "\<forall>(u,v)\<in>cf.E. \<not>push_precond f l (u,v)"
  assumes no_relabel: "\<forall>u. \<not>relabel_precond f l u"
  shows "isMaxFlow f"  
proof -
  from assms have "\<forall>u\<in>V-{t}. excess f u \<le> 0"
    unfolding push_precond_def relabel_precond_def
    by force 
  with excess_non_negative have "\<forall>u\<in>V-{s,t}. excess f u = 0" by force
  then interpret NFlow 
    apply unfold_locales 
    using no_deficient_nodes unfolding excess_def by auto
  from noAugPath_iff_maxFlow no_augmenting_path show "isMaxFlow f" by auto
qed      
      
(* Cormen 26.19 *) 
lemma excess_imp_source_path: 
  assumes "excess f u > 0"
  obtains p where "cf.isSimplePath u p s"
proof -
  obtain U where U_def: "U = {v|p v. cf.isSimplePath u p v}" by blast
  have fct1: "U \<subseteq> V"
  proof 
    fix v
    assume "v \<in> U"
    then have "(u, v) \<in> cf.E\<^sup>*" using U_def cf.isSimplePath_def cf.isPath_rtc by auto
    then obtain u' where "u = v \<or> ((u, u') \<in> cf.E\<^sup>* \<and> (u', v) \<in> cf.E)" by (meson rtranclE)
    thus "v \<in> V"
    proof
      assume "u = v"
      thus ?thesis using excess_nodes_only[OF assms] by blast
    next
      assume "(u, u') \<in> cf.E\<^sup>* \<and> (u', v) \<in> cf.E"
      then have "v \<in> cf.V" unfolding cf.V_def by blast
      thus ?thesis by simp
    qed
  qed 
    
  have "s \<in> U"
  proof(rule ccontr)
    assume "s \<notin> U"
    obtain U' where U'_def: "U' = V - U" by blast
    
    have "(\<Sum>u\<in>U. excess f u) = (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) - (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v)))"
    proof -
      have "(\<Sum>u\<in>U. excess f u) = (\<Sum>u\<in>U. (\<Sum>v\<in>incoming u. f v)) - (\<Sum>u\<in>U.(\<Sum>v\<in>outgoing u. f v))"
        (is "_ = ?R1 - ?R2") unfolding excess_def by (simp add: sum_subtractf)
      also have "?R1 = (\<Sum>u\<in>U. (\<Sum>v\<in>V. f (v, u)))" 
        using sum_incoming_alt_flow fct1 by (meson subsetCE sum.cong)
      also have "\<dots> = (\<Sum>u\<in>U. (\<Sum>v\<in>U. f (v, u))) + (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u)))"
      proof -
        have "(\<Sum>v\<in>V. f (v, u)) = (\<Sum>v\<in>U. f (v, u)) + (\<Sum>v\<in>U'. f (v, u))" for u
          using U'_def fct1 finite_V by (metis ab_semigroup_add_class.add.commute sum_subset_split)
        thus ?thesis by (simp add: sum.distrib)
      qed
      also have "?R2 = (\<Sum>u\<in>U. (\<Sum>v\<in>V. f (u, v)))" 
        using sum_outgoing_alt_flow fct1 by (meson subsetCE sum.cong)
      also have "\<dots> = (\<Sum>u\<in>U. (\<Sum>v\<in>U. f (u, v))) + (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v)))"
      proof -
        have "(\<Sum>v\<in>V. f (u, v)) = (\<Sum>v\<in>U. f (u, v)) + (\<Sum>v\<in>U'. f (u, v))" for u
          using U'_def fct1 finite_V by (metis ab_semigroup_add_class.add.commute sum_subset_split)
        thus ?thesis by (simp add: sum.distrib)
      qed
      also have "(\<Sum>u\<in>U. (\<Sum>v\<in>U. f (u, v))) = (\<Sum>u\<in>U. (\<Sum>v\<in>U. f (v, u)))"
      proof -
        {
          fix A :: "nat set"
          assume "finite A"
          then have "(\<Sum>u\<in>A. (\<Sum>v\<in>A. f (u, v))) = (\<Sum>u\<in>A. (\<Sum>v\<in>A. f (v, u)))"
          proof (induction "card A" arbitrary: A)
            case 0
            then show ?case by auto
          next
            case (Suc x)
            then obtain A' a where o1:"A = insert a A'" and o2:"x = card A'" and o3:"finite A'"
              by (metis card_insert_disjoint card_le_Suc_iff le_refl nat.inject)
            then have lm:"(\<Sum>e\<in>A. g e) = (\<Sum>e\<in>A'. g e) + g a" for g :: "nat \<Rightarrow> 'a"  using Suc.hyps(2)
              by (metis card_insert_if n_not_Suc_n semiring_normalization_rules(24) sum.insert)

            have "(\<Sum>u\<in>A. (\<Sum>v\<in>A. f (u, v))) = (\<Sum>u\<in>A'. (\<Sum>v\<in>A. f (u, v))) + (\<Sum>v\<in>A. f (a, v))"
              (is "_ = ?R1 + ?R2") using lm by auto     
            also have "?R1 = (\<Sum>u\<in>A'. (\<Sum>v\<in>A'. f (u, v))) + (\<Sum>u\<in>A'. f(u, a))" 
              (is "_ = ?R1_1 + ?R1_2") using lm sum.distrib by force
            also note add.assoc
            also have "?R1_2 + ?R2 = (\<Sum>u\<in>A'. f(a, u)) + (\<Sum>v\<in>A. f(v, a))"
              (is "_ = ?R1_2' + ?R2'") using lm by auto    
            also have "?R1_1 = (\<Sum>u\<in>A'. (\<Sum>v\<in>A'. f (v, u)))" 
              (is "_ = ?R1_1'") using Suc.hyps(1)[of A'] o2 o3 by auto
            also note add.assoc[symmetric]
            also have "?R1_1' + ?R1_2' = (\<Sum>u\<in>A'. (\<Sum>v\<in>A. f (v, u)))"
              by (metis (no_types, lifting) lm sum.cong sum.distrib)
            finally show ?case using lm[symmetric] by auto
          qed
        } note this[of U]
        thus ?thesis using fct1 finite_V finite_subset by auto
      qed
      finally show ?thesis by arith
    qed
    moreover have "(\<Sum>u\<in>U. excess f u) > 0"
    proof -
      have "u \<in> U" using U_def by simp
      moreover have "u \<in> U \<Longrightarrow> excess f u \<ge> 0" for u using fct1 excess_non_negative' `s \<notin> U` by auto
      ultimately show ?thesis using assms fct1 finite_V
        by (metis Diff_cancel Diff_eq_empty_iff Diff_infinite_finite finite_Diff sum_pos2)
    qed
    ultimately have fct2: "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) - (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v))) > 0" by simp
    
    have fct3: "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) > 0"
    proof -
      have "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) \<ge> 0" using capacity_const by (simp add: sum_nonneg)
      moreover have "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v))) \<ge> 0" using capacity_const by (simp add: sum_nonneg)
      ultimately show ?thesis using fct2 by simp
    qed
      
    have "\<exists>u' v'. (u' \<in> U \<and> v' \<in> U' \<and> f (v', u') > 0)"
    proof(rule ccontr)
      assume "\<not> (\<exists>u' v'. u' \<in> U \<and> v' \<in> U' \<and> f (v', u') > 0)"
      then have "(\<forall>u' v'. (u' \<in> U \<and> v' \<in> U' \<longrightarrow> f (v', u') = 0))"
        using capacity_const by (metis le_neq_trans)
      thus False using fct3 by simp
    qed
    then obtain u' v' where "u' \<in> U" and "v' \<in> U'" and "f (v', u') > 0" by blast
    
    obtain p1 where "cf.isSimplePath u p1 u'" using U_def `u' \<in> U` by auto
    moreover have "(u', v') \<in> cf.E"
    proof -
      have "(v', u') \<in> E" using capacity_const `f (v', u') > 0` by (metis not_less zero_flow_simp)
      then have "cf (u', v') > 0" unfolding cf_def 
        using no_parallel_edge `f (v', u') > 0` by (auto split: if_split)
      thus ?thesis unfolding cf.E_def by simp
    qed
    ultimately have "cf.isPath u (p1 @ [(u', v')]) v'" 
      using Graph.isPath_append_edge Graph.isSimplePath_def by blast
    then obtain p2 where "cf.isSimplePath u p2 v'" using cf.isSPath_pathLE by blast
    then have "v' \<in> U" using U_def by auto
    thus False using `v' \<in> U'` and U'_def by simp
  qed
  then obtain p' where "cf.isSimplePath u p' s" using U_def by auto
  thus ?thesis ..
qed


  
  
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
  
text \<open>Locale to relate original flow and flow where one edge was augmented.
  We already must have proven that we preserve a valid Labeling.
\<close>
locale augment_edge_locale =
  Labeling c s t f l + l': Labeling c s t "augment_edge f (u, v) \<Delta>" l
  for c s t f l u v \<Delta> +
  assumes uv_cf_edge: "(u,v)\<in>cf.E"
begin  
  abbreviation "f' \<equiv> augment_edge f (u, v) \<Delta>"
  
  lemma uv_edge_cases:
    obtains (par) "(u,v)\<in>E" "(v,u)\<notin>E" | (rev) "(v,u)\<in>E" "(u,v)\<notin>E"
    using uv_cf_edge cfE_ss_invE no_parallel_edge by blast  
  
  lemma excess'_u[simp]: "excess f' u = excess f u - \<Delta>"
    unfolding excess_def[where f=f']
  proof -
    show "sum f' (incoming u) - sum f' (outgoing u) = excess f u - \<Delta>"
    proof (cases rule: uv_edge_cases)  
      case [simp]: par 
      hence UV_ONI:"(u,v)\<in>outgoing u - incoming u"
        by (auto simp: incoming_def outgoing_def no_self_loop)
      have 1: "sum f' (incoming u) = sum f (incoming u)"    
        apply (rule sum.cong[OF refl])
        using UV_ONI
        apply (subst augment_edge_other)
        by auto  
          
      have "sum f' (outgoing u) 
        = sum f (outgoing u) + (\<Sum>x\<in>outgoing u. if x = (u, v) then \<Delta> else 0)"     
        by (auto simp: augment_edge_def sum.distrib[symmetric] intro: sum.cong)
      also have "\<dots> = sum f (outgoing u) + \<Delta>" using UV_ONI by (auto simp: sum.delta)
      finally show ?thesis using 1 unfolding excess_def by simp 
    next  
      case [simp]: rev 
      have UV_INO:"(v,u)\<in>incoming u - outgoing u"
        by (auto simp: incoming_def outgoing_def no_self_loop)
      have 1: "sum f' (outgoing u) = sum f (outgoing u)"    
        apply (rule sum.cong[OF refl])
        using UV_INO
        apply (subst augment_edge_rev_other)  
        by (auto)
      have "sum f' (incoming u) 
        = sum f (incoming u) + (\<Sum>x\<in>incoming u. if x = (v, u) then - \<Delta> else 0)"
        by (auto simp: sum.distrib[symmetric] augment_edge_def intro: sum.cong)
      also have "\<dots> = sum f (incoming u) - \<Delta>"  
        using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 unfolding excess_def by auto
    qed      
  qed
    
  lemma excess'_v[simp]: "excess f' v = excess f v + \<Delta>"
    unfolding excess_def[where f=f']
  proof -    
    show "sum f' (incoming v) - sum f' (outgoing v) = excess f v + \<Delta>"
    proof (cases rule: uv_edge_cases)
      case [simp]: par 
      have UV_INO: "(u,v)\<in>incoming v - outgoing v"
        unfolding incoming_def outgoing_def by (auto simp: no_self_loop)
      have 1: "sum f' (outgoing v) = sum f (outgoing v)"    
        using UV_INO
        by (auto simp: augment_edge_def intro: sum.cong)
          
      have "sum f' (incoming v) 
        = sum f (incoming v) + (\<Sum>x\<in>incoming v. if x=(u,v) then \<Delta> else 0)"    
        using UV_INO
        by (auto simp: augment_edge_def sum.distrib[symmetric] intro: sum.cong)
      also have "\<dots> = sum f (incoming v) + \<Delta>" using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 by (auto simp: excess_def)
    next
      case [simp]: rev
      have UV_INO:"(v,u)\<in>outgoing v - incoming v"
        by (auto simp: incoming_def outgoing_def no_self_loop)

      have 1: "sum f' (incoming v) = sum f (incoming v)"
        using UV_INO
        by (auto simp: augment_edge_def intro: sum.cong)
          
      have "sum f' (outgoing v) 
        = sum f (outgoing v) + (\<Sum>x\<in>outgoing v. if x=(v,u) then - \<Delta> else 0)"    
        using UV_INO
        by (auto simp: augment_edge_def sum.distrib[symmetric] intro: sum.cong)
      also have "\<dots> = sum f (outgoing v) - \<Delta>" using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 by (auto simp: excess_def)
    qed
  qed  
    
  lemma excess'_other[simp]:
    assumes "x \<noteq> u" "x \<noteq> v"  
    shows "excess f' x = excess f x"
  proof -
    have NE: "(u,v)\<notin>incoming x" "(u,v)\<notin>outgoing x"
          "(v,u)\<notin>incoming x" "(v,u)\<notin>outgoing x"
      using assms unfolding incoming_def outgoing_def by auto
    have 
      "sum f' (outgoing x) = sum f (outgoing x)"
      "sum f' (incoming x) = sum f (incoming x)"
      by (auto simp: augment_edge_def NE split!: if_split intro: sum.cong)  
    thus ?thesis    
      unfolding excess_def by auto
  qed      

  lemma excess'_if: 
    "excess f' x = (if x=u then excess f u - \<Delta> else if x=v then excess f v + \<Delta> else excess f x)"  
    by simp
    
    
end    
    
context Height_Bounded_Labeling
begin

(* Cormen 26.20 *)  
lemma relabel_pres_height_bound:
  assumes "relabel_precond f l u"
  shows "Height_Bounded_Labeling c s t f (relabel_effect f l u)"
proof -
  let ?l' = "relabel_effect f l u"
  
  from relabel_pres_Labeling[OF assms]  
  interpret l': Labeling c s t f ?l' .
  
  from assms have "excess f u > 0" unfolding relabel_precond_def by auto
  with l'.excess_imp_source_path obtain p where p_obt: "cf.isSimplePath u p s" .
  
  have "u \<in> V" using excess_nodes_only `excess f u > 0` .
  then have "length p < card V" using cf.simplePath_length_less_V[of u p] p_obt by auto
  moreover have "?l' u \<le> ?l' s + length p" using p_obt l'.gen_valid[of u p s] p_obt 
    unfolding cf.isSimplePath_def by auto
  moreover have "?l' s = card V" using l'.Labeling_axioms Labeling_def Labeling_axioms_def by auto
  ultimately have "?l' u \<le> 2*card V - 1" by auto
  thus "Height_Bounded_Labeling c s t f ?l'" 
    apply unfold_locales
    using height_bound relabel_preserve_other
    by metis  
qed      
  
(* Cormen 26.21 ... this limits the number of relabel operations. *)  
  
(* Cormen 26.22 ... also limits number of saturating pushes: Sat-push removes edge (u,v),
  and it can only be re-inserted by a push in the other direction, for which height of
  other node must increase, and, in turn, height of this node must increase before the
  next saturated push over this edge.
*)  

definition (in Network) "unsat_potential f l \<equiv> sum l {v\<in>V. excess f v > 0}"
  -- \<open>Sum of heights of all active nodes\<close>
  
lemma unsat_push_decr_unsat_potential:
  assumes "unsat_push_precond f l e"
  shows "unsat_potential (push_effect f e) l < unsat_potential f l"  
proof (cases e)
  case [simp]: (Pair u v)
  then show ?thesis
    using assms 
  proof (simp add: unsat_push_alt)
    let ?f'="(augment_edge f (u, v) (excess f u))"
    from push_pres_Labeling[of e] assms push_precond_eq_sat_or_unsat[of f l e] unsat_push_alt[of f l u v]
    interpret l': Labeling c s t ?f' l by auto
    
    from assms have UVCFE: "(u,v) \<in> cf.E" and [simp]: "l u = l v + 1" and XU: "0 < excess f u"
      unfolding unsat_push_precond_def by auto
        
    interpret augment_edge_locale c s t f l u v "excess f u" 
      apply unfold_locales using UVCFE by auto
  
    have [simp]: "u\<in>V" "v\<in>V" "u\<noteq>v" "v\<noteq>u"
      using UVCFE E_ss_VxV cfE_ss_invE no_parallel_edge by auto
    from XU have [simp]: "u\<noteq>s" using excess_s_non_pos by auto    
  
    define S where "S={x\<in>V. x\<noteq>u \<and> x\<noteq>v \<and> 0<excess f x}"
    have S_alt: "S = {x\<in>V. x\<noteq>u \<and> x\<noteq>v \<and> 0<excess ?f' x}"  
      unfolding S_def by auto
  
    have NES: "s\<notin>S" "u\<notin>S" "v\<notin>S" 
      and [simp, intro!]: "finite S" 
      unfolding S_def using excess_s_non_pos
      by auto 
  
    have 1: "{v\<in>V. 0 < excess ?f' v} = (if s=v then S else insert v S)"
      unfolding S_alt
      using XU excess_non_negative' l'.excess_s_non_pos
      by (auto intro!: add_nonneg_pos)
        
    have 2: "{v\<in>V. 0 < excess f v} 
      = insert u S \<union> (if excess f v>0 then {v} else {})"    
      unfolding S_def using XU by auto  
  
    show "unsat_potential ?f' l < unsat_potential f l"
      unfolding unsat_potential_def 1 2
      by (cases "s=v"; cases "0<excess f v"; auto simp: NES)
  qed      
qed
end -- \<open>Height bound labeling\<close>
  
context Network begin  
  definition adm_edges :: "'capacity flow \<Rightarrow> (nat\<Rightarrow>nat) \<Rightarrow> _" 
    where "adm_edges f l \<equiv> {(u,v)\<in>cfE_of f. l u = l v + 1}"
    
  lemma adm_edges_inv_disj: "adm_edges f l \<inter> (adm_edges f l)\<inverse> = {}"
    unfolding adm_edges_def by auto
  
  (* TODO: Move, should make some lemma about Preflow.cf redundant *)    
  lemma cfE_of_ss_VxV: "cfE_of f \<subseteq> V\<times>V"
    unfolding V_def
    unfolding residualGraph_def Graph.E_def
    by auto  

  lemma cfE_of_finite[simp, intro!]: "finite (cfE_of f)"
    using finite_subset[OF cfE_of_ss_VxV] by auto
      
  lemma finite_adm_edges[simp, intro!]: "finite (adm_edges f l)"
    apply (rule finite_subset[of _ "cfE_of f"])
    by (auto simp: adm_edges_def)
      
      
end

(* TODO: Move *)  
lemma swap_in_iff_inv: "prod.swap p \<in> S \<longleftrightarrow> p \<in> S\<inverse>"
  apply (cases p) by auto
  
context Labeling begin  
  
lemma sat_push_decr_adm_edges:
  assumes "sat_push_precond f l e"
  shows "e\<in>adm_edges f l" "adm_edges (push_effect f e) l = adm_edges f l - {e}"
  unfolding sat_push_alt[OF assms]
proof -
  let ?f'="(augment_edge f e (cf e))"
  interpret l': Labeling c s t ?f' l 
    using push_pres_Labeling[of e] push_precond_eq_sat_or_unsat[of f l e] assms
    unfolding sat_push_alt[OF assms] by auto

  from assms show G1: "e\<in>adm_edges f l"    
    unfolding sat_push_precond_def adm_edges_def by auto
      
  have "l'.cf.E \<subseteq> insert (prod.swap e) cf.E - {e}" "l'.cf.E \<supseteq> cf.E - {e}"
    unfolding l'.cf_def cf_def
    unfolding augment_edge_def residualGraph_def Graph.E_def
    by (auto split!: if_splits prod.splits)
  hence "l'.cf.E = insert (prod.swap e) cf.E - {e} \<or> l'.cf.E = cf.E - {e}"
    by auto
  thus "adm_edges ?f' l = adm_edges f l - {e}" 
  proof (cases rule: disjE[consumes 1])
    case 1
    from assms have "e \<in> adm_edges f l" unfolding sat_push_precond_def adm_edges_def by auto
    with adm_edges_inv_disj have "prod.swap e \<notin> adm_edges f l" by (auto simp: swap_in_iff_inv)
    thus "adm_edges ?f' l = adm_edges f l - {e}" using G1
      unfolding adm_edges_def 1   
      by auto
  next
    case 2
    thus "adm_edges ?f' l = adm_edges f l - {e}" 
      unfolding adm_edges_def 2   
      by auto  
  qed
qed    
      
lemma unsat_push_pres_adm_edges:
  assumes "unsat_push_precond f l e"
  shows "adm_edges (push_effect f e) l = adm_edges f l"
  using assms  
proof (cases e; simp add: unsat_push_alt)
  fix u v assume [simp]: "e=(u,v)"
  
  let ?f'="(augment_edge f (u,v) (excess f u))"
  interpret l': Labeling c s t ?f' l 
    using push_pres_Labeling[of e] push_precond_eq_sat_or_unsat[of f l e] assms unsat_push_alt[of f l u v]
    by auto
  
  from assms have "e \<in> adm_edges f l" unfolding unsat_push_precond_def adm_edges_def by auto
  with adm_edges_inv_disj have AUX: "prod.swap e \<notin> adm_edges f l" by (auto simp: swap_in_iff_inv)
      
  from assms have 
    "excess f u < cf (u,v)" "0 < excess f u"
    and [simp]: "l u = l v + 1" 
    unfolding unsat_push_precond_def by auto
  hence "l'.cf.E \<subseteq> insert (prod.swap e) cf.E" "l'.cf.E \<supseteq> cf.E"
    unfolding l'.cf_def cf_def
    unfolding augment_edge_def residualGraph_def Graph.E_def
    apply (safe)
    apply (simp split: if_splits)  
    apply (simp split: if_splits)  
    subgoal
      by (metis (full_types) capacity_const diff_0_right diff_strict_left_mono not_less)  
    subgoal
      by (metis add_le_same_cancel1 f_non_negative linorder_not_le)  
    done    
  hence "l'.cf.E = insert (prod.swap e) cf.E \<or> l'.cf.E = cf.E"
    by auto
  thus "adm_edges ?f' l = adm_edges f l" using AUX
    unfolding adm_edges_def  
    by auto  
qed  

end -- \<open>Labeling\<close>  
  
(* Termination proof without complexity *)  
  
context Network begin  
definition "sum_heights_measure l \<equiv> \<Sum>v\<in>V. 2*card V - l v"
definition "card_adm_measure f l \<equiv> card (adm_edges f l)"
end  

context Height_Bounded_Labeling begin  

  lemma relabel_measure:
    assumes "relabel_precond f l u"
    shows "sum_heights_measure (relabel_effect f l u) < sum_heights_measure l"
  proof -
    let ?l' = "relabel_effect f l u"
    from relabel_pres_height_bound[OF assms] 
    interpret l': Height_Bounded_Labeling c s t f ?l' .
      
    from assms have "u\<in>V" 
      by (simp add: excess_nodes_only relabel_precond_def)
        
    hence V_split: "V = insert u V" by auto
        
    show ?thesis  
      using relabel_increase_u[OF assms] relabel_preserve_other[of u]
      using l'.height_bound 
      unfolding sum_heights_measure_def
      apply (rewrite at "\<Sum>_\<in>\<hole>. _" V_split)+
      apply (subst sum.insert_remove[OF finite_V])+
      using \<open>u\<in>V\<close>  
      by auto   
  qed        
  
  lemma sat_push_measure:  
    assumes "sat_push_precond f l e"
    shows "card_adm_measure (push_effect f e) l < card_adm_measure f l"  
    unfolding card_adm_measure_def 
    apply (rule psubset_card_mono)
    apply simp  
    using sat_push_decr_adm_edges[OF assms] 
    by auto  
      
  lemma unsat_push_measure:    
    assumes "unsat_push_precond f l e"
    shows "card_adm_measure (push_effect f e) l = card_adm_measure f l"
      and "unsat_potential (push_effect f e) l < unsat_potential f l"
    unfolding card_adm_measure_def  
    by (simp_all 
        add: unsat_push_decr_unsat_potential[OF assms] unsat_push_pres_adm_edges[OF assms])
      
end  
  
context Network begin  
inductive_set algo_rel where
  unsat_push: "\<lbrakk>Height_Bounded_Labeling c s t f l; unsat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((push_effect f e,l),(f,l))\<in>algo_rel"
| sat_push: "\<lbrakk>Height_Bounded_Labeling c s t f l; sat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((push_effect f e,l),(f,l))\<in>algo_rel"
| relabel: "\<lbrakk>Height_Bounded_Labeling c s t f l; relabel_precond f l u \<rbrakk>
    \<Longrightarrow> ((f,relabel_effect f l u),(f,l))\<in>algo_rel"

  
definition "term_f \<equiv> \<lambda>(f,l). (sum_heights_measure l, card_adm_measure f l, unsat_potential f l)"
  
lemma "wf algo_rel"  
proof -
  have "algo_rel \<subseteq> inv_image (less_than <*lex*> less_than <*lex*> less_than) term_f"
    unfolding term_f_def
    using Height_Bounded_Labeling.unsat_push_measure  
    using Height_Bounded_Labeling.sat_push_measure  
    using Height_Bounded_Labeling.relabel_measure  
    by (fastforce elim!: algo_rel.cases)
  thus ?thesis
    by (rule_tac wf_subset; auto)
qed  
  
  
  
end  
    
    
end
