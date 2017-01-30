theory Preflow
imports Ford_Fulkerson
  Refine_Add_Fofu
  Refine_Monadic_Syntax_Sugar
begin

(* TODO: Move *)  
context Graph begin  
definition "adjacent_nodes u \<equiv> E``{u} \<union> E\<inverse>``{u}"
end  
  
context Finite_Graph begin
lemma adjacent_nodes_finite[simp, intro!]: "finite (adjacent_nodes u)"
  unfolding adjacent_nodes_def by (auto intro: finite_Image)
end  
  
  
(* TODO: Move *)  
lemma swap_in_iff_inv: "prod.swap p \<in> S \<longleftrightarrow> p \<in> S\<inverse>"
  apply (cases p) by auto
  
  
(* TODO: Move *)  
lemma (in Network) card_V_ge2: "card V \<ge> 2"
proof -
  have "2 = card {s,t}" by auto
  also have "{s,t} \<subseteq> V" by auto
  hence "card {s,t} \<le> card V" by (rule_tac card_mono) auto
  finally show ?thesis .   
qed  
  
(* TODO: Move *)  
lemma strengthen_SPEC': "m \<le> SPEC \<Phi> \<Longrightarrow> m \<le> SPEC(\<lambda>s. inres m s \<and> nofail m \<and> \<Phi> s)"
  -- "Strengthen SPEC by adding trivial upper bound for result"
  by (auto simp: pw_le_iff refine_pw_simps)

    
(* TODO: Move *)  
context Network begin
  
abbreviation "cf_of \<equiv> residualGraph c"
abbreviation "cfE_of f \<equiv> Graph.E (cf_of f)"

(* TODO: Move, should make some lemma about Preflow.cf redundant *)    
lemma cfE_of_ss_VxV: "cfE_of f \<subseteq> V\<times>V"
  unfolding V_def
  unfolding residualGraph_def Graph.E_def
  by auto  

lemma cfE_of_finite[simp, intro!]: "finite (cfE_of f)"
  using finite_subset[OF cfE_of_ss_VxV] by auto

(* TODO: Move *)    
lemma cf_no_self_loop: "(u,u)\<notin>cfE_of f"
proof
  assume a1: "(u, u) \<in> cfE_of f"
  have "(u, u) \<notin> E"
    using no_parallel_edge by blast
  then show False
    using a1 unfolding Graph.E_def residualGraph_def by fastforce
qed 
  
    
    
end
    
  
  
  
(* Auxiliary Stuff *)  
  
(* Topological ordering of Graphs *)  
(* Topological ordering: TODO: Move*)  
  
definition "list_before_rel l \<equiv> { (a,b). \<exists>l1 l2 l3. l=l1@a#l2@b#l3 }"
lemma list_before_irrefl_eq_distinct: "irrefl (list_before_rel l) \<longleftrightarrow> distinct l"  
  using not_distinct_decomp[of l]
  by (auto simp: irrefl_def list_before_rel_def)
  
lemma list_before_rel_alt: "list_before_rel l = { (l!i, l!j) | i j. i<j \<and> j<length l }"
  unfolding list_before_rel_def
  apply (rule; clarsimp)
  subgoal for a b l1 l2 l3  
    apply (rule exI[of _ "length l1"]; simp)
    apply (rule exI[of _ "length l1 + Suc (length l2)"]; auto simp: nth_append)
    done      
  subgoal for i j
    apply (rule exI[of _ "take i l"])
    apply (rule exI[of _ "drop (Suc i) (take j l)"])
    apply (rule exI[of _ "drop (Suc j) l"])
    by (simp add: Cons_nth_drop_Suc drop_take_drop_unsplit)
  done      
    
lemma list_before_trans[trans]: "distinct l \<Longrightarrow> trans (list_before_rel l)" 
  by (clarsimp simp: trans_def list_before_rel_alt) (metis index_nth_id less_trans)    
    
lemma list_before_asym: "distinct l \<Longrightarrow> asym (list_before_rel l)"
  by (meson asym.intros irrefl_def list_before_irrefl_eq_distinct list_before_trans transE)
    
lemma list_before_rel_empty[simp]: "list_before_rel [] = {}"    
  unfolding list_before_rel_def by auto
    
lemma list_before_rel_cons: "list_before_rel (x#l) = ({x}\<times>set l) \<union> list_before_rel l"    
  apply (intro equalityI subsetI; simp add: split_paired_all)  
  subgoal for a b proof -
    assume "(a,b) \<in> list_before_rel (x # l)"  
    then obtain i j where IDX_BOUND: "i<j" "j<Suc (length l)" and [simp]: "a=(x#l)!i" "b=(x#l)!j" 
      unfolding list_before_rel_alt by auto

    {
      assume "i=0"
      hence "x=a" "b\<in>set l" using IDX_BOUND
        by (auto simp: nth_Cons split: nat.splits)
    } moreover {
      assume "i\<noteq>0"
      with IDX_BOUND have "a=l!(i-1)" "b=l!(j-1)" "i-1 < j-1" "j-1 < length l"
        by auto
      hence "(a, b) \<in> list_before_rel l" unfolding list_before_rel_alt by blast 
    } ultimately show ?thesis by blast
  qed
  subgoal premises prems for a b  
  proof -
    {
      assume [simp]: "a=x" and "b\<in>set l"
      then obtain j where "b = l!j" "j<length l" by (auto simp: in_set_conv_nth)
      hence "a=(x#l)!0" "b = (x#l)!Suc j" "0 < Suc j" "Suc j < length (x#l)" by auto
      hence ?thesis unfolding list_before_rel_alt by blast    
    } moreover {
      assume "(a, b) \<in> list_before_rel l"
      hence ?thesis unfolding list_before_rel_alt
        by clarsimp (metis Suc_mono nth_Cons_Suc)  
    } ultimately show ?thesis using prems by blast
  qed
  done  
  
lemma list_before_rel_on_elems: "list_before_rel l \<subseteq> set l \<times> set l" 
  unfolding list_before_rel_def by auto
    
    
definition "is_top_sorted R l \<equiv> list_before_rel l \<inter> (R\<^sup>*)\<inverse> = {}"  
lemma is_top_sorted_alt: "is_top_sorted R l \<longleftrightarrow> (\<forall>x y. (x,y)\<in>list_before_rel l \<longrightarrow> (y,x)\<notin>R\<^sup>*)"
  unfolding is_top_sorted_def by auto
  
lemma is_top_sorted_empty_rel[simp]: "is_top_sorted {} l \<longleftrightarrow> distinct l"
  by (auto simp: is_top_sorted_def list_before_irrefl_eq_distinct[symmetric] irrefl_def)

lemma is_top_sorted_empty_list[simp]: "is_top_sorted R []"
  by (auto simp: is_top_sorted_def)

lemma is_top_sorted_distinct: 
  assumes "is_top_sorted R l" 
  shows "distinct l"
proof (rule ccontr)  
  assume "\<not>distinct l"
  with list_before_irrefl_eq_distinct[of l] obtain x where "(x,x)\<in>(list_before_rel l)"
    by (auto simp: irrefl_def)
  with assms show False unfolding is_top_sorted_def by auto      
qed  
  
    
lemma is_top_sorted_cons: "is_top_sorted R (x#l) \<longleftrightarrow> ({x}\<times>set l \<inter> (R\<^sup>*)\<inverse> = {}) \<and> is_top_sorted R l"
  unfolding is_top_sorted_def
  by (auto simp: list_before_rel_cons)
    
lemma is_top_sorted_append: "is_top_sorted R (l1@l2) 
  \<longleftrightarrow> (set l1\<times>set l2 \<inter> (R\<^sup>*)\<inverse> = {}) \<and> is_top_sorted R l1 \<and> is_top_sorted R l2"    
  by (induction l1) (auto simp: is_top_sorted_cons)

lemma is_top_sorted_remove_elem: "is_top_sorted R (l1@x#l2) \<Longrightarrow> is_top_sorted R (l1@l2)"
  by (auto simp: is_top_sorted_cons is_top_sorted_append)
    
lemma is_top_sorted_antimono:
  assumes "R\<subseteq>R'"
  assumes "is_top_sorted R' l"
  shows "is_top_sorted R l"  
  using assms 
  unfolding is_top_sorted_alt  
  by (auto dest: rtrancl_mono_mp)

lemma is_top_sorted_isolated_constraint:
  assumes "R' \<subseteq> R \<union> {x}\<times>X" "R'\<inter>UNIV\<times>{x} = {}"
  assumes "x\<notin>set l"  
  assumes "is_top_sorted R l"  
  shows "is_top_sorted R' l"  
proof -
  {
    fix a b
    assume "(a,b)\<in>R'\<^sup>*" "a\<noteq>x" "b\<noteq>x"  
    hence "(a,b)\<in>R\<^sup>*"  
    proof (induction rule: converse_rtrancl_induct)
      case base
      then show ?case by simp
    next
      case (step y z)
      with assms(1,2) have "z\<noteq>x" "(y,z)\<in>R" by auto  
      with step show ?case by auto
    qed
  } note AUX=this
    
  show ?thesis
    using assms(3,4) AUX list_before_rel_on_elems 
    unfolding is_top_sorted_def by fastforce
qed  
  

(* Refinement Framework VCG control:
  Idea: Put a frame around stuff in the program where the VCG shall not look into
    on outermost pass, and discharge the frame's content with nested vcg call.
    Very useful with subgoal command, to set up some auxiliary context before
    discharging, e.g., interpret locales, etc.
 
*)  
(* TODO: Make this a generic technique:
  Problems: 
    * Splitter will split inside VCG_FRAME (e.g., ifs)

*)  
  
definition VCG_FRAME :: "_ nres \<Rightarrow> _ nres" where "VCG_FRAME m \<equiv> m"
lemma VCG_FRAME_cong[cong]: "VCG_FRAME x \<equiv> VCG_FRAME x" by simp

lemma vcg_intro_frame: "m \<equiv> VCG_FRAME m" unfolding VCG_FRAME_def by simp
lemma vcg_rem_frame: "m\<le>m' \<Longrightarrow> VCG_FRAME m \<le> m'" unfolding VCG_FRAME_def by simp
  
  
  
  
  
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

lemma push_precondI[intro?]: "\<lbrakk>excess f u > 0; (u,v)\<in>cfE_of f; l u = l v + 1\<rbrakk> \<Longrightarrow> push_precond f l (u,v)"
  unfolding push_precond_def by auto
  
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
  
lemma finite_min_cf_outgoing[simp, intro!]: "finite {l v |v. (u, v) \<in> cf.E}"    
proof -
  have "{l v |v. (u, v) \<in> cf.E} = l`snd`cf.outgoing u"
    by (auto simp: cf.outgoing_def)
  moreover have "finite (l`snd`cf.outgoing u)" by auto
  ultimately show ?thesis by auto
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

lemma no_excess_imp_maxflow:    
  assumes "\<forall>u\<in>V-{s,t}. excess f u = 0"
  shows "isMaxFlow f"  
proof -    
  from assms interpret NFlow 
    apply unfold_locales 
    using no_deficient_nodes unfolding excess_def by auto
  from noAugPath_iff_maxFlow no_augmenting_path show "isMaxFlow f" by auto
qed
  
lemma push_relabel_term_imp_maxflow:
  assumes no_push: "\<forall>(u,v)\<in>cf.E. \<not>push_precond f l (u,v)"
  assumes no_relabel: "\<forall>u. \<not>relabel_precond f l u"
  shows "isMaxFlow f"  
proof -
  from assms have "\<forall>u\<in>V-{t}. excess f u \<le> 0"
    unfolding push_precond_def relabel_precond_def
    by force 
  with excess_non_negative have "\<forall>u\<in>V-{s,t}. excess f u = 0" by force
  with no_excess_imp_maxflow show ?thesis . 
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
    
context Network begin  
  definition adm_edges :: "'capacity flow \<Rightarrow> (nat\<Rightarrow>nat) \<Rightarrow> _" 
    where "adm_edges f l \<equiv> {(u,v)\<in>cfE_of f. l u = l v + 1}"
    
  lemma adm_edges_inv_disj: "adm_edges f l \<inter> (adm_edges f l)\<inverse> = {}"
    unfolding adm_edges_def by auto
  
  lemma finite_adm_edges[simp, intro!]: "finite (adm_edges f l)"
    apply (rule finite_subset[of _ "cfE_of f"])
    by (auto simp: adm_edges_def)
      
      
end
    
    
    
text \<open>Locale to relate original flow and flow after a push.\<close>
locale push_effect_locale = Labeling +
  fixes u v
  assumes PRE: "push_precond f l (u,v)"
begin    
  abbreviation "f' \<equiv> push_effect f (u,v)"
  sublocale l': Labeling c s t f' l  
    using push_pres_Labeling[OF PRE] .
  
  lemma uv_cf_edge[simp, intro!]: "(u,v)\<in>cf.E" using PRE unfolding push_precond_def by auto
  lemma excess_u_pos: "excess f u > 0" using PRE unfolding push_precond_def by auto   
  lemma l_u_eq[simp]: "l u = l v + 1" using PRE unfolding push_precond_def by auto   

  lemma uv_adm: "(u,v)\<in>adm_edges f l" unfolding adm_edges_def by auto
      
  lemma uv_edge_cases:
    obtains (par) "(u,v)\<in>E" "(v,u)\<notin>E" | (rev) "(v,u)\<in>E" "(u,v)\<notin>E"
    using uv_cf_edge cfE_ss_invE no_parallel_edge by blast  

  lemma uv_nodes[simp, intro!]: "u\<in>V" "v\<in>V" 
    using E_ss_VxV cfE_ss_invE no_parallel_edge by auto
      
  lemma uv_not_eq[simp]: "u\<noteq>v" "v\<noteq>u"
    using E_ss_VxV cfE_ss_invE[THEN set_mp, OF uv_cf_edge] no_parallel_edge by auto

  definition "\<Delta> = min (excess f u) (cf_of f (u,v))"    
    
  lemma \<Delta>_positive: "\<Delta> > 0"  
    unfolding \<Delta>_def 
    using excess_u_pos uv_cf_edge[unfolded cf.E_def] resE_positive 
    by auto
      
  lemma f'_alt: "f' = augment_edge f (u,v) \<Delta>" unfolding push_effect_def \<Delta>_def by auto
      
  lemma unsat_push_\<Delta>: "unsat_push_precond f l (u,v) \<Longrightarrow> \<Delta> = excess f u"      
    unfolding \<Delta>_def unsat_push_precond_def by auto
  lemma sat_push_\<Delta>: "sat_push_precond f l (u,v) \<Longrightarrow> \<Delta> = cf (u,v)"      
    unfolding \<Delta>_def sat_push_precond_def by auto
      
      
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
        using UV_ONI unfolding f'_alt
        apply (subst augment_edge_other)
        by auto  
          
      have "sum f' (outgoing u) 
        = sum f (outgoing u) + (\<Sum>x\<in>outgoing u. if x = (u, v) then \<Delta> else 0)"     
        by (auto simp: f'_alt augment_edge_def sum.distrib[symmetric] intro: sum.cong)
      also have "\<dots> = sum f (outgoing u) + \<Delta>" using UV_ONI by (auto simp: sum.delta)
      finally show ?thesis using 1 unfolding excess_def by simp 
    next  
      case [simp]: rev 
      have UV_INO:"(v,u)\<in>incoming u - outgoing u"
        by (auto simp: incoming_def outgoing_def no_self_loop)
      have 1: "sum f' (outgoing u) = sum f (outgoing u)"    
        apply (rule sum.cong[OF refl])
        using UV_INO unfolding f'_alt
        apply (subst augment_edge_rev_other)  
        by (auto)
      have "sum f' (incoming u) 
        = sum f (incoming u) + (\<Sum>x\<in>incoming u. if x = (v, u) then - \<Delta> else 0)"
        by (auto simp: f'_alt sum.distrib[symmetric] augment_edge_def intro: sum.cong)
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
        using UV_INO unfolding f'_alt
        by (auto simp: augment_edge_def intro: sum.cong)
          
      have "sum f' (incoming v) 
        = sum f (incoming v) + (\<Sum>x\<in>incoming v. if x=(u,v) then \<Delta> else 0)"    
        using UV_INO unfolding f'_alt
        by (auto simp: augment_edge_def sum.distrib[symmetric] intro: sum.cong)
      also have "\<dots> = sum f (incoming v) + \<Delta>" using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 by (auto simp: excess_def)
    next
      case [simp]: rev
      have UV_INO:"(v,u)\<in>outgoing v - incoming v"
        by (auto simp: incoming_def outgoing_def no_self_loop)

      have 1: "sum f' (incoming v) = sum f (incoming v)"
        using UV_INO unfolding f'_alt
        by (auto simp: augment_edge_def intro: sum.cong)
          
      have "sum f' (outgoing v) 
        = sum f (outgoing v) + (\<Sum>x\<in>outgoing v. if x=(v,u) then - \<Delta> else 0)"    
        using UV_INO unfolding f'_alt
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
      by (auto simp: augment_edge_def f'_alt NE split!: if_split intro: sum.cong)  
    thus ?thesis    
      unfolding excess_def by auto
  qed      

  lemma excess'_if: 
    "excess f' x = (if x=u then excess f u - \<Delta> else if x=v then excess f v + \<Delta> else excess f x)"  
    by simp
    
end  
 

context Height_Bounded_Labeling
begin

lemma push_pres_height_bound:
  assumes "push_precond f l e"
  shows "Height_Bounded_Labeling c s t (push_effect f e) l"  
proof -    
  from push_pres_Labeling[OF assms] interpret l': Labeling c s t "push_effect f e" l .
  show ?thesis using height_bound by unfold_locales    
qed      
  
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
    
  show ?thesis 
  proof simp  
    interpret push_effect_locale c s t f l u v 
      apply unfold_locales using assms 
      by (simp add: push_precond_eq_sat_or_unsat)
      
    note [simp] = unsat_push_\<Delta>[OF assms[simplified]]
  
    define S where "S={x\<in>V. x\<noteq>u \<and> x\<noteq>v \<and> 0<excess f x}"
    have S_alt: "S = {x\<in>V. x\<noteq>u \<and> x\<noteq>v \<and> 0<excess f' x}"  
      unfolding S_def by auto
  
    have NES: "s\<notin>S" "u\<notin>S" "v\<notin>S" 
      and [simp, intro!]: "finite S" 
      unfolding S_def using excess_s_non_pos
      by auto 
      
    have 1: "{v\<in>V. 0 < excess f' v} = (if s=v then S else insert v S)"
      unfolding S_alt
      using excess_u_pos excess_non_negative' l'.excess_s_non_pos
      by (auto intro!: add_nonneg_pos)
        
    have 2: "{v\<in>V. 0 < excess f v} 
      = insert u S \<union> (if excess f v>0 then {v} else {})"    
      unfolding S_def using excess_u_pos by auto  
  
    show "unsat_potential f' l < unsat_potential f l"
      unfolding unsat_potential_def 1 2
      by (cases "s=v"; cases "0<excess f v"; auto simp: NES)
  qed      
qed
      
end -- \<open>Height bound labeling\<close>
  

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

(* Cormen 26.27 *)  
lemma push_adm_edges:
  assumes "push_precond f l e"  
  defines "f' \<equiv> push_effect f e"
  shows "adm_edges f l - {e} \<subseteq> adm_edges f' l" and "adm_edges f' l \<subseteq> adm_edges f l"
  unfolding f'_def 
  using assms sat_push_decr_adm_edges[of e] unsat_push_pres_adm_edges[of e]
  unfolding push_precond_eq_sat_or_unsat  
  by auto  

(* Cormen 26.28 *)
lemma relabel_adm_edges:
  assumes PRE: "relabel_precond f l u"
  defines "l' \<equiv> relabel_effect f l u"
  shows "adm_edges f l' \<inter> cf.outgoing u \<noteq> {}" (is ?G1)
    and "adm_edges f l' \<inter> cf.incoming u = {}" (is ?G2)
    and "adm_edges f l' - cf.adjacent u = adm_edges f l - cf.adjacent u" (is ?G3)
proof -
  from PRE have  
        NOT_SINK: "u\<noteq>t"
    and ACTIVE: "excess f u > 0"
    and NO_ADM: "\<And>v. (u,v)\<in>cf.E \<Longrightarrow> l u \<noteq> l v + 1"
  unfolding relabel_precond_def by auto
  
  have NE: "{l v |v. (u, v) \<in> cf.E} \<noteq> {}"  
    using active_has_cf_outgoing[OF ACTIVE] cf.outgoing_def by blast
  obtain v where VUE: "(u,v)\<in>cf.E" and [simp]: "l v = Min {l v |v. (u, v) \<in> cf.E}"
    using Min_in[OF finite_min_cf_outgoing[of u] NE] by auto
  hence "(u,v) \<in> adm_edges f l' \<inter> cf.outgoing u"  
    unfolding l'_def relabel_effect_def adm_edges_def cf.outgoing_def
    by (auto simp: cf_no_self_loop)
  thus ?G1 by blast

  {
    fix uh
    assume "(uh,u) \<in> adm_edges f l'"  
    hence 1: "l' uh = l' u + 1" and UHUE: "(uh,u) \<in> cf.E" unfolding adm_edges_def by auto
    hence "uh \<noteq> u" using cf_no_self_loop by auto
    hence [simp]: "l' uh = l uh" unfolding l'_def relabel_effect_def by simp
    from 1 relabel_increase_u[OF PRE, folded l'_def] have "l uh > l u + 1" by simp
    with valid[OF UHUE] have False by auto    
  }    
  thus ?G2 by (auto simp: cf.incoming_def)
      
  show ?G3    
    unfolding adm_edges_def
    by (auto simp: l'_def relabel_effect_def cf.adjacent_def cf.incoming_def cf.outgoing_def
        split: if_splits)
      
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
  
lemma wf_algo_rel[simp, intro!]: "wf algo_rel"  
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
  
lemma algo_rel_alt: "algo_rel = 
    { ((push_effect f e,l),(f,l)) | f e l. Height_Bounded_Labeling c s t f l \<and> push_precond f l e }
  \<union> { ((f, relabel_effect f l u), (f,l)) | f u l. Height_Bounded_Labeling c s t f l \<and> relabel_precond f l u }"  
  by (auto elim!: algo_rel.cases intro: algo_rel.intros simp: push_precond_eq_sat_or_unsat)
  
lemma algo_rel_pushI: "\<lbrakk>Height_Bounded_Labeling c s t f l; push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((push_effect f e,l),(f,l))\<in>algo_rel"
  unfolding algo_rel_alt by blast

lemma algo_rel_altE: 
  assumes "xx \<in> algo_rel"
  obtains f e l where "Height_Bounded_Labeling c s t f l" "push_precond f l e" "xx = ((push_effect f e,l),(f,l))"
        | f u l where "Height_Bounded_Labeling c s t f l" "relabel_precond f l u" "xx = ((f, relabel_effect f l u), (f,l))"
  using assms unfolding algo_rel_alt by blast
  

definition "RR \<equiv> { ((f, relabel_effect f l u), (f,l)) | f u l. Height_Bounded_Labeling c s t f l \<and> relabel_precond f l u }"
    
lemma "RR \<subseteq> measure (\<lambda>(f,l). sum_heights_measure l)"
  unfolding RR_def 
  apply auto
  using Height_Bounded_Labeling.relabel_measure 
  by blast    
  
    
end  


  
  
  
  
(* Relabel to front *)  
context Network begin  
  
definition "discharge f l n u \<equiv> do {  
  while\<^sub>T (\<lambda>(f,l,n). excess f u \<noteq> 0) (\<lambda>(f,l,n). do {
    v \<leftarrow> selectp v. v\<in>n u;
    case v of
      None \<Rightarrow> do {
        assert (relabel_precond f l u);
        return (f,relabel_effect f l u,n(u := adjacent_nodes u))
      }
    | Some v \<Rightarrow> do {
        if ((u,v) \<in> cfE_of f \<and> l u = l v + 1) then do {
          assert (push_precond f l (u,v));
          return (push_effect f (u,v),l,n)
        } else do {
          assert ( (u,v) \<notin> adm_edges f l );
          return (f,l,n( u := n u - {v} ))
        }
      }
  }) (f,l,n)
}"
  
end  
  
locale neighbor_invar = Height_Bounded_Labeling +
  fixes n :: "node \<Rightarrow> node set"  
  assumes neighbors_adm: "\<lbrakk>v \<in> adjacent_nodes u - n u\<rbrakk> \<Longrightarrow> (u,v) \<notin> adm_edges f l"
  assumes neighbors_finite[simp, intro!]: "finite (n u)"  
begin
  
lemma nbr_is_hbl: "Height_Bounded_Labeling c s t f l" by unfold_locales

lemma push_pres_nbr_invar:
  assumes PRE: "push_precond f l e"
  shows "neighbor_invar c s t (push_effect f e) l n"  
proof (cases e)
  case [simp]: (Pair u v)
  show ?thesis proof simp
    from PRE interpret push_effect_locale c s t f l u v
      by unfold_locales simp
    from push_pres_height_bound[OF PRE] interpret l': Height_Bounded_Labeling c s t f' l .
  
    show "neighbor_invar c s t f' l n"
      apply unfold_locales
      using push_adm_edges[OF PRE] neighbors_adm
      by auto  
  qed
qed
    
lemma relabel_pres_nbr_invar:  
  assumes PRE: "relabel_precond f l u"
  shows "neighbor_invar c s t f (relabel_effect f l u) (n(u:=adjacent_nodes u))"
proof -
  let ?l' = "relabel_effect f l u"
  from relabel_pres_height_bound[OF PRE] 
  interpret l': Height_Bounded_Labeling c s t f ?l' .
  
  show ?thesis proof (unfold_locales; clarsimp split: if_splits)
    fix a b
    assume A: "a\<noteq>u" "b\<in>adjacent_nodes a" "b \<notin> n a" "(a,b)\<in>adm_edges f ?l'"
    hence "(a,b)\<in>cf.E" unfolding adm_edges_def by auto
    with A relabel_adm_edges(2,3)[OF PRE] neighbors_adm 
    show False 
      apply (auto) (* TODO: Clean up this mess *)
      by (smt DiffD2 Diff_triv adm_edges_def cf.incoming_def mem_Collect_eq prod.simps(2) 
          relabel_preserve_other)
  qed
qed  

lemma excess_nz_iff_gz: "\<lbrakk> u\<in>V; u\<noteq>s \<rbrakk> \<Longrightarrow> excess f u \<noteq> 0 \<longleftrightarrow> excess f u > 0"  
  using excess_non_negative' by force
  
lemma no_neighbors_relabel_precond: 
  assumes "n u = {}" "u\<noteq>t" "u\<noteq>s" "u\<in>V" "excess f u \<noteq> 0"
  shows "relabel_precond f l u"  
  using assms neighbors_adm cfE_ss_invE 
  unfolding relabel_precond_def adm_edges_def
  by (auto simp: adjacent_nodes_def excess_nz_iff_gz)
  
lemma remove_neighbor_pres_nbr_invar: "(u,v)\<notin>adm_edges f l \<Longrightarrow> neighbor_invar c s t f l (n (u := n u - {v}))"
  apply unfold_locales
  using neighbors_adm 
  by (auto split: if_splits)
    
end
  
locale discharge_invar = neighbor_invar c s t f l n + lo: neighbor_invar c s t fo lo no
  for c s t and u :: node and fo lo no f l n +
  assumes lu_incr: "lo u \<le> l u"
  assumes u_node: "u\<in>V-{s,t}"  
  (*assumes excess_u_decr: "excess fo u \<ge> excess f u"*)
  assumes no_relabel_adm_edges: "lo u = l u \<Longrightarrow> adm_edges f l \<subseteq> adm_edges fo lo"
  assumes no_relabel_excess: "\<lbrakk>lo u = l u; u\<noteq>v; excess fo v \<noteq> excess f v\<rbrakk> \<Longrightarrow> (u,v)\<in>adm_edges fo lo"
  assumes adm_edges_leaving_u: "(u',v)\<in>adm_edges f l - adm_edges fo lo \<Longrightarrow> u'=u"
  assumes relabel_u_no_incoming_adm: "lo u \<noteq> l u \<Longrightarrow> (v,u)\<notin>adm_edges f l"
  assumes algo_rel: "((f,l),(fo,lo)) \<in> algo_rel\<^sup>*"  
begin

lemma u_node_simp1[simp]: "u\<noteq>s" "u\<noteq>t" "s\<noteq>u" "t\<noteq>u" using u_node by auto
lemma u_node_simp2[simp, intro!]: "u\<in>V" using u_node by auto   
  
lemma dis_is_hbl: "Height_Bounded_Labeling c s t f l" by unfold_locales
lemma dis_is_nbr: "neighbor_invar c s t f l n" by unfold_locales
  
lemma new_adm_imp_relabel: "(u',v)\<in>adm_edges f l - adm_edges fo lo \<Longrightarrow> lo u \<noteq> l u"
  using no_relabel_adm_edges adm_edges_leaving_u by auto
  
lemma push_pres_dis_invar:
  assumes PRE: "push_precond f l (u,v)"
  shows "discharge_invar c s t u fo lo no (push_effect f (u,v)) l n"
proof -  
  from PRE interpret push_effect_locale by unfold_locales
  
  from push_pres_nbr_invar[OF PRE] interpret neighbor_invar c s t f' l n .
    
  show "discharge_invar c s t u fo lo no f' l n"
    apply unfold_locales
    subgoal using lu_incr by auto
    subgoal by auto    
    (*subgoal using excess_u_decr \<Delta>_positive by auto*)
    subgoal using no_relabel_adm_edges push_adm_edges(2)[OF PRE] by auto  
    subgoal for v' proof -
      assume LOU: "lo u = l u"
      assume EXNE: "excess fo v' \<noteq> excess f' v'"
      assume UNV': "u\<noteq>v'"  
      {
        assume "excess fo v' \<noteq> excess f v'"
        from no_relabel_excess[OF LOU UNV' this] have ?thesis .
      } moreover {
        assume "excess fo v' = excess f v'"
        with EXNE have "excess f v' \<noteq> excess f' v'" by simp
        hence "v'=v" using UNV' by (auto simp: excess'_if split: if_splits)
        hence ?thesis using no_relabel_adm_edges[OF LOU] uv_adm by auto
      } ultimately show ?thesis by blast
    qed
    subgoal by (meson Diff_iff push_adm_edges(2)[OF PRE] adm_edges_leaving_u subsetCE)  
    subgoal using push_adm_edges(2)[OF PRE] relabel_u_no_incoming_adm by blast
    subgoal using converse_rtrancl_into_rtrancl[OF algo_rel_pushI[OF dis_is_hbl PRE] algo_rel] .
    done
qed
      
lemma relabel_pres_dis_invar:
  assumes PRE: "relabel_precond f l u"
  shows "discharge_invar c s t u fo lo no f (relabel_effect f l u) (n(u := adjacent_nodes u))"
proof -  
  let ?l' = "relabel_effect f l u"
  let ?n' = "n(u := adjacent_nodes u)"  
  from relabel_pres_nbr_invar[OF PRE] interpret l': neighbor_invar c s t f ?l' ?n' .
    
  note lu_incr also note relabel_increase_u[OF PRE] finally have INCR: "lo u < ?l' u" .
      
  show ?thesis    
    apply unfold_locales
    using INCR  
    apply simp_all
    subgoal for u' v 
    proof clarsimp
      assume IN': "(u', v) \<in> adm_edges f ?l'" and NOT_INO: "(u', v) \<notin> adm_edges fo lo"
      {
        assume IN: "(u', v) \<in> adm_edges f l"
        with adm_edges_leaving_u NOT_INO have "u'=u" by auto
      } moreover {
        assume NOT_IN: "(u', v) \<notin> adm_edges f l"
        with IN' relabel_adm_edges[OF PRE] have "u'=u" 
          unfolding cf.incoming_def cf.outgoing_def cf.adjacent_def
          by auto  
      } ultimately show ?thesis by blast
    qed      
    subgoal 
      using relabel_adm_edges(2)[OF PRE] 
      unfolding adm_edges_def cf.incoming_def 
      by fastforce  
    subgoal using converse_rtrancl_into_rtrancl[OF relabel[OF dis_is_hbl PRE] algo_rel] .
    done  
qed                                                    
  
(*lemma aux_excess_pos: "\<lbrakk>u\<noteq>s; u\<in>V; \<not> 0 < excess f u\<rbrakk> \<Longrightarrow> excess f u = 0"
  using excess_non_negative' by force
*)

lemma push_precondI_nz: "\<lbrakk>excess f u \<noteq> 0; (u,v)\<in>cfE_of f; l u = l v + 1\<rbrakk> \<Longrightarrow> push_precond f l (u,v)"
  unfolding push_precond_def by (auto simp: excess_nz_iff_gz)
  
  
lemma remove_neighbor_pres_dis_invar: 
  assumes PRE: "(u,v)\<notin>adm_edges f l"  
  defines "n' \<equiv> n (u := n u - {v})"  
  shows "discharge_invar c s t u fo lo no f l n'"
proof -
  from remove_neighbor_pres_nbr_invar[OF PRE] interpret neighbor_invar c s t f l n' unfolding n'_def .
  show ?thesis 
    apply unfold_locales
    using lu_incr no_relabel_adm_edges no_relabel_excess adm_edges_leaving_u 
      relabel_u_no_incoming_adm algo_rel
    by auto  
qed  
    
end  
  
lemma (in neighbor_invar) discharge_invar_init: 
  assumes "u\<in>V-{s,t}"
  shows "discharge_invar c s t u f l n f l n"
  using assms  
  by unfold_locales auto  
  
  
context Network begin  
  
lemma discharge_correct[THEN order_trans, refine_vcg]:
  assumes DINV: "neighbor_invar c s t f l n"
  assumes NOT_ST: "u\<noteq>t" "u\<noteq>s" and UIV: "u\<in>V"
  shows "discharge f l n u \<le> SPEC (\<lambda>(f',l',n'). discharge_invar c s t u f l n f' l' n' \<and> excess f' u = 0)"  
  unfolding discharge_def  
  apply (refine_vcg WHILET_rule[where 
            I="\<lambda>(f',l',n'). discharge_invar c s t u f l n f' l' n'"
        and R="inv_image (algo_rel <*lex*> finite_psubset) 
                (\<lambda>(f',l',n'). ((f',l'),n' u))"]
      )
  apply (vc_solve 
      solve: wf_lex_prod DINV 
      solve: neighbor_invar.discharge_invar_init[OF DINV]
      solve: neighbor_invar.no_neighbors_relabel_precond 
      solve: discharge_invar.relabel_pres_dis_invar discharge_invar.push_pres_dis_invar
      solve: discharge_invar.push_precondI_nz algo_rel.relabel algo_rel_pushI
      solve: discharge_invar.remove_neighbor_pres_dis_invar
      (*solve: discharge_invar.aux_excess_pos*)
      intro: discharge_invar.dis_is_hbl discharge_invar.dis_is_nbr 
      simp: NOT_ST neighbor_invar.neighbors_finite[OF discharge_invar.dis_is_nbr] UIV)
  subgoal unfolding adm_edges_def by auto  
  subgoal by (auto)
  done
  
end  
  
context Network begin  
  
definition "rtf_init_n u \<equiv> if u\<in>V-{s,t} then adjacent_nodes u else {}"

lemma rtf_init_n_finite[simp, intro!]: "finite (rtf_init_n u)"
  unfolding rtf_init_n_def
  by auto  
  
lemma init_no_adm_edges[simp]: "adm_edges pp_init_f pp_init_l = {}"  
  unfolding adm_edges_def pp_init_l_def
  using card_V_ge2  
  by auto  

lemma rtf_init_neighbor_invar: "neighbor_invar c s t pp_init_f pp_init_l rtf_init_n"
proof -
  from pp_init_height_bound interpret Height_Bounded_Labeling c s t pp_init_f pp_init_l .
  show ?thesis by unfold_locales auto  
qed


definition "relabel_to_front \<equiv> do {
  let f = pp_init_f;
  let l = pp_init_l;
  let n = rtf_init_n;

  let L_left=[];
  L_right \<leftarrow> spec l. distinct l \<and> set l = V - {s,t};

  (f,l,n,L_left,L_right) \<leftarrow> while\<^sub>T (\<lambda>(f,l,n,L_left,L_right). L_right \<noteq> []) (\<lambda>(f,l,n,L_left,L_right). do {
    let u = hd L_right;
    let old_lu = l u;

    (f,l,n) \<leftarrow> discharge f l n u;

    if (l u \<noteq> old_lu) then do {
      (* Move u to front of l, and restart scanning L *)
      let (L_left,L_right) = ([u],L_left @ tl L_right);
      return (f,l,n,L_left,L_right)
    } else do {
      (* Goto next node in l *)
      let (L_left,L_right) = (L_left@[u], tl L_right);
      return (f,l,n,L_left,L_right)
    }

  }) (f,l,n,L_left,L_right);

  return f
}"
  
  
end  
  
  
    
    
locale rtf_invar = neighbor_invar +
  fixes L_left L_right :: "node list"
  assumes left_no_excess: "\<forall>u\<in>set (L_left). excess f u = 0"  
  assumes L_sorted: "is_top_sorted (adm_edges f l) (L_left @ L_right)"
  assumes L_set: "set L_left \<union> set L_right = V-{s,t}"  
begin    
  lemma rtf_is_nbr: "neighbor_invar c s t f l n" by unfold_locales
      
  lemma L_distinct: "distinct (L_left @ L_right)" using is_top_sorted_distinct[OF L_sorted] .
  
  lemma terminated_imp_maxflow: 
    assumes [simp]: "L_right = []"   
    shows "isMaxFlow f" 
  proof -
    from L_set left_no_excess have "\<forall>u\<in>V-{s,t}. excess f u = 0" by auto
    with no_excess_imp_maxflow show ?thesis .    
  qed        
      
      
end  

context Network begin  
lemma rtf_init_invar: 
  assumes DIS: "distinct L_left" and L_set: "set L_left = V-{s,t}"
  shows "rtf_invar c s t pp_init_f pp_init_l rtf_init_n [] L_left"  
proof -
  from rtf_init_neighbor_invar interpret neighbor_invar c s t pp_init_f pp_init_l rtf_init_n .
  show ?thesis using DIS L_set by unfold_locales auto  
qed  
  
lemma relabel_to_front_correct: 
  "relabel_to_front \<le> SPEC isMaxFlow"
  unfolding relabel_to_front_def
  apply (rewrite in "while\<^sub>T _ \<hole>" vcg_intro_frame)
  apply (refine_vcg  
      WHILET_rule[where I="\<lambda>(f,l,n,L_left,L_right). rtf_invar c s t f l n L_left L_right"
                    and R="inv_image (algo_rel\<^sup>+ <*lex*> less_than) (\<lambda>(f,l,n,L_left,L_right). ((f,l),length L_right))"
        ]
      )
  apply (vc_solve simp: rtf_init_invar rtf_invar.rtf_is_nbr)
  subgoal by (blast intro: wf_lex_prod wf_trancl)  
  subgoal for _ f l n L_left L_right proof -
    assume "rtf_invar c s t f l n L_left L_right"
    then interpret rtf_invar c s t f l n L_left L_right .
        
    assume "L_right \<noteq> []" then obtain u L_right' where [simp]: "L_right = u#L_right'" by (cases L_right) auto
        
    from L_set have [simp]: "u\<in>V" "u\<noteq>s" "u\<noteq>t" "s\<noteq>u" "t\<noteq>u" by auto
        
    from L_distinct have [simp]: "u\<notin>set L_left" "u\<notin>set L_right'" by auto
        
    show ?thesis
      apply (rule vcg_rem_frame)
      apply (rewrite in "do {(_,_,_) \<leftarrow> discharge _ _ _ _; \<hole>}" vcg_intro_frame)  
      apply refine_vcg
      apply (vc_solve simp: rtf_is_nbr split del: if_split)
      subgoal for f' l' n' proof -
        assume "discharge_invar c s t u f l n f' l' n'"
        then interpret l': discharge_invar c s t u f l n f' l' n' .
      
        assume [simp]: "excess f' u = 0"
  
        show ?thesis 
          apply (rule vcg_rem_frame)
          apply refine_vcg
          apply (vc_solve)
          subgoal proof -
            assume RELABEL: "l' u \<noteq> l u"
              
            have AUX1: "x=u" if "(x, u) \<in> (adm_edges f' l')\<^sup>*" for x
              using that l'.relabel_u_no_incoming_adm[OF RELABEL[symmetric]]
              by (auto elim: rtranclE)
              
            have TS1: "is_top_sorted (adm_edges f l) (L_left @ L_right')"
              using L_sorted by (auto intro: is_top_sorted_remove_elem)

            (* intuition: 
                new edges come from u, but u has no incoming edges, nor is it in L_left@L_right'.
                thus, these new edges cannot add effective constraints. 
            *)
            from l'.adm_edges_leaving_u l'.relabel_u_no_incoming_adm[OF RELABEL[symmetric]]
            have "adm_edges f' l' \<subseteq> adm_edges f l \<union> {u}\<times>UNIV" and "adm_edges f' l' \<inter> UNIV\<times>{u}={}" by auto
            from is_top_sorted_isolated_constraint[OF this _ TS1]    
            have AUX2: "is_top_sorted (adm_edges f' l') (L_left @ L_right')" by simp   
                
            show "rtf_invar c s t f' l' n' [u] (L_left @ L_right')"
              apply unfold_locales
              subgoal by simp  
              subgoal using AUX2 by (auto simp: is_top_sorted_cons dest!: AUX1)
              subgoal using L_set by auto
              done    
          qed  
          subgoal using l'.algo_rel by (auto dest: rtranclD)
          subgoal proof -
            assume NO_RELABEL[simp]: "l' u = l u"
            (*Intuition: non-zero excess would imply an admissible edge contrary to top_sorted.*)
            have AUX: "excess f' v = 0" if "v\<in>set L_left" for v
            proof (rule ccontr)
              from that \<open>u\<notin>set L_left\<close> have "u \<noteq> v" by blast 
              moreover assume "excess f' v \<noteq> 0"
              moreover from that left_no_excess have "excess f v = 0" by auto
              ultimately have "(u,v)\<in>adm_edges f l"    
                using l'.no_relabel_excess[OF NO_RELABEL[symmetric]] 
                by auto
              
              with L_sorted that show False
                by (auto simp: is_top_sorted_append is_top_sorted_cons)
            qed      
            show "rtf_invar c s t f' l' n' (L_left @ [u]) L_right'"  
              apply unfold_locales
              subgoal by (auto simp: AUX)  
              subgoal 
                apply (rule is_top_sorted_antimono[OF l'.no_relabel_adm_edges[OF NO_RELABEL[symmetric]]])
                using L_sorted by simp  
              subgoal using L_set by auto
              done
          qed
          subgoal using l'.algo_rel by (auto dest: rtranclD)
          done    
      qed
      done  
  qed
  subgoal by (auto intro: rtf_invar.terminated_imp_maxflow)  
  done
    
end -- \<open>Network\<close> 
  

section \<open>FIFO selection rule\<close>  
(* Straightforward, also O(V\<^sup>3) complexity, can be combined with gap heuristics.
  Idea: Maintain queue of active nodes, discharge node at front, add activated nodes
        to end.
*)
  
  
context Network
begin

definition "Q_invar f Q \<equiv> distinct Q \<and> set Q = { v\<in>V-{s,t}. excess f v \<noteq> 0 }"  
definition "QD_invar u f Q \<equiv> distinct Q \<and> set Q = { v\<in>V-{s,t,u}. excess f v \<noteq> 0 }"  

lemma Q_invar_when_discharged: "\<lbrakk>QD_invar u f Q; excess f u = 0\<rbrakk> \<Longrightarrow> Q_invar f Q"  
  unfolding Q_invar_def QD_invar_def by auto
  
end  
  
context discharge_invar begin  
  
  lemma push_no_activate_pres_QD_invar:
    fixes v
    assumes INV: "QD_invar u f Q"
    assumes PRE: "push_precond f l (u,v)"
    assumes VC: "s=v \<or> t=v \<or> excess f v \<noteq> 0"  
    shows "QD_invar u (push_effect f (u,v)) Q"
  proof -
    interpret push_effect_locale c s t f l u v 
      using PRE by unfold_locales
    
    from excess_non_negative \<Delta>_positive have "excess f v + \<Delta> \<noteq> 0" if "v\<notin>{s,t}"
      using that by force
    thus ?thesis    
      using VC INV
      unfolding QD_invar_def
      by (auto simp: excess'_if split!: if_splits)  
  qed      

  lemma push_activate_pres_QD_invar:  
    fixes v
    assumes INV: "QD_invar u f Q"
    assumes PRE: "push_precond f l (u,v)"
    assumes VC: "s\<noteq>v" "t\<noteq>v" and [simp]: "excess f v = 0"  
    shows "QD_invar u (push_effect f (u,v)) (Q@[v])"
  proof -
    interpret push_effect_locale c s t f l u v 
      using PRE by unfold_locales
    
    show ?thesis    
      using VC INV \<Delta>_positive
      unfolding QD_invar_def
      by (auto simp: excess'_if split!: if_splits)  
  qed      
    
end  
  
  
context Network
begin
  
definition "fifo_discharge f l n Q \<equiv> do {  
  let u=hd Q; let Q=tl Q;
  assert (u\<in>V \<and> u\<noteq>s \<and> u\<noteq>t);
  while\<^sub>T (\<lambda>(f,l,n,Q). excess f u \<noteq> 0) (\<lambda>(f,l,n,Q). do {
    v \<leftarrow> selectp v. v\<in>n u;
    case v of
      None \<Rightarrow> do {
        assert (relabel_precond f l u);
        return (f,relabel_effect f l u,n(u := adjacent_nodes u),Q)
      }
    | Some v \<Rightarrow> do {
        if ((u,v) \<in> cfE_of f \<and> l u = l v + 1) then do {
          assert (push_precond f l (u,v));
          let Q = (if v\<noteq>s \<and> v\<noteq>t \<and> excess f v = 0 then Q@[v] else Q);
          return (push_effect f (u,v),l,n,Q)
        } else do {
          assert ( (u,v) \<notin> adm_edges f l );
          return (f,l,n( u := n u - {v} ),Q)
        }
      }
  }) (f,l,n,Q)
}"

lemma fifo_discharge_correct[THEN order_trans, refine_vcg]:
  assumes DINV: "neighbor_invar c s t f l n"
  assumes QINV: "Q_invar f Q" and QNE: "Q\<noteq>[]"
  shows "fifo_discharge f l n Q \<le> SPEC (\<lambda>(f',l',n',Q'). 
    discharge_invar c s t (hd Q) f l n f' l' n' \<and> excess f' (hd Q) = 0 \<and> Q_invar f' Q'
  )"  
proof -
  from QNE obtain u Qr where [simp]: "Q=u#Qr" by (cases Q) auto
  
  from QINV have U: "u\<in>V-{s,t}" "QD_invar u f Qr"
    by (auto simp: Q_invar_def QD_invar_def)    

  show ?thesis
    using U
    unfolding fifo_discharge_def  
    apply (refine_vcg WHILET_rule[where 
              I="\<lambda>(f',l',n',Q'). discharge_invar c s t u f l n f' l' n' \<and> QD_invar u f' Q'"
          and R="inv_image (algo_rel <*lex*> finite_psubset) 
                  (\<lambda>(f',l',n',_). ((f',l'),n' u))"]
        )
    apply (vc_solve 
        solve: wf_lex_prod DINV 
        solve: neighbor_invar.discharge_invar_init[OF DINV]
        solve: neighbor_invar.no_neighbors_relabel_precond 
        solve: discharge_invar.relabel_pres_dis_invar discharge_invar.push_pres_dis_invar
        solve: discharge_invar.push_precondI_nz algo_rel.relabel algo_rel_pushI
        solve: discharge_invar.remove_neighbor_pres_dis_invar
        solve: Q_invar_when_discharged
        intro: discharge_invar.dis_is_hbl discharge_invar.dis_is_nbr 
        simp: neighbor_invar.neighbors_finite[OF discharge_invar.dis_is_nbr])
    subgoal 
      by (auto 
          intro: discharge_invar.push_activate_pres_QD_invar 
          intro: discharge_invar.push_no_activate_pres_QD_invar)
    subgoal unfolding adm_edges_def by auto  
    subgoal by (auto)
    done
qed  
  

definition "fifo_push_relabel \<equiv> do {
  let f = pp_init_f;
  let l = pp_init_l;
  let n = rtf_init_n;

  Q \<leftarrow> spec l. distinct l \<and> set l = {v\<in>V - {s,t}. excess f v \<noteq> 0}; (* TODO: This is exactly E``{s}! *)

  (f,l,n,_) \<leftarrow> while\<^sub>T (\<lambda>(f,l,n,Q). Q \<noteq> []) (\<lambda>(f,l,n,Q). do {
    fifo_discharge f l n Q
  }) (f,l,n,Q);

  return f
}"
  
lemma fifo_push_relabel_correct: 
  "fifo_push_relabel \<le> SPEC isMaxFlow"
  unfolding fifo_push_relabel_def
  apply (refine_vcg  
      WHILET_rule[where I="\<lambda>(f,l,n,Q). neighbor_invar c s t f l n \<and> Q_invar f Q"
                    and R="inv_image (algo_rel\<^sup>+) (\<lambda>(f,l,n,Q). ((f,l)))"
        ]
      )
  apply (vc_solve solve: rtf_init_neighbor_invar simp: discharge_invar.dis_is_nbr)
  subgoal by (blast intro: wf_lex_prod wf_trancl)  
  subgoal unfolding Q_invar_def by auto    
  subgoal for initQ f l n Q f' l' n' Q' proof -
    assume "discharge_invar c s t (hd Q) f l n f' l' n'" 
    then interpret discharge_invar c s t "hd Q" f l n f' l' n' .

    assume "Q_invar f Q" "Q \<noteq> []" "excess f' (hd Q) = 0"
    hence "f \<noteq> f'" unfolding Q_invar_def by (cases Q) auto 
    with algo_rel show "((f', l'), f, l) \<in> algo_rel\<^sup>+" by (auto dest: rtranclD)
  qed
  subgoal for initQ f l n proof -
    assume "neighbor_invar c s t f l n"
    then interpret neighbor_invar c s t f l n .
    assume "Q_invar f []"    
    hence "\<forall>u\<in>V-{s,t}. excess f u = 0" unfolding Q_invar_def by auto
    thus "isMaxFlow f" by (rule no_excess_imp_maxflow)    
  qed
  done    
    
end  
    
end
