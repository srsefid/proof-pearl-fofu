theory Augmenting_Path_DFS
imports Refine_Add_Fofu Graph Graph_Impl
begin



text {*
  We define a simple DFS-algorithm, prove a simple correctness
  property, and do data refinement to an efficient implementation.
*}

subsection {* Definition *}

text {* Recursive DFS-Algorithm. 
  @{text "E"} is the edge relation of the graph, @{text "vd"} the node to 
  search for, and @{text "v0"} the start node.
  Already explored nodes are stored in @{text "V"}.*}

context Graph begin

  context 
    fixes v0 tgt :: node
    assumes valid_st: "v0\<in>V" "tgt\<in>V"
  begin
    definition dfs :: "path option nres" where
      "dfs \<equiv> do {
        (_,r) \<leftarrow> RECT (\<lambda>dfs (V,v). do {
          ASSERT (v\<in>local.V);
          if v\<in>V then RETURN (V,None)
          else do {
            let V=insert v V;
            if v = tgt then
              RETURN (V,Some [])
            else do {
              let succs = E``{v};
              FOREACH\<^sub>C succs (\<lambda>(_,b). b=None) (\<lambda>v' (V,_). do {
                ASSERT (v'\<in>local.V);
                (V,r) \<leftarrow> dfs (V,v');
                case r of
                  None \<Rightarrow> RETURN (V,r)
                | Some p \<Rightarrow> RETURN (V,Some ((v,v')#p))  
              }) (V,None)
            }  
          }
        }) ({},v0);
        RETURN r
      }"
  
    definition "correct_path_spec r \<equiv> case r of 
      None \<Rightarrow> (v0,tgt)\<notin>E\<^sup>* 
    | Some p \<Rightarrow> isSimplePath v0 p tgt"

    lemma correct_path_spec_alt: "correct_path_spec r \<longleftrightarrow> (case r of 
      None \<Rightarrow> \<forall>p. \<not>isSimplePath v0 p tgt
    | Some p \<Rightarrow> isSimplePath v0 p tgt)"
      unfolding correct_path_spec_def
      using isSPath_pathLE
      by (auto 
        simp: isSimplePath_def
        split: option.splits         
        dest!: Graph.isPath_alt_rtc1 
        dest: Graph.isPath_alt
        )
      


    lemma dfs_correct:
      assumes fr: "finite (reachable v0)"
      shows "dfs \<le> SPEC (correct_path_spec)"
    proof -
      have F: "\<And>v. v\<in>reachable v0 \<Longrightarrow> finite (E``{v})"
        using fr
        apply (auto simp: reachable_alt)
        by (metis (mono_tags) Image_singleton_iff
          finite_subset rtrancl.rtrancl_into_rtrancl subsetI)
  
    
      def rpre \<equiv> "\<lambda>S (V,v). 
          v\<in>reachable v0
        \<and> V\<subseteq>reachable v0
        \<and> S\<subseteq>V
        \<and> tgt\<notin>V
        \<and> E``(V-S) \<subseteq> V"
  
      def rpost \<equiv> "\<lambda>S (V,v) (V',r). 
            (r=None\<longleftrightarrow>tgt\<notin>V') 
          \<and> (\<forall>p. r=Some p \<longrightarrow> isSimplePath v p tgt \<and> set (pathVertices v p) \<subseteq> V'-V)  
          \<and> V\<subseteq>V' 
          \<and> v\<in>V'
          \<and> V'\<subseteq>reachable v0
          \<and> (r=None \<longrightarrow> (E``(V'-S) \<subseteq> V'))
        "
  
      def fe_inv \<equiv> "\<lambda>S V v it (V',r).
          (r=None\<longleftrightarrow>tgt\<notin>V')
        \<and> (v\<notin>V)  
        \<and> (\<forall>p. r=Some p \<longrightarrow> isSimplePath v p tgt \<and> set (pathVertices v p) \<subseteq> V'-V)  
        \<and> insert v V\<subseteq>V'
        \<and> E``{v} - it \<subseteq> V'
        \<and> V'\<subseteq>reachable v0
        \<and> S\<subseteq>insert v V
        \<and> (r=None \<longrightarrow> E``(V'-S) \<subseteq> V' \<union> it \<and> E``(V'-insert v S) \<subseteq> V')"
  
      have vc_pre_initial: "rpre {} ({}, v0)"
        by (auto simp: rpre_def reachable_def)
  
      {
        (* Case: Node already visited *)
        fix S V v
        assume "rpre S (V,v)"
          and "v\<in>V"
        hence "rpost S (V,v) (V,None)"
          unfolding rpre_def rpost_def
          by auto
      } note vc_node_visited = this
  
      {
        (* Case: Found node *)
        fix S V
        assume "rpre S (V,tgt)"
        hence "rpost S (V,tgt) (insert tgt V, Some [])"
          unfolding rpre_def rpost_def
          by auto
      } note vc_node_found = this
  
      { 
        fix S V v
        assume "rpre S (V, v)"
        hence "finite (E``{v})"
          unfolding rpre_def using F by (auto)
      } note vc_foreach_finite = this
    
      {
        (* fe_inv initial *)
        fix S V v
        assume A: "v \<notin> V" "v \<noteq> tgt"
          and PRE: "rpre S (V, v)"
        hence "fe_inv S V v (E``{v}) (insert v V, None)"
          unfolding fe_inv_def rpre_def by (auto)
      } note vc_enter_foreach = this
  
      {
        (* fe_inv ensures rpre *)
        fix S V v v' it V'
        assume A: "v \<notin> V" "v \<noteq> tgt" "v' \<in> it" "it \<subseteq> E``{v}"
          and FEI: "fe_inv S V v it (V', None)"
          and PRE: "rpre S (V, v)"
  
        from A have "v' \<in> E``{v}" by auto
        moreover from PRE have "v \<in> reachable v0" by (auto simp: rpre_def)
        hence "E``{v} \<subseteq> reachable v0" by (auto simp: reachable_alt)
        ultimately have [simp]: "v'\<in>reachable v0" by blast
  
        have "rpre (insert v S) (V', v')"
          unfolding rpre_def
          using FEI PRE by (auto simp: fe_inv_def rpre_def) []
      } note vc_rec_pre = this

      {
        (* rpost implies fe_inv (no path found) *)
        fix S V V' v v' it V''
        assume "fe_inv S V v it (V', None)"
          and "rpost (insert v S) (V', v') (V'', None)"
        hence "fe_inv S V v (it - {v'}) (V'', None)"
          unfolding rpre_def rpost_def fe_inv_def
          apply clarsimp
          apply blast
          done
      } note vc_iterate_foreach_None = this

      {
        (* rpost implies fe_inv (path found) *)
        fix S V V' v v' it V'' p
        assume "fe_inv S V v it (V', None)"
          and "rpost (insert v S) (V', v') (V'', Some p)"
          and "(v,v')\<in>E"
        hence "fe_inv S V v (it - {v'}) (V'', Some ((v,v')#p))"
          unfolding rpre_def rpost_def fe_inv_def
          apply clarsimp
          apply (blast intro: isSimplePath_prepend)
          done
      } note vc_iterate_foreach_Some = this
  
  
      {
        (* fe_inv (completed) implies rpost *)
        fix S V v V'
        assume PRE: "rpre S (V, v)" 
        assume A: "v \<notin> V" "v \<noteq> tgt"
        assume FEI: "fe_inv S V v {} (V', None)"
        have "rpost S (V, v) (V', None)"
          unfolding rpost_def
          using FEI by (auto simp: fe_inv_def) []
      } note vc_foreach_completed_imp_post = this
  
      {
        (* fe_inv (interrupted) implies rpost *)
        fix S V v V' it p
        assume PRE: "rpre S (V, v)" 
          and A: "v \<notin> V" "v \<noteq> tgt" "it \<subseteq> E``{v}"
          and FEI: "fe_inv S V v it (V', Some p)"
        hence "rpost S (V, v) (V', Some p)"
          by (auto simp add: rpre_def rpost_def fe_inv_def) []
      } note vc_foreach_interrupted_imp_post = this
  
      {
        fix V r
        assume "rpost {} ({}, v0) (V, r)"
        hence "correct_path_spec r"
          by (fastforce 
            simp: rpost_def reachable_alt correct_path_spec_def
            dest: Image_closed_trancl 
            intro: rev_ImageI)
      } note vc_rpost_imp_spec = this

      have vc_rpre_imp_node: "\<And>S V v. rpre S (V,v) \<Longrightarrow> v\<in>local.V"
        using reachable_ss_V valid_st
        by (auto simp: rpre_def)
  
      show ?thesis
        unfolding dfs_def
        apply (refine_rcg refine_vcg)
        apply (rule order_trans)
        
        apply(rule RECT_rule_arb'[where 
            pre=rpre 
            and M="\<lambda>a x. SPEC (rpost a x)"
            and V="finite_psupset (reachable v0) <*lex*> {}"
            ])
        apply refine_mono
        apply (blast intro: fr)
        apply (rule vc_pre_initial)
        
        apply (refine_rcg refine_vcg 
          FOREACHc_rule'[where I="fe_inv S v s" for S v s]
          )
        apply (simp_all add: vc_node_visited vc_node_found)
  
        apply (simp add: vc_rpre_imp_node)
        apply (simp add: vc_foreach_finite)
  
        apply (auto intro: vc_enter_foreach) []

        apply (auto simp: V_def) []

        apply (rule order_trans)
        apply (rprems)
        apply (erule (5) vc_rec_pre)
          apply (auto simp add: fe_inv_def finite_psupset_def) []
          apply (refine_rcg refine_vcg)
          apply (simp add: vc_iterate_foreach_None)
          apply (auto simp add: vc_iterate_foreach_Some) []
  
        apply (auto simp add: vc_foreach_completed_imp_post) []
  
        apply (auto simp add: vc_foreach_interrupted_imp_post) []
  
        apply (auto simp add: vc_rpost_imp_spec) []
        done
    qed
  end

subsection \<open>Explicit Successor Function\<close>


  context
    fixes succ :: "node \<Rightarrow> node list nres"
    fixes v0 tgt :: node
  begin
    definition dfs2 :: "path option nres" where
      "dfs2 \<equiv> do {
        ASSERT (v0\<in>V);
        ASSERT (tgt\<in>V);
        (_,r) \<leftarrow> RECT (\<lambda>dfs (V,v). do {
          ASSERT (v\<in>local.V);
          if v\<in>V then RETURN (V,None)
          else do {
            let V=insert v V;
            if v = tgt then
              RETURN (V,Some [])
            else do {
              succs \<leftarrow> succ v;
              nfoldli succs (\<lambda>(_,b). b=None) (\<lambda>v' (V,_). do {
                ASSERT (v'\<in>local.V);
                (V,r) \<leftarrow> dfs (V,v');
                case r of
                  None \<Rightarrow> RETURN (V,r)
                | Some p \<Rightarrow> RETURN (V,Some ((v,v')#p))  
              }) (V,None)
            }  
          }
        }) ({},v0);
        RETURN r
      }"
 
    lemma dfs2_refine:
      assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> \<Longrightarrow> succ ui \<le> SPEC (\<lambda>l. (l,E``{u}) \<in> \<langle>Id\<rangle>list_set_rel)"
      assumes valid_st: "v0\<in>V" "tgt\<in>V"
      shows "dfs2 \<le> \<Down>Id (dfs v0 tgt)"
    proof -
      have [refine_dref_RELATES]: "RELATES (\<langle>nat_rel\<rangle>list_set_rel)" by (simp add: RELATES_def)
      show ?thesis
        unfolding dfs2_def dfs_def[OF valid_st]
        apply (refine_rcg LFOc_refine succ_impl)
        apply refine_dref_type
        apply (vc_solve simp: valid_st)
        done
    qed

  
  end

end

lemma dfs2_refine_succ: 
  assumes [refine]: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>Graph.V c\<rbrakk> \<Longrightarrow> succi ui \<le> \<Down>Id (succ u)"
  assumes [simplified, simp]: "(si,s)\<in>Id" "(ti,t)\<in>Id" "(ci,c)\<in>Id"
  shows "Graph.dfs2 ci succi si ti \<le> \<Down>Id (Graph.dfs2 c succ s t)"
  unfolding Graph.dfs2_def
  apply (refine_rcg param_nfoldli[param_fo, THEN nres_relD] nres_relI fun_relI)
  apply refine_dref_type
  apply vc_solve
  done




subsection \<open>Refinement to Imperative/HOL\<close>

term Graph.dfs2

context Impl_Succ begin
  definition op_dfs :: "'ga \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres" where [simp]: "op_dfs c s t \<equiv> Graph.dfs2 (absG c) (succ c) s t"

  lemma pat_op_dfs[pat_rules]: 
    "Graph.dfs2$(absG$c)$(succ$c)$s$t \<equiv> UNPROTECT op_dfs$c$s$t" by simp 

  sepref_register "PR_CONST op_dfs" "'ig \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres"  

  schematic_lemma dfs_impl:
    fixes s t :: nat
    notes [sepref_opt_simps del] = imp_nfoldli_def 
      -- \<open>Prevent the foreach-loop to be unfolded to a fixed-point, 
          to produce more readable code for presentation purposes.\<close>
    notes [id_rules] = 
      itypeI[Pure.of s "TYPE(nat)"]
      itypeI[Pure.of t "TYPE(nat)"]
      itypeI[Pure.of c "TYPE('ig)"]
      -- \<open>Declare parameters to operation identification\<close>
    shows "hn_refine (
      hn_ctxt (isG) c ci 
    * hn_val nat_rel s si 
    * hn_val nat_rel t ti) (?c::?'c Heap) ?\<Gamma>' ?R (PR_CONST op_dfs c s t)"
    unfolding Graph.dfs2_def op_dfs_def PR_CONST_def
    using [[id_debug, goals_limit = 1]]
    apply sepref_keep
    done
  
  concrete_definition dfs_impl uses dfs_impl
    -- \<open>Extract generated implementation into constant\<close>


(*  prepare_code_thms dfs_impl_def *)
 
  lemmas dfs_impl_fr_rule = dfs_impl.refine[to_hfref]  

end



(*
locale intf_gen_dfs =
  fixes absG :: "'ga \<Rightarrow> graph"
  fixes ifT :: "'ig itself"
  fixes succ :: "'ga \<Rightarrow> node \<Rightarrow> node list nres"
begin

  definition op_dfs :: "'ga \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres" where [simp]: "op_dfs c s t \<equiv> Graph.dfs2 (absG c) (succ c) s t"

  lemma pat_op_dfs[pat_rules]: 
    "Graph.dfs2$(absG$c)$(succ$c)$s$t \<equiv> UNPROTECT op_dfs$c$s$t" by simp 

  sepref_register "succ" "'ig \<Rightarrow> node \<Rightarrow> node list nres"  
  sepref_register "PR_CONST op_dfs" "'ig \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres"  
end

locale impl_gen_dfs = intf_gen_dfs absG ifT for absG :: "'ga \<Rightarrow> _" and ifT :: "'ig itself" +  
  fixes isG :: "'ga \<Rightarrow> 'gi \<Rightarrow> assn"
  fixes succ_impl :: "'gi \<Rightarrow> node \<Rightarrow> node list Heap"
  assumes [constraint_rules]: "precise isG"
  assumes si_rule[sepref_fr_rules]: "(uncurry succ_impl,(uncurry succ)) \<in> [\<lambda>(c,u). u\<in>Graph.V (absG c)]\<^sub>a isG\<^sup>k *\<^sub>a (pure nat_rel)\<^sup>k \<rightarrow> hn_list_aux (pure nat_rel)"
begin
  schematic_lemma dfs_impl:
    fixes s t :: nat
    notes [sepref_opt_simps del] = imp_nfoldli_def 
      -- \<open>Prevent the foreach-loop to be unfolded to a fixed-point, 
          to produce more readable code for presentation purposes.\<close>
    notes [id_rules] = 
      itypeI[Pure.of s "TYPE(nat)"]
      itypeI[Pure.of t "TYPE(nat)"]
      itypeI[Pure.of c "TYPE('ig)"]
      -- \<open>Declare parameters to operation identification\<close>
    shows "hn_refine (
      hn_ctxt (isG) c ci 
    * hn_val nat_rel s si 
    * hn_val nat_rel t ti) (?c::?'c Heap) ?\<Gamma>' ?R (PR_CONST op_dfs c s t)"
    unfolding Graph.dfs2_def op_dfs_def PR_CONST_def
    using [[id_debug, goals_limit = 1]]
    apply sepref_keep
    done
  
  concrete_definition dfs_impl uses dfs_impl
    -- \<open>Extract generated implementation into constant\<close>


(*  prepare_code_thms dfs_impl_def *)
 
  lemmas dfs_impl_fr_rule = dfs_impl.refine[to_hfref]  


end
*)


end

