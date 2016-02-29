*** Obsolete ***
theory Algorithm
imports 
  CAVA_Base  
  "../../cava/Libs/Refine_Imperative_HOL/Heaps/Array_List"
  MaxFlow_MinCut
  "Augmenting_Path_BFS"
begin

  (*
  definition find_path0_pred where "find_path0_pred G P \<equiv> \<lambda>r. case r of 
      None \<Rightarrow> (g_E G)\<^sup>* `` g_V0 G \<inter> Collect P = {}
    | Some (vs,v) \<Rightarrow> P v \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G) v0 vs v \<and> distinct (vs@[v]))"
  
  definition find_path0_spec
    :: "('v, _) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
    -- \<open>Searches a path from the root nodes to some target node that satisfies a 
        given predicate. If such a path is found, the path and the target node
        are returned\<close>
  where
    "find_path0_spec G P \<equiv> do {
      ASSERT (fb_graph G);
      SPEC (find_path0_pred G P)
    }"
  *)  


  fun path_conv1 :: "nat list \<times> nat \<Rightarrow> edge list" where
    "path_conv1 ([],_) = []"
  | "path_conv1 ([u],v) = [(u,v)]"  
  | "path_conv1 (u1#u2#p,v) = (u1,u2)#path_conv1 (u2#p,v)"

  definition "path_conv2 p \<equiv> map fst p"

  context Graph begin

    lemma path_conv2: "isPath u p v \<Longrightarrow> path E u (path_conv2 p) v"
      apply (induction p arbitrary: u)
      by (auto simp: path_conv2_def path_simps E_def)

    lemma path_conv1: "path E u p v \<longleftrightarrow> isPath u (path_conv1 (p,v)) v"
    proof (induction "(p,v)" arbitrary: p v u rule: path_conv1.induct)
      case 1 thus ?case by (auto simp: path_simps E_def) []
    next
      case 2 thus ?case by (auto simp: path_simps E_def) []
    next  
      case (3 u1 u2 p v u) show ?case proof
        assume "path E u (u1 # u2 # p) v"
        hence [simp]: "u=u1" and "(u1,u2)\<in>E" and 1: "path E u2 (u2#p) v" by (auto simp: path_simps)
        
        from "3.hyps" 1 have "isPath u2 (path_conv1 (u2 # p, v)) v" by simp
        then show "isPath u (path_conv1 (u1 # u2 # p, v)) v"
          using \<open>(u1,u2)\<in>E\<close>
          by (auto simp: E_def)
      next    
        assume "isPath u (path_conv1 (u1 # u2 # p, v)) v"
        hence 1: "u=u1" "(u1,u2)\<in>E" and "isPath u2 (path_conv1 (u2 # p, v)) v"
          by (auto simp: E_def)
        with "3.hyps" have "path E u2 (u2#p) v" by simp
        thus "path E u (u1 # u2 # p) v" using 1 by (auto simp: path_simps)
      qed
    qed  

    lemma path_conv1_empty_iff[simp]: "path_conv1 (p,v) = [] \<longleftrightarrow> p=[]"
      by (induction "(p,v)" rule: path_conv1.induct) auto

    lemma snd_last_path_conv[simp]: "p\<noteq>[] \<Longrightarrow> snd (last (path_conv1 (p, v))) = v"  
      by (induction "(p,v)" arbitrary: p rule: path_conv1.induct) auto

    lemma fst_set_path_conv[simp]: "fst`set (path_conv1 (p,v)) = set p"  
      by (induction "(p,v)" arbitrary: p rule: path_conv1.induct) auto


    lemma distinct_conv: "distinct (pathVertices ((hd (p@[v]))) (path_conv1 (p, v))) \<longleftrightarrow> (distinct (p@[v]))"
      apply (induction "(p,v)" arbitrary: p v rule: path_conv1.induct)
      apply simp
      apply simp
      apply (auto simp add: pathVertices_alt del: pathVertices.simps) []
      done


  end

  definition (in Graph) "augment_cf edges cap \<equiv> \<lambda>e. 
    if e\<in>edges then c e - cap 
    else if prod.swap e\<in>edges then c e + cap
    else c e"
  
  lemma (in Graph) augment_cf_empty[simp]: "augment_cf {} cap = c" 
    by (auto simp: augment_cf_def)

  lemma (in Graph) augment_cf_ss_V: "\<lbrakk>edges \<subseteq> E\<rbrakk> \<Longrightarrow> Graph.V (augment_cf edges cap) \<subseteq> V"  
    by (auto simp add: augment_cf_def Graph.V_def Graph.E_def) []
    

  lemma (in Graph) augment_saturate:
    fixes edges e
    defines "c' \<equiv> augment_cf edges (c e)"
    assumes EIE: "e\<in>edges"
    shows "e\<notin>Graph.E c'"
    using EIE unfolding c'_def augment_cf_def
    by (auto simp: Graph.E_def)
    

  lemma (in -) augment_cf_split: 
    assumes "edges1 \<inter> edges2 = {}" "edges1\<inverse> \<inter> edges2 = {}"
    shows "Graph.augment_cf c (edges1 \<union> edges2) cap 
      = Graph.augment_cf (Graph.augment_cf c edges1 cap) edges2 cap"  
    using assms
    by (fastforce simp: Graph.augment_cf_def intro!: ext)
    
  lemma (in Graph) augment_singleton_bounds:
    fixes e cap
    defines "c' \<equiv> augment_cf {e} cap"
    assumes CAP_POS: "cap>0" and NO_LOOP: "e\<noteq>prod.swap e"
    shows "Graph.E c' \<supseteq> E - {e} \<union> {prod.swap e}" "Graph.E c' \<subseteq> E \<union> {prod.swap e}"
    unfolding c'_def using CAP_POS NO_LOOP
    by (auto simp: augment_cf_def Graph.E_def)

  lemma (in Graph) augment_singleton_bounds_saturate:
    fixes e
    defines "c' \<equiv> augment_cf {e} (c e)"
    assumes CAP_POS: "c e>0" and NO_LOOP: "e\<noteq>prod.swap e"
    shows "Graph.E c' \<supseteq> E - {e} \<union> {prod.swap e}" "Graph.E c' \<subseteq> E \<union> {prod.swap e}" "e\<notin>Graph.E c'"
    unfolding c'_def using CAP_POS NO_LOOP
    by (auto simp: augment_cf_def Graph.E_def)



  context NFlow begin

    lemma augmenting_edge_no_swap_aux:
      assumes AUG: "isAugmenting p"
      assumes EIP: "e\<in>set p"
      shows "prod.swap e \<notin> set p"
    proof -  
      interpret cf!: Graph cf .  (* TODO: Define this globally as a sublocale, with prefix cf! *)

      from AUG have P: "cf.isPath s p t" and D: "distinct (cf.pathVertices s p)"
        by (auto simp: isAugmenting_def cf.isSimplePath_def)

      show "prod.swap e \<notin> set p"  
        apply (cases e) using D EIP
        by (auto 
          dest!: cf.pathVertices_edge[OF P] 
          elim!: list_match_lel_lel list_Cons_eq_append_cases)

    qed

    corollary augmenting_edge_no_swap: "isAugmenting p \<Longrightarrow> set p \<inter> (set p)\<inverse> = {}"
      by (auto dest: augmenting_edge_no_swap_aux)

    lemma aug_flows_finite[simp, intro!]: 
      "finite {cf e |e. e \<in> set p}"
      apply (rule finite_subset[where B="cf`set p"])
      by auto

    lemma aug_flows_finite'[simp, intro!]: 
      "finite {cf (u,v) |u v. (u,v) \<in> set p}"
      apply (rule finite_subset[where B="cf`set p"])
      by auto

    lemma augment_alt:
      assumes AUG: "isAugmenting p"
      defines "f' \<equiv> augment (augmentingFlow p)"
      defines "cf' \<equiv> residualGraph f'"
      shows "cf' = Graph.augment_cf cf (set p) (bottleNeck p)"
    proof -
      interpret cf!: Graph cf .

      note aux = augmenting_edge_no_swap_aux[OF AUG, where e="(u,v)" for u v, simplified]

      {
        fix u v
        assume "(u,v)\<in>set p"
        hence "bottleNeck p \<le> cf (u,v)"
          unfolding bottleNeck_def by (auto intro: Min_le)
      } note bn_smallerI = this

      {
        fix u v
        assume "(u,v)\<in>set p"
        hence "(u,v)\<in>cf.E" using AUG cf.isPath_edgeset
          by (auto simp: isAugmenting_def cf.isSimplePath_def)
        hence "(u,v)\<in>E \<or> (v,u)\<in>E"
          by (auto simp: residualGraph_def Graph.E_def split: split_if_asm)
      } note edge_or_swap = this 

      show ?thesis  
        apply (rule ext)
        unfolding cf.augment_cf_def
        apply (auto 
          simp: augment_def augmentingFlow_def cf'_def f'_def residualGraph_def
          split: prod.splits
          dest: aux edge_or_swap
          )
        apply (simp add: no_parallel_edge')
        apply (subst diff_diff_right[rule_format])
        apply (erule order_trans[OF bn_smallerI])
        apply (auto simp: residualGraph_def) []

        apply (rule diff_add_assoc2)
        apply (simp add: capacity_cons)
        done
    qed    

    lemma augmenting_path_contains_bottleneck:
      assumes "isAugmenting p"
      obtains e where "e\<in>set p" "cf e = bottleNeck p" 
    proof -  
      interpret cf!: Graph cf .
      from assms have "p\<noteq>[]" by (auto simp: isAugmenting_def s_not_t)
      hence "{cf e | e. e \<in> set p} \<noteq> {}" by (cases p) auto
      with Min_in[OF aug_flows_finite this, folded bottleNeck_def]
        obtain e where "e\<in>set p" "cf e = bottleNeck p" by auto
      thus ?thesis by (blast intro: that)
    qed  
        
  
    (* TODO: Move,Rename! This lemma looks more on the same level than the original one.*)    
    lemma bottleNeck_gzero': "isAugmenting p \<Longrightarrow> 0<bottleNeck p"
      using bottleNeck_gzero[of p] by (auto simp: isAugmenting_def Graph.isSimplePath_def)
  
    lemma shortest_path_decr_ek_measure:
      fixes p
      assumes SP: "Graph.shortestPath cf s p t"
      defines "f' \<equiv> augment (augmentingFlow p)"
      defines "cf' \<equiv> residualGraph f'"
      shows "Graph.ekMeasure cf' s t < Graph.ekMeasure cf s t"
    proof -
      interpret cf!: Graph cf .
      interpret cf'!: Graph cf' .
  
      from SP have AUG: "isAugmenting p" 
        unfolding isAugmenting_def cf.shortestPath_alt by simp
  
      note [simp] = bottleNeck_gzero'[OF AUG]  
  
      have cf'_alt: "cf' = cf.augment_cf (set p) (bottleNeck p)"
        using augment_alt[OF AUG] unfolding cf'_def f'_def by simp
  
      obtain e where
        EIP: "e\<in>set p" and EBN: "cf e = bottleNeck p"
        by (rule augmenting_path_contains_bottleneck[OF AUG]) auto
  
      have ENIE': "e\<notin>cf'.E" 
        using cf.augment_saturate[OF EIP] EBN by (simp add: cf'_alt)
      
      show ?thesis 
        apply (rule cf.measure_decr(2))
        apply (simp_all add: resV_netV finite_V)
        apply (rule SP)
        apply (rule order_refl)
        apply (rule conjI)
          apply (auto simp: cf'_alt cf.augment_cf_def Graph.E_def) []
          using augmenting_edge_no_swap[OF AUG]
          apply (simp add: cf'_alt cf.augment_cf_def Graph.E_def; fastforce) []
          
        apply (auto simp: cf'_alt cf.augment_cf_def Graph.E_def) []
        using EIP ENIE' apply auto []
        done
    qed    
  end


  context Network 
  begin

(*     definition "fofu \<equiv> do {
      let f = (\<lambda>_. 0);

      WHILET 
        (\<lambda>f. \<exists>p. NFlow.isAugmenting c s t f p) 
        (\<lambda>f. do {
          p \<leftarrow> SPEC (\<lambda>p. NFlow.isAugmenting c s t f p);
          let f' = NFlow.augmentingFlow c f p;
          let f = NFlow.augment c f f';
          RETURN f
        })
        f
    }"
 *)
 

    definition "find_augmenting_spec f \<equiv> ASSERT (NFlow c s t f) \<guillemotright> 
      SPEC (\<lambda>Some p \<Rightarrow> NFlow.isAugmenting c s t f p | None \<Rightarrow> \<forall>p. \<not>NFlow.isAugmenting c s t f p)"

    abbreviation "fofu_invar \<equiv> \<lambda>(f,brk). 
            NFlow c s t f 
          \<and> (brk \<longrightarrow> (\<forall>p. \<not>NFlow.isAugmenting c s t f p))
        "  

    definition "fofu \<equiv> do {
      let f = (\<lambda>_. 0);

      (f,_) \<leftarrow> WHILEIT fofu_invar
        (\<lambda>(f,brk). \<not>brk) 
        (\<lambda>(f,_). do {
          p \<leftarrow> find_augmenting_spec f;
          case p of 
            None \<Rightarrow> RETURN (f,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (NFlow.isAugmenting c s t f p);
              let f' = NFlow.augmentingFlow c f p;
              let f = NFlow.augment c f f';
              RETURN (f, False)
            }  
        })
        (f,False);
      RETURN f 
    }"


    lemma fofu_total_correct: "fofu \<le> SPEC (\<lambda>f. isMaxFlow c s t f)"
      unfolding fofu_def find_augmenting_spec_def
      apply (refine_vcg)
      apply clarsimp_all
      proof -
        show "NFlow c s t (\<lambda>_. 0)" unfolding NFlow_def Flow_def using Network_axioms by (auto simp: s_node t_node)  

        let ?S = "measure (\<lambda>f. (\<Sum>e\<in> outgoing s. c e) - Flow.val c s f) <*lex*> measure (\<lambda>True \<Rightarrow> 0 | False \<Rightarrow> 1)"
        show "wf ?S" by auto

        {
          fix f p
          assume asm1: "NFlow c s t f"
          assume asm2: "NFlow.isAugmenting c s t f p"
          have "Flow (residualGraph f) s t (NFlow.augmentingFlow c f p)"
            (is "Flow _ _ _ ?F'") using NFlow.augFlow_resFlow[OF asm1 asm2] .
          then have "Flow c s t (NFlow.augment c f ?F')" (is "Flow _ _ _ ?F''")
            using NFlow.augment_flow_presv[OF asm1] by auto
          then show "NFlow c s t ?F''" unfolding NFlow_def using Network_axioms by blast
          then interpret F''!: NFlow c s t ?F'' .

          {
            {
              have "Graph.isPath (residualGraph f) s p t" 
                using asm2 NFlow.isAugmenting_def[OF asm1] Graph.isSimplePath_def by auto
              then have "0 < NFlow.bottleNeck c f p" using NFlow.bottleNeck_gzero[OF asm1] by auto
              then have "Flow.val (residualGraph f) s (NFlow.augmentingFlow c f p) > 0"
                using NFlow.augFlow_val[OF asm1 asm2] by auto
              then have "Flow.val c s ?F'' > Flow.val c s f" using asm2 
                NFlow.augment_flow_value[OF asm1 NFlow.augFlow_resFlow[OF asm1]] by auto
            } 
            moreover 
            { 
              have "outgoing s \<subseteq> E" unfolding outgoing_def by auto
              then have "finite (outgoing s)" using finite_E finite_subset by auto
              moreover have "\<And>e. e \<in> outgoing s \<Longrightarrow> ?F'' e \<le> c e" using F''.capacity_cons by auto
              ultimately have "(\<Sum>e \<in> outgoing s. ?F'' e) \<le> (\<Sum>e \<in> outgoing s. c e)"
                using setsum_mono by blast
              then have "F''.val \<le> (\<Sum>e \<in> outgoing s. c e)" using F''.val_alt by auto
            }
            ultimately show "((NFlow.augment c f
               (NFlow.augmentingFlow c f p), False),
              (f,False)) \<in> ?S"
              by simp   
          }
        }
        {
          fix f
          assume asm1: "NFlow c s t f"
          assume asm2: "(\<forall>p. \<not>NFlow.isAugmenting c s t f p)"
          show "isMaxFlow c s t f" using NFlow.maxFlow_iff_noAugPath[OF asm1] asm2 by blast
        }
        { fix f
          show "((f, True), f, False) \<in> ?S" by auto
        }  

        {
          fix f
          assume "NFlow c s t f" then interpret NFlow c s t f .
          
          assume "isAugmenting []"
          thus False unfolding isAugmenting_def Graph.isSimplePath_def
            using s_not_t
            by (simp add: Graph.isPath.simps)

        }

      qed   

(*    definition flowOf :: "graph \<Rightarrow> flow" where
      "flowOf cf = (\<lambda>(u, v).
        if (u, v) \<in> E then
          cf (v, u)
        else
          0)"

    definition "fofu_t \<equiv> do {
      let f = (\<lambda>_. 0);
      let c' = residualGraph c f;

      WHILET 
        (\<lambda>g. \<exists>p. Graph.isSimplePath g s p t) 
        (\<lambda>g. do {
          p \<leftarrow> SPEC (\<lambda>p. Graph.isSimplePath g s p t);
          let c' = NFlowExt.augment g (NFlow.bottleNeck c (flowOf g) p) p;
          RETURN c'
        })
        c';
      RETURN (flowOf c')
    }" 
*)     
    
(*    definition (in -) "res_graph_of c s f \<equiv> \<lparr>
      g_V = UNIV,
      g_E = Graph.E (residualGraph c f),
      g_V0 = {s}
    \<rparr>"
*)

  (*
    definition (in -) "find_augmenting2 c s t f \<equiv> do {
      p \<leftarrow> Graph.dfs (residualGraph c f) s t;
      RETURN (p)
    }"
    
    
    lemma (in NFlow) "Graph.E cf \<subseteq> Graph.V cf \<times> Graph.V cf"
      using Graph.V_def by auto

    lemma (in NFlow) res_graph_of_is_fb_graph: "fb_graph (res_graph_of c s f)"
      unfolding res_graph_of_def
      apply default
      apply clarsimp_all
      proof -  
        fix v
        have "Graph.E cf \<subseteq> Graph.V cf \<times> Graph.V cf" using Graph.V_def by auto
        from finite_subset[OF this] finite_V have "finite (Graph.E cf)"
          by (simp add: resV_netV)
        thus "finite (Graph.E cf `` {v})"
          using finite_Image by blast
      qed    

    lemma find_augmenting2_refine: "find_augmenting2 c s t f \<le> find_augmenting_spec f"
      unfolding find_augmenting2_def find_augmenting_spec_def find_path0_spec_def
      apply (rule refine_IdD)
      apply refine_vcg
      apply (simp add: NFlow.res_graph_of_is_fb_graph)
      apply (auto split: option.split simp: find_path0_pred_def res_graph_of_def)
      proof -
        assume "NFlow c s t f"
        then interpret NFlow c s t f .

        {
          assume "(s, t) \<notin> (Graph.E cf)\<^sup>*"
          with path_is_rtrancl have NP: "\<forall>p. \<not>path (Graph.E cf) s p t"
            by metis
  
          fix p
          assume "isAugmenting p" 
          hence "Graph.isPath cf s p t"  
            unfolding isAugmenting_def Graph.isSimplePath_def by simp
          from Graph.path_conv2[OF this] NP show False by blast
        }  

        {
          fix p
          assume 1: "path (Graph.E cf) s p t" and 2: "distinct p" "t \<notin> set p"
          from Graph.path_conv1 1 have "Graph.isPath cf s (path_conv1 (p,t)) t" by simp
          with distinct_conv[of p t] 2 have "Graph.isSimplePath cf s (path_conv1 (p,t)) t"
            unfolding Graph.isSimplePath_def 
            by (cases p) (auto simp: pathVertices_alt)
          thus "isAugmenting (path_conv1 (p, t))" unfolding isAugmenting_def .
        }  
      qed  
*)

    (* TODO: Move *)  
    lemma (in NFlow) finite_cf_reachable[simp, intro!]: "finite (Graph.reachable cf s)"
      by (metis Graph.reachable_ss_V finite_V resV_netV rev_finite_subset s_node)

    lemma (in NFlow) bfs_refines_augmenting_spec: "Graph.bfs cf s t \<le> find_augmenting_spec f"
      apply (rule order_trans)
      apply (rule Graph.bfs_correct)
      apply simp
      apply (auto 
        simp: find_augmenting_spec_def isAugmenting_def resV_netV finite_V
        simp: Graph.isReachable_def Graph.isSimplePath_def
        simp: pw_le_iff refine_pw_simps
        split: option.splits
        )
      done


(*TODO: Refine f to cf
  We have: f(u,v) = if c(u,v)>0 then c(u,v) - cf(u,v) else 0
    residualGraph c f = cf
    augment: cf (u,v) -= f(u,v)
    bottleNeck: Uses cf

    initialization: cf = c
*)


    definition "fofu2 \<equiv> do {
      let f = (\<lambda>_. 0);

      (f,_) \<leftarrow> WHILEIT fofu_invar
        (\<lambda>(f,brk). \<not>brk) 
        (\<lambda>(f,_). do {
          p \<leftarrow> Graph.bfs (residualGraph f) s t;
          case p of 
            None \<Rightarrow> RETURN (f,True)
          | Some p \<Rightarrow> do {
              ASSERT (NFlow.isAugmenting c s t f p);
              ASSERT (p\<noteq>[]);
              let f = NFlow.augment c f (NFlow.augmentingFlow c f p);
              RETURN (f, False)
            }  
        })
        (f,False);
      RETURN f 
    }"

    lemma fofu2_refine: "fofu2 \<le> fofu"
      apply (rule refine_IdD)
      unfolding fofu_def fofu2_def
      apply (refine_rcg)
      apply refine_dref_type
      apply (auto simp add: NFlow.bfs_refines_augmenting_spec)
      done

  end

  fun bottleNeck2 :: "graph \<Rightarrow> flow \<Rightarrow> path \<Rightarrow> nat" where
    "bottleNeck2 c f [] = 0"
  | "bottleNeck2 c f [e] = Graph.residualGraph c f e"
  | "bottleNeck2 c f (e#p) = min (Graph.residualGraph c f e) (bottleNeck2 c f p)"
  
  definition augment'_edge where "augment'_edge c x \<equiv> (\<lambda>e f. 
      if c e > 0 then
        f ( e := f e + x)
      else  
        f ( prod.swap e := f (prod.swap e) - x)
    )" 

  definition augment' :: "graph \<Rightarrow> path \<Rightarrow> nat \<Rightarrow> flow \<Rightarrow> flow" where
    "augment' c p x f = fold (augment'_edge c x) p f"
    
  definition augment_g :: "graph \<Rightarrow> flow \<Rightarrow> flow \<Rightarrow> flow" where
    "augment_g c f f' \<equiv> \<lambda>(u, v).
      if (u, v) \<in> Graph.E c then
        f (u, v) + f' (u, v) - f' (v, u)
      else
        f (u, v)"
      
  definition capacityFlow :: "path \<Rightarrow> capacity \<Rightarrow> flow" where
    "capacityFlow p cap \<equiv> \<lambda>(u, v).
      if (u, v) \<in> (set p) then
        cap
      else
        0"        
       
  (* this lemma was not used *)      
  lemma augment'_idemp: "\<lbrakk>e \<notin> set p; prod.swap e \<notin> set p\<rbrakk> \<Longrightarrow> (augment' c p x f) e = f e"
    proof (induction p arbitrary: f)
      case Nil
        thus ?case unfolding augment'_def by auto
    next
      case (Cons e1 p1)
        have "(augment' c (e1 # p1)) x f e = (augment' c p1 x (augment'_edge c x e1 f)) e"
          (is "?L = _") unfolding augment'_def by auto
        then have "?L = (augment'_edge c x e1 f) e" using Cons.prems Cons.IH by auto
        moreover have "(augment'_edge c x e1 f) e = f e"
          unfolding augment'_edge_def using Cons.prems by auto
        ultimately show ?case by simp
    qed
      
  lemma augment'_assoc: "\<lbrakk>e \<notin> set p; prod.swap e \<notin> set p\<rbrakk> \<Longrightarrow>
    augment' c p x (augment'_edge c x e f) = augment'_edge c x e (augment' c p x f)"
    proof (induction p arbitrary: f)
      case Nil
        thus ?case unfolding augment'_def by auto
    next
      case (Cons e1 p1)
        have "augment' c (e1 # p1) x (augment'_edge c x e f) = 
          augment' c p1 x (augment'_edge c x e1 (augment'_edge c x e f))"
          (is "?L = _") unfolding augment'_def by auto
        moreover {
          have "e \<noteq> e1" and "e \<noteq> prod.swap e1" using Cons.prems by auto
          then have "augment'_edge c x e1 (augment'_edge c x e f) = 
            augment'_edge c x e (augment'_edge c x e1 f)" unfolding augment'_edge_def by auto
        }
        ultimately have "?L = augment'_edge c x e (augment' c p1 x (augment'_edge c x e1 f))"
          using Cons.prems Cons.IH[of "augment'_edge c x e1 f"] by auto
        thus ?case using augment'_def by auto
    qed

  (*export_code bottleNeck2 augment' in SML*)

  
  context NFlow begin

    (*
    lemma stupid_fin_aux_lemma: 
      "{cf (a, b) |a b. a = aa \<and> b = ba \<or> (a, b) \<in> set va} \<subseteq> cf ` set va \<union> {cf (aa,ba)}"
      by auto

      
    lemma bottleNeck2_refine: "p\<noteq>[] \<Longrightarrow> bottleNeck2 c f p = bottleNeck p"
      apply (induction c\<equiv>c f\<equiv>f p rule: bottleNeck2.induct)
      unfolding bottleNeck_def
      apply auto []
      apply auto []
      apply auto []
      apply (subst Min_insert[symmetric])      
      apply (rule finite_subset[OF stupid_fin_aux_lemma]; auto)
      apply auto []
      apply (fo_rule arg_cong)
      apply auto
      done
    *)  

    lemma augment'_refine_pre1: "\<lbrakk>distinct p; \<forall>(u, v) \<in> set p. (v, u) \<notin> set p;
      \<forall>(u, v) \<in> set p. c (u, v) > 0 \<or> c (v, u) > 0\<rbrakk> \<Longrightarrow> 
      augment' c p x f = augment_g c f (capacityFlow p x)"
      proof (induction p)
        case Nil
          thus ?case unfolding augment'_def augment_g_def capacityFlow_def by auto
      next
        case (Cons e p)
          have "augment' c (e # p) x f = augment' c p x (augment'_edge c x e f)"
            (is "?L = ?R")unfolding augment'_def by auto
          moreover have "?R =  augment'_edge c x e (augment' c p x f)"
            using Cons.prems augment'_assoc by auto
          moreover have "augment' c p x f = augment_g c f (capacityFlow p x)"
            using Cons.prems Cons.IH by auto
          ultimately have "?L = augment'_edge c x e (augment_g c f (capacityFlow p x))"
            (is "_ = ?R") by simp
          moreover have "?R = augment_g c f (capacityFlow (e # p) x)"
            proof -
              {
                fix a
                have "?R a = (augment_g c f (capacityFlow (e # p) x)) a"
                  proof (cases "a \<noteq> e \<and> a \<noteq> prod.swap e")
                    case True
                      then have "?R a = (augment_g c f (capacityFlow p x)) a"
                        unfolding augment'_edge_def by auto
                      moreover {
                        have "(capacityFlow p x) a = (capacityFlow (e # p) x) a"
                          unfolding capacityFlow_def using True by simp
                        moreover have "(capacityFlow p x) (prod.swap a) = (capacityFlow (e # p) x)
                          (prod.swap a)" by (smt True capacityFlow_def insert_iff 
                          list.set(2) old.prod.case prod.swap_def swap_swap)
                        ultimately have "(augment_g c f (capacityFlow p x)) a = 
                          (augment_g c f (capacityFlow (e # p) x)) a" unfolding augment_g_def
                          by (smt old.prod.case prod.sel(1) prod.swap_def swap_swap)
                      }
                      ultimately show ?thesis by simp
                  next
                    case False
                      have "e \<noteq> prod.swap e" by (metis (no_types, lifting) 
                        Cons.prems(2) list.set_intros(1) prod.sel(1) prod.swap_def splitD)
                      have "a = e \<or> a = prod.swap e" using False by simp
                      thus ?thesis
                        proof
                          assume "a = e"
                          then have "a \<noteq> prod.swap e" using `e \<noteq> prod.swap e` by simp
                          show ?thesis
                            proof (cases "c e > 0")
                              case True
                                have "c a > 0" using `a = e` `c e > 0` by blast
                                have "augment'_edge c x e (augment_g c f (capacityFlow p x)) a =
                                  augment_g c f (capacityFlow p x) a + x" (is "?L = ?R1 + x") 
                                  unfolding augment'_edge_def using True `a = e` by simp
                                moreover have "?R1 = f a + (capacityFlow p x) a -
                                  (capacityFlow p x) (prod.swap a)" unfolding augment_g_def E_def
                                  using `c a > 0` by (smt mem_Collect_eq not_gr0 old.prod.case
                                  prod.sel(1) prod.swap_def swap_swap)                                
                                moreover have "(capacityFlow p x) a = 0" unfolding capacityFlow_def
                                  using `a = e` Cons.prems(1) by auto
                                moreover {
                                  have "prod.swap a \<notin> set p" using `a = e` Cons.prems(2) by auto
                                  then have "(capacityFlow p x) (prod.swap a) = 0"
                                    unfolding capacityFlow_def by (simp add: prod.swap_def) 
                                }
                                ultimately have "?L = f a + x" by simp
                                have "augment_g c f (capacityFlow (e # p) x) a = f a + 
                                  (capacityFlow (e # p) x) a - (capacityFlow (e#p) x) (prod.swap a)"
                                  (is "?R = _") unfolding augment_g_def E_def using `c a > 0` 
                                  by (smt mem_Collect_eq not_gr0 old.prod.case 
                                    prod.sel(1) prod.swap_def swap_swap)
                                moreover have "(capacityFlow (e # p) x) a = x"
                                  unfolding capacityFlow_def using `a = e` by auto
                                moreover {
                                  have "prod.swap a \<notin> set (e # p)"using `a = e` Cons.prems(2)
                                    by (metis list.set_intros(1) prod.swap_def
                                    splitD swap_simp swap_swap)
                                  then have "(capacityFlow (e # p) x) (prod.swap a) = 0"
                                    unfolding capacityFlow_def by (simp add: prod.swap_def)
                                }
                                ultimately have "?R = f a + x" by simp
                                show ?thesis using `?L = f a + x` `?R = f a + x` by simp
                            next
                              case False
                                have "augment'_edge c x e (augment_g c f (capacityFlow p x)) a =
                                  augment_g c f (capacityFlow p x) a"
                                  unfolding augment'_edge_def using False `a \<noteq> prod.swap e` by simp
                                moreover {
                                  have "c a = 0" using `a = e` False by blast
                                  then have "\<And>f'. augment_g c f f' a = f a" unfolding augment_g_def
                                    E_def by (smt gr0I le_0_eq mem_Collect_eq splitE2 split_conv)
                                }
                                ultimately show ?thesis by simp
                            qed
                        next
                          assume "a = prod.swap e"
                          then have "a \<noteq> e" using `e \<noteq> prod.swap e` by simp
                          thus ?thesis
                            proof (cases "c (prod.swap e) > 0")
                              case True
                                have "c a > 0" using `a = prod.swap e` True by blast
                                have "c e = 0" using no_parallel_edge True
                                  by (xmetis not_gr0 prod.swap_def swap_simp swap_swap)
                                then have "augment'_edge c x e (augment_g c f (capacityFlow p x)) a 
                                  = augment_g c f (capacityFlow p x) a - x" (is "?L = ?R1 - x")
                                  unfolding augment'_edge_def using False `a = prod.swap e` by simp
                                moreover have "?R1 = f a + (capacityFlow p x) a -
                                  (capacityFlow p x) (prod.swap a)" unfolding augment_g_def E_def
                                  using `c a > 0` by (smt mem_Collect_eq not_gr0 old.prod.case
                                  prod.sel(1) prod.swap_def swap_swap)
                                moreover {
                                  have "a \<notin> set p" using `a = prod.swap e` Cons.prems(2) by auto
                                  then have "(capacityFlow p x) a = 0"
                                    unfolding capacityFlow_def by (simp add: prod.swap_def)
                                }
                                moreover {
                                  have "prod.swap a \<notin> set p" 
                                    using `a = prod.swap e` Cons.prems(1) by auto
                                  then have "(capacityFlow p x) (prod.swap a) = 0"
                                    unfolding capacityFlow_def by (simp add: prod.swap_def)
                                }
                                ultimately have "?L = f a - x" by simp
                                have "augment_g c f (capacityFlow (e # p) x) a = f a + 
                                  (capacityFlow (e # p) x) a - (capacityFlow (e#p) x) (prod.swap a)"
                                  (is "?R = _") unfolding augment_g_def E_def using `c a > 0` 
                                  by (smt mem_Collect_eq not_gr0 old.prod.case 
                                    prod.sel(1) prod.swap_def swap_swap)
                                moreover {
                                  have "a \<notin> set (e # p)" using `a = prod.swap e` Cons.prems(2)
                                    by (metis (no_types, lifting) list.set_intros(1)
                                    prod.sel(1) prod.swap_def splitD swap_swap)
                                  then have "(capacityFlow (e # p) x) a = 0"
                                    unfolding capacityFlow_def by (simp add: prod.swap_def)
                                }
                                moreover have "(capacityFlow (e # p) x) (prod.swap a) = x"
                                  unfolding capacityFlow_def using `a = prod.swap e` by auto
                                ultimately have "?R = f a - x" by simp
                                show ?thesis using `?L = f a - x` `?R = f a - x` by simp
                            next
                              case False
                                then have "c a = 0" using `a = prod.swap e` by blast
                                show ?thesis
                                  proof (cases "c e > 0")
                                    case True
                                      then have 
                                        "augment'_edge c x e (augment_g c f (capacityFlow p x)) a =
                                          augment_g c f (capacityFlow p x) a" 
                                        unfolding augment'_edge_def using `a \<noteq> e` by simp
                                      moreover have "\<And>f'. augment_g c f f' a = f a"
                                        unfolding augment_g_def E_def using `c a = 0` 
                                        by (smt gr0I le_0_eq mem_Collect_eq splitE2 split_conv)
                                      ultimately show ?thesis by simp
                                  next
                                    case False
                                      thus ?thesis using `\<not>0 < c(prod.swap e)` Cons.prems(3) by auto
                                  qed
                            qed
                        qed
                  qed
              }
              thus ?thesis by auto
            qed
          ultimately show ?case by simp
      qed
  
    lemma augment'_refine_pre2: 
      assumes "distinct p" and "\<forall>(u, v) \<in> set p. (v, u) \<notin> set p" and "p \<noteq> []"
      assumes "\<forall>(u, v) \<in> set p. c (u, v) > 0 \<or> c (v, u) > 0"
      shows "augment' c p (bottleNeck p) f = augment (augmentingFlow p)"
      proof -
        {
          fix f'
          have "\<forall> e. c e = 0 \<longrightarrow> f e = 0" using capacity_cons by (metis le_0_eq)
          then have "augment_g c f f' = augment f'"
            unfolding augment_g_def augment_def E_def by auto  
        }
        then have "augment_g c f = augment" by auto
        moreover have "capacityFlow p (bottleNeck p) = augmentingFlow p"
          unfolding capacityFlow_def augmentingFlow_def by simp
        (*moreover have "bottleNeck2 c f p = bottleNeck p" using assms(3)
          proof (induction p)  ** NOTE: This is a DUP of bottleNeck2_refine!
            case Nil
              thus ?case by simp
          next
            case (Cons e p)
              thus ?case
                proof (cases "p = []")
                  case True
                    have "{cf e1 | e1. e1 \<in> {e}} = {cf e}" by blast
                    then have "bottleNeck (e # p) = cf e" 
                      unfolding bottleNeck_def using True by simp
                    then show ?thesis using True by simp
                next 
                  case False
                    obtain e1 p1 where obt: "p = e1 # p1" using False by (meson bottleNeck2.elims)
                    {
                      have f1: "finite {cf e1 |e1. e1 \<in> {e}}" using finite.simps by fastforce
                      have f2: "{cf e1 |e1. e1 \<in> {e}} \<noteq> {}" by blast
                      have f3: "finite {cf e1 |e1. e1 \<in> set p}"
                        by (metis (no_types) Collect_mem_eq List.finite_set finite_image_set)
                      have f4: "{cf e1 |e1. e1 \<in> set p} \<noteq> {}" using False by (metis 
                        (mono_tags, lifting) Collect_empty_eq all_not_in_conv set_empty2)
                      note Lattices_Big.linorder_class.Min_Un[OF f1 f2 f3 f4]
                      moreover have "{cf e1 |e1. e1 \<in> {e}} \<union> {cf e1 |e1. e1 \<in> set p} = 
                        {cf e1 |e1. e1 \<in> set (e # p)}" by auto
                      moreover have "{cf e1 | e1. e1 \<in> {e}} = {cf e}" by blast
                      ultimately have "bottleNeck (e # p) = min (cf e) (bottleNeck p)" 
                        unfolding bottleNeck_def by auto
                    }
                    moreover have "bottleNeck p = bottleNeck2 c f p" using Cons.IH False by simp
                    ultimately have "min (cf e) (bottleNeck2 c f p) = bottleNeck (e # p)" by simp
                    thus ?thesis using bottleNeck2.simps(3)[of c f e e1 p1] obt by auto
                qed
          qed*)
        moreover note augment'_refine_pre1[OF assms(1) assms(2) assms(4)]
        ultimately show ?thesis by simp
      qed
  
    lemma augment'_refine_AXIOMATIC: "\<lbrakk>p \<noteq> []; Graph.isSimplePath cf u p v\<rbrakk> \<Longrightarrow> 
      augment' c p (bottleNeck p) f = augment (augmentingFlow p)"
      proof -
        assume asm1: "p \<noteq> []"
        assume asm2: "Graph.isSimplePath cf u p v"
        have "distinct p" using Graph.isSPath_distinct asm2 by simp
        moreover have "(\<forall>(u, v) \<in> set p. (v, u) \<notin> set p)" 
          using Graph.isSPath_nt_parallel asm2 by simp
        moreover have "\<forall>(u, v) \<in> set p. c (u, v) > 0 \<or> c (v, u) > 0"
          proof (rule ccontr)
            assume "\<not> (\<forall>(u, v) \<in> set p. c (u, v) > 0 \<or> c (v, u) > 0)"
            then obtain x y where "(x, y) \<in> set p" and "c (x, y) = 0" and "c (y, x) = 0" by blast
            then have "cf (x, y) > 0" 
              using asm2 Graph.isSimplePath_def Graph.isPath_edgeset Graph.E_def by auto
            moreover have "cf (x, y) = 0" using `c (x, y) = 0` `c (y, x) = 0` 
              unfolding residualGraph_def by (auto simp: E_def)
            ultimately show "False" by simp
          qed
        ultimately show ?thesis using asm1 augment'_refine_pre2 by simp
      qed


  end

  text \<open>
    The next refinement step works on residual graphs, which are, abstractly,
    represented by a graph and a flow. 
    \<close>

  definition [simp]: "zero_flow \<equiv> (\<lambda>_. 0)"

  abbreviation (input) valid_node :: "graph \<Rightarrow> node \<Rightarrow> bool" where
    "valid_node c u \<equiv> u \<in> Graph.V c"

  abbreviation (input) valid_edge :: "graph \<Rightarrow> edge \<Rightarrow> bool" where
    "valid_edge c \<equiv> \<lambda>(u,v). u\<in>Graph.V c \<and> v\<in>Graph.V c"

(*
  abbreviation (input) has_edge :: "graph \<Rightarrow> edge \<Rightarrow> bool" where
    "has_edge \<equiv> \<lambda>c e. c e > 0"

  definition rg_get_flow :: "res_graph \<Rightarrow> edge \<Rightarrow> capacity" where "rg_get_flow \<equiv> \<lambda>(ps,c,f) e. f e"
  definition rg_set_flow :: "res_graph \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> res_graph" where "rg_set_flow \<equiv> \<lambda>(ps,c,f) e v. (ps,c,(f(e := v)))"
  definition rg_get_cap :: "res_graph \<Rightarrow> edge \<Rightarrow> capacity" where "rg_get_cap \<equiv> \<lambda>(ps,c,f) e. c e"

  definition rg_res_graph :: "res_graph \<Rightarrow> graph" where "rg_res_graph \<equiv> uncurry residualGraph o snd"

  definition rg_pred_succ :: "res_graph \<Rightarrow> node \<Rightarrow> node list" where
    "rg_pred_succ \<equiv> \<lambda>(ps,_,_) u. ps u"

  lemma zero_res_graph_valid: "abs_is_pred_succ ps c \<Longrightarrow> rg_valid (zero_res_graph ps c)"
    unfolding zero_res_graph_def rg_valid_def by auto
*)

  lemma (in NFlow) augmenting_valid_edges: "isAugmenting p \<Longrightarrow> e\<in>set p \<Longrightarrow> valid_edge c e"
    apply (cases e)
    apply (clarsimp simp: isAugmenting_def Graph.isSimplePath_def) []
    apply (drule (1) Graph.isPath_edgeset)
    unfolding resV_netV[symmetric]
    apply (auto simp: Graph.V_alt)
    done


  definition cap_of_edge :: "graph \<Rightarrow> flow \<Rightarrow> edge \<Rightarrow> capacity nres" where
    "cap_of_edge c f e \<equiv> do { 
      ASSERT (valid_edge c e);
      let cuv = c e;
      if cuv > 0 then RETURN (cuv - f e)
      else RETURN (f (prod.swap e))
    }"

  lemma (in NFlow) cap_of_edge_refine: "valid_edge c e \<Longrightarrow> cap_of_edge c f e \<le> RETURN (cf e)" 
    unfolding residualGraph_def cap_of_edge_def 
    using capacity_cons
    apply (auto split: prod.split simp: E_def)
    by (metis le_0_eq)     

  definition "bottleneck_impl c f p \<equiv> 
    case p of
      [] \<Rightarrow> RETURN 0
    | (e#p) \<Rightarrow> do {
        cap \<leftarrow> cap_of_edge c f e;
        ASSERT (distinct p);
        FOREACH (set p) (\<lambda>e cap. do {
          cape \<leftarrow> cap_of_edge c f e;
          RETURN (min cape cap)
        }) cap
      }"

  lemma (in NFlow) bottleneck_impl_refine: 
    assumes AUG: "isAugmenting p" "p\<noteq>[]"
    shows "bottleneck_impl c f p \<le> SPEC (\<lambda>r. r = bottleNeck p)"
  proof -
    (* TODO: These definitions are a bit unwieldy to handle, and blow up 
      this straightforward proof *)
    def spec \<equiv> "\<lambda>r. r=bottleNeck p"
    def bn \<equiv> "\<lambda>s. Min (cf`s)"

    have [simp]: "\<And>e. bn {e} = cf e" by (auto simp: bn_def)
    have [simp]: "\<And>(e::edge) (s::edge set). \<lbrakk>finite s; s\<noteq>{}\<rbrakk> \<Longrightarrow> bn (insert e s) = min (cf e) (bn s)"
      unfolding bn_def
      by auto 

    from AUG obtain e p' where [simp]: "p=e#p'" by (auto simp: neq_Nil_conv)

    from AUG(1) have [simp]: "e\<notin>set p'" "distinct p'"
      by (auto simp: isAugmenting_def dest: Graph.isSPath_distinct)

    thus ?thesis
      apply (subst spec_def[symmetric])
      unfolding bottleneck_impl_def
      apply (simp)
      
      apply (refine_vcg 
          order_trans[OF cap_of_edge_refine]
          FOREACH_rule[where I="\<lambda>it cap. cap = bn (insert e (set p - it))"])
      using augmenting_valid_edges[OF AUG(1)] apply auto [2]
      apply auto []
      apply (auto simp: insert_Diff_if) [] 
      using augmenting_valid_edges[OF AUG(1)] apply auto [2]
      apply (subst it_step_insert_iff)
        apply auto []
        apply auto []
        apply (simp only: insert_commute[of e])
        apply simp

      apply (auto simp: spec_def bn_def bottleNeck_def)
      apply (fo_rule arg_cong)
      apply (cases e)
      apply auto
      done
  qed 

  (*lemma rg_valid_edge_swap[simp]: "valid_edge c (prod.swap e) \<longleftrightarrow> valid_edge c e"  
    by (auto simp: )*)

  definition augment_edge_impl :: "graph \<Rightarrow> flow \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> flow nres" where
    "augment_edge_impl c f e x \<equiv> do {         
      ASSERT (valid_edge c e);
      if c e > 0 then do {
        RETURN (f (e := f e + x))
      } else do {
        let e = prod.swap e;
        ASSERT (valid_edge c e);
        RETURN (f ( e := f e - x))
      }
    }"

  lemma augment_edge_impl_refine: "\<lbrakk>valid_edge c e\<rbrakk> 
    \<Longrightarrow> augment_edge_impl c f e x \<le> RETURN (augment'_edge c x e f)"
    unfolding augment_edge_impl_def augment'_edge_def
    by (auto)


  definition augment_impl :: "graph \<Rightarrow> flow \<Rightarrow> path \<Rightarrow> capacity \<Rightarrow> flow nres" where
    "augment_impl c f p x \<equiv> do {
      RECT (\<lambda>D. \<lambda>
        ([],f) \<Rightarrow> RETURN f
      | (e#p,f) \<Rightarrow> do {
          f \<leftarrow> augment_edge_impl c f e x;
          D (p,f)
        }  
      ) (p,f)
    }"

  lemma augment_impl_refine_pre: 
    assumes "\<forall>e\<in>set p. valid_edge c e"
    shows "augment_impl c f p x \<le> RETURN (augment' c p x f)"
    using assms
    apply (induction p arbitrary: f)
    apply (simp add: augment'_def)
    apply (simp add: augment_impl_def)
    apply (subst RECT_unfold, refine_mono)
    apply simp

    apply (simp add: augment_impl_def)
    apply (subst RECT_unfold, refine_mono)
    apply simp
    apply (refine_vcg order_trans[OF augment_edge_impl_refine])
    apply simp
    apply simp
    apply (rule order_trans)
    apply clarsimp
    apply rprems
    apply (simp add: augment'_def)
    done

  context NFlow begin  
  
    thm augment'_refine_AXIOMATIC
  
    lemma augment_impl_refine: 
      assumes "isAugmenting p" "p \<noteq> []" 
      shows "augment_impl c f p (bottleNeck p) \<le> RETURN (augment (augmentingFlow p))"
      apply (rule order_trans)
      apply (rule augment_impl_refine_pre)
        using augmenting_valid_edges[OF \<open>isAugmenting p\<close>]
        apply blast

        using augment'_refine_AXIOMATIC assms
        apply (simp add: isAugmenting_def)
      done
  end      

  definition "augment_flow_impl c f p \<equiv> do {
    ASSERT (p\<noteq>[]);
    x \<leftarrow> bottleneck_impl c f p;
    augment_impl c f p x
  }"

  context NFlow begin
    lemma rg_augment_flow_impl_refine:
      assumes "isAugmenting p" "p \<noteq> []" 
      shows "augment_flow_impl c f p \<le> (RETURN (augment (augmentingFlow p)))"
      unfolding augment_flow_impl_def
      using augment_impl_refine[OF assms] bottleneck_impl_refine[OF assms] \<open>p\<noteq>[]\<close>
      by (auto simp: pw_le_iff refine_pw_simps)

  end

  definition "fofu3_invar c s t \<equiv> Network.fofu_invar c s t"

  (* TODO: ps not actually used here! Remove? *)
  definition "fofu3 ps c s t \<equiv> do {
    ASSERT (Network c s t);
    ASSERT (is_pred_succ ps c);
    let f = zero_flow;

    (f,_) \<leftarrow> WHILEIT (fofu3_invar c s t)
      (\<lambda>(_,brk). \<not>brk) 
      (\<lambda>(f,_). do {
        ASSERT (is_pred_succ ps c);
        ASSERT (NFlow c s t f);
        p \<leftarrow> Graph.bfs (Graph.residualGraph c f) s t;
        case p of 
          None \<Rightarrow> RETURN (f,True)
        | Some p \<Rightarrow> do {
            ASSERT (p\<noteq>[]);
            f \<leftarrow> augment_flow_impl c f p;
            RETURN (f, False)
          }  
      })
      (f,False);
    RETURN f 
  }"

  lemma (in Network) fofu3_refine: 
    assumes [simp]: "is_pred_succ ps c"
    shows "fofu3 ps c s t \<le> fofu2"
  proof -

    show ?thesis
      unfolding fofu3_def fofu2_def fofu3_invar_def
      apply (rule refine_IdD)
      apply xx(refine_rcg NFlow.rg_augment_flow_impl_refine[THEN order_trans])
      apply refine_dref_type
      apply (vc_solve)
      apply unfold_locales []
      apply (assumption|rule refl| intro conjI)+
      done
  qed  

  definition "rg_succ ps c f u \<equiv>  
    filter 
      (\<lambda>v. Graph.residualGraph c f (u,v) > 0) 
      (ps u)"

 
  lemma (in NFlow) rg_succ_ref1: "\<lbrakk>is_pred_succ ps c\<rbrakk> \<Longrightarrow> (rg_succ ps c f u, Graph.E (residualGraph f)``{u}) \<in> \<langle>Id\<rangle>list_set_rel"
    apply (auto simp: list_set_rel_def br_def rg_succ_def Graph.E_def)
    apply (auto simp: is_pred_succ_def residualGraph_def E_def split: split_if_asm)
    done

  definition "rg_succ2 ps c f u \<equiv> do {
    ASSERT (valid_node c u);
    let l = ps u;
    RECT (\<lambda>D l. case l of 
      [] \<Rightarrow> RETURN [] 
    | (v#l) \<Rightarrow> do {
        rl \<leftarrow> D l;
        ASSERT (valid_edge c (u,v));
        x \<leftarrow> cap_of_edge c f (u,v);
        if x > 0 then RETURN (v#rl) else RETURN rl   
      }) l
    }"

  lemma (in NFlow) rg_succ_ref2: "\<lbrakk>is_pred_succ ps c; valid_node c u\<rbrakk> \<Longrightarrow> rg_succ2 ps c f u \<le> RETURN (rg_succ ps c f u)"
  proof -
    def l \<equiv> "ps u"

    assume VN: "valid_node c u"
    assume V: "is_pred_succ ps c"

    have "\<forall>v\<in>set l. valid_edge c (u,v)"
      using V VN 
      by (auto simp: is_pred_succ_def l_def Graph.V_def)

    thus ?thesis
      unfolding rg_succ2_def
      apply refine_vcg
      apply (simp add: VN) []
      apply (simp add: rg_succ_def l_def[symmetric])
  
      apply (induction l)
        apply (simp add: rg_succ_def) apply (subst RECT_unfold, refine_mono)
        apply simp
  
        apply (subst RECT_unfold, refine_mono)
        apply (simp split del: split_if)
        using cap_of_edge_refine
        apply (simp add: pw_le_iff refine_pw_simps) 
        apply fastforce
      done
  qed    

  lemma (in NFlow) rg_succ_ref:
    assumes A: "is_pred_succ ps c"
    assumes B: "u\<in>V"
    shows "rg_succ2 ps c f u \<le> SPEC (\<lambda>l. (l,Graph.E cf``{u}) \<in> \<langle>Id\<rangle>list_set_rel)"
    using rg_succ_ref1[OF A, of u] rg_succ_ref2[OF A B]
    by (auto simp: pw_le_iff refine_pw_simps)


  definition "fofu4 ps c s t \<equiv> do {
    ASSERT (Network c s t);
    ASSERT (is_pred_succ ps c);
    let f = zero_flow;

    (f,_) \<leftarrow> WHILEIT (fofu3_invar c s t)
      (\<lambda>(_,brk). \<not>brk) 
      (\<lambda>(f,_). do {
        ASSERT (is_pred_succ ps c);
        ASSERT (NFlow c s t f);
        p \<leftarrow> Graph.bfs2 (Graph.residualGraph c f) (rg_succ2 ps c f) s t;
        case p of 
          None \<Rightarrow> RETURN (f,True)
        | Some p \<Rightarrow> do {
            ASSERT (p\<noteq>[]);
            f \<leftarrow> augment_flow_impl c f p;
            RETURN (f, False)
          }  
      })
      (f,False);
    RETURN f 
  }"

  lemma fofu4_refine: "fofu4 ps c s t \<le> fofu3 ps c s t"
    unfolding fofu3_def fofu4_def
    apply (rule refine_IdD)
    apply (refine_rcg)
    apply refine_dref_type
    apply vc_solve
    apply (rule refine_IdD)
    apply (rule Graph.bfs2_refine)
    apply simp
    apply (rule NFlow.rg_succ_ref; simp add: NFlow.resV_netV)    
    done

  subsection \<open>Matrix by Array\<close> (* TODO: Move *)

  type_synonym 'a amtx = "nat\<times>nat \<Rightarrow> 'a"
  type_synonym 'a mtx = "'a Heap.array"

  typedecl 'a i_mtx

  definition amtx_new_op :: "'a amtx \<Rightarrow> 'a amtx" where [simp]: "amtx_new_op c \<equiv> c"
  definition amtx_get_op :: "'a amtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a" where [simp]: "amtx_get_op c e \<equiv> (c e)"
  definition amtx_set_op :: "'a amtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a \<Rightarrow> 'a amtx" where [simp]: "amtx_set_op c e v \<equiv> (c(e:=v))"

  sepref_register amtx_new_op "'a amtx \<Rightarrow> 'a i_mtx"
  sepref_register amtx_get_op "'a i_mtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a"
  sepref_register amtx_set_op "'a i_mtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a \<Rightarrow> 'a i_mtx"

  lemma pat_amtx_get: "c$e\<equiv>amtx_get_op$c$e" by simp
  lemma pat_amtx_set: "fun_upd$c$e$v\<equiv>amtx_set_op$c$e$v" by simp

  lemmas amtx_pats = pat_amtx_get pat_amtx_set

  definition "is_mtx N c mtx \<equiv> \<exists>\<^sub>Al. mtx \<mapsto>\<^sub>a l * \<up>( 
      length l = N*N 
    \<and> (\<forall>i<N. \<forall>j<N. l!(i+j*N) = c (i,j))
    \<and> (\<forall>i j. (i\<ge>N \<or> j\<ge>N) \<longrightarrow> c (i,j) = 0))"

  lemma is_mtx_precise[constraint_rules]: "precise (is_mtx N)"
    apply rule
    unfolding is_mtx_def
    apply clarsimp
    apply prec_extract_eqs
    apply (rule ext)
    apply (rename_tac x)
    apply (case_tac x; simp)
    apply (rename_tac i j)
    apply (case_tac "i<N"; case_tac "j<N"; simp)
    done
    

  definition "mtx_new N c \<equiv> do {
    Array.make (N*N) (\<lambda>i. c (i mod N, i div N))
  }"

  definition "mtx_get N mtx e \<equiv> Array.nth mtx (fst e + snd e * N)"
  definition "mtx_set N mtx e v \<equiv> Array.upd (fst e + snd e * N) v mtx"

  lemma mtx_idx_valid[simp]: "\<lbrakk>i < (N::nat); j < N\<rbrakk> \<Longrightarrow> i + j * N < N * N"
  proof -
    assume a1: "i < N"
    assume a2: "j < N"
    have "\<forall>n na. \<exists>nb. \<not> na < n \<or> Suc (na + nb) = n"
      using less_imp_Suc_add by blast
    hence "0 < N"
      using a2 by blast
    thus ?thesis
      using a2 a1 by (metis (no_types) ab_semigroup_add_class.add.commute ab_semigroup_mult_class.mult.commute add.left_neutral div_if mod_div_equality mod_lemma mult_0_right)
  qed

  lemma mtx_index_unique[simp]: "\<lbrakk>i<(N::nat); j<N; i'<N; j'<N\<rbrakk> \<Longrightarrow> i+j*N = i'+j'*N \<longleftrightarrow> i=i' \<and> j=j'"
    by (metis ab_semigroup_add_class.add.commute add_diff_cancel_right' div_if div_mult_self3 gr0I not_less0)

  lemma mtx_new_rl[sep_heap_rules]: "Graph.V c \<subseteq> {0..<N} \<Longrightarrow> <emp> mtx_new N c <is_mtx N c>"
    apply (sep_auto simp: mtx_new_def is_mtx_def)
    apply (auto simp: Graph.V_def Graph.E_def)
    by (metis (no_types, lifting) atLeastLessThan_iff gr0I linorder_not_less mem_Collect_eq subsetCE)

  lemma mtx_get_rl[sep_heap_rules]: "\<lbrakk>i<N; j<N \<rbrakk> \<Longrightarrow> <is_mtx N c mtx> mtx_get N mtx (i,j) <\<lambda>r. is_mtx N c mtx * \<up>(r = c (i,j))>"
    by (sep_auto simp: mtx_get_def is_mtx_def)
    
  lemma mtx_set_rl[sep_heap_rules]: "\<lbrakk>i<N; j<N \<rbrakk> 
    \<Longrightarrow> <is_mtx N c mtx> mtx_set N mtx (i,j) v <\<lambda>r. is_mtx N (c((i,j) := v)) r>"
    by (sep_auto simp: mtx_set_def is_mtx_def nth_list_update)
        
  lemma mtx_new_fr_rl[sepref_fr_rules]: 
    "(mtx_new N, RETURN o amtx_new_op) \<in> [\<lambda>c. Graph.V c \<subseteq> {0..<N}]\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id))\<^sup>k \<rightarrow> is_mtx N"  
    apply rule apply rule
    apply (sep_auto simp: pure_def)
    done

  lemma [sepref_fr_rules]: 
    "CONSTRAINT IS_PURE_ID R \<Longrightarrow> (uncurry (mtx_get N), uncurry (RETURN oo amtx_get_op)) \<in> [\<lambda>(_,(i,j)). i<N \<and> j<N]\<^sub>a (is_mtx N)\<^sup>k *\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel))\<^sup>k \<rightarrow> R"
    apply rule apply rule
    apply (sep_auto simp: pure_def IS_PURE_ID_def)
    done
    
  lemma [sepref_fr_rules]: "CONSTRAINT IS_PURE_ID R \<Longrightarrow> (uncurry2 (mtx_set N), uncurry2 (RETURN ooo amtx_set_op)) 
    \<in> [\<lambda>((_,(i,j)),_). i<N \<and> j<N]\<^sub>a (is_mtx N)\<^sup>d *\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel))\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> is_mtx N"
    apply rule apply rule
    apply (sep_auto simp: pure_def hn_ctxt_def IS_PURE_ID_def)
    done

  experiment begin  (* TODO: Ultimately, this should replace network-checker. *)

  definition compute_ps where
    "compute_ps N mtx \<equiv> do {
      ps \<leftarrow> array'_op_new N [];
      (_,ps) \<leftarrow> WHILET (\<lambda>(i,ps). i<N) (\<lambda>(i,ps). do {
        (_,ps) \<leftarrow> WHILET (\<lambda>(j,ps). j<N) (\<lambda>(j,ps). do {
          l \<leftarrow> lst_op_get ps i; let l=j#l; ps \<leftarrow> lst_op_set ps i l;
          l \<leftarrow> lst_op_get ps j; let l=i#l; ps \<leftarrow> lst_op_set ps j l;
          RETURN (j+1,ps)
        }) (0,ps);
        RETURN (i+1,ps)
      }) (0,ps);
      RETURN ps
    }"

  schematic_lemma compute_ps_impl:
    fixes N :: nat and amtx :: "'a::{heap,default,zero} amtx"
    notes [id_rules] = itypeI[Pure.of N "TYPE(nat)"] itypeI[Pure.of amtx "TYPE('a i_mtx)"]
    notes [sepref_import_param] = IdI[of N]
    shows "hn_refine (hn_ctxt (is_mtx N) amtx mtx) (?c::?'c Heap) ?\<Gamma> ?R (compute_ps N amtx)"
    unfolding compute_ps_def APP_def
    using [[id_debug, goals_limit = 1]]
    by sepref_keep
  concrete_definition compute_ps_impl uses compute_ps_impl
  
  end
                                                       
  type_synonym pscf = "(node \<Rightarrow> node list) \<times> graph \<times> flow"

  abbreviation valid_node_pscf :: "pscf \<Rightarrow> node \<Rightarrow> bool" where "valid_node_pscf \<equiv> \<lambda>(ps,c,f). valid_node c"
  abbreviation valid_edge_pscf :: "pscf \<Rightarrow> edge \<Rightarrow> bool" where "valid_edge_pscf \<equiv> \<lambda>(ps,c,f). valid_edge c"
  definition res_graph_pscf :: "pscf \<Rightarrow> graph" where "res_graph_pscf \<equiv> \<lambda>(ps,c,f). Graph.residualGraph c f"

  text \<open>Basic Operations\<close>
  definition pscf_init :: "(node \<Rightarrow> node list) \<Rightarrow> graph \<Rightarrow> pscf nres" where 
    "pscf_init ps c \<equiv> do {ASSERT (is_pred_succ ps c); RETURN (ps,c,zero_flow)}"
  definition pscf_flow :: "pscf \<Rightarrow> flow" where "pscf_flow \<equiv> \<lambda>(ps,c,f). f"
  definition pscf_ps :: "pscf \<Rightarrow> node \<Rightarrow> node list nres" where "pscf_ps \<equiv> \<lambda>(ps,c,f) u. do {
    ASSERT (valid_node c u);
    RETURN (ps u)
  }"
  definition pscf_c :: "pscf \<Rightarrow> edge \<Rightarrow> capacity nres" where "pscf_c \<equiv> \<lambda>(ps,c,f) e. do {
    ASSERT (valid_edge c e);
    RETURN (c e)
  }"
  definition pscf_f :: "pscf \<Rightarrow> edge \<Rightarrow> capacity nres" where "pscf_f \<equiv> \<lambda>(ps,c,f) e. do {
    ASSERT (valid_edge c e);
    RETURN (f e)
  }"
  definition pscf_set_f :: "pscf \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> pscf nres" where "pscf_set_f \<equiv> \<lambda>(ps,c,f) e cap. do {
    ASSERT (valid_edge c e);
    RETURN (ps,c,f(e := cap))
  }"

  text \<open>Derived Operations\<close>

  definition cap_of_edge_pscf :: "pscf \<Rightarrow> edge \<Rightarrow> capacity nres" where
    "cap_of_edge_pscf pscf e \<equiv> do { 
      cuv \<leftarrow> pscf_c pscf e;
      if cuv > 0 then do {
        fuv \<leftarrow> pscf_f pscf e;
        RETURN (cuv - fuv)
      } else do {
        fvu \<leftarrow> pscf_f pscf (prod.swap e);
        RETURN (fvu)
      }
    }"

  definition pscf_succ :: "pscf \<Rightarrow> node \<Rightarrow> node list nres" where 
    "pscf_succ pscf u \<equiv> do {
    l \<leftarrow> pscf_ps pscf u;
    RECT (\<lambda>D l. case l of 
      [] \<Rightarrow> RETURN [] 
    | (v#l) \<Rightarrow> do {
        rl \<leftarrow> D l;
        x \<leftarrow> cap_of_edge_pscf pscf (u,v);
        if x > 0 then RETURN (v#rl) else RETURN rl   
      }) l
    }"

  definition "bottleneck_pscf pscf p \<equiv> 
    case p of
      [] \<Rightarrow> RETURN 0
    | (e#p) \<Rightarrow> do {
        cap \<leftarrow> cap_of_edge_pscf pscf e;
        nfoldli p (\<lambda>_. True) (\<lambda>e cap. do {
          cape \<leftarrow> cap_of_edge_pscf pscf e;
          RETURN (min cape cap)
        }) cap
      }"


  definition augment_edge_pscf :: "pscf \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> pscf nres" where
    "augment_edge_pscf pscf e x \<equiv> do {         
      ce \<leftarrow> pscf_c pscf e;
      if ce > 0 then do {
        fe \<leftarrow> pscf_f pscf e;
        pscf_set_f pscf e (fe + x)
      } else do {
        let e = prod.swap e;
        fe \<leftarrow> pscf_f pscf e;
        pscf_set_f pscf e (fe - x)
      }
    }"

  definition augment_pscf :: "pscf \<Rightarrow> path \<Rightarrow> capacity \<Rightarrow> pscf nres" where
    "augment_pscf pscf p x \<equiv> do {
      RECT (\<lambda>D. \<lambda>
        ([],pscf) \<Rightarrow> RETURN pscf
      | (e#p,pscf) \<Rightarrow> do {
          pscf \<leftarrow> augment_edge_pscf pscf e x;
          D (p,pscf)
        }  
      ) (p,pscf)
    }"


  definition "augment_flow_pscf pscf p \<equiv> do {
    x \<leftarrow> bottleneck_pscf pscf p;
    augment_pscf pscf p x
  }"

  definition pscf_rel :: "(node \<Rightarrow> node list) \<Rightarrow> graph \<Rightarrow> (pscf\<times>flow) set" where
    "pscf_rel ps c \<equiv> {((ps,c,f),f) | f::flow. True}"

  lemma pscf_rel_RELATES: "RELATES (pscf_rel ps c)" by (simp add: RELATES_def)

  lemma cap_of_edge_refine[refine]: "\<lbrakk>(ei,e)\<in>Id; (pscf,f)\<in>pscf_rel ps c\<rbrakk> 
    \<Longrightarrow> cap_of_edge_pscf pscf ei \<le> \<Down>Id (cap_of_edge c f e)"  
    unfolding cap_of_edge_pscf_def cap_of_edge_def
    by (simp add: pscf_c_def pscf_f_def pw_le_iff refine_pw_simps pscf_rel_def split: prod.split)


  lemma pscf_succ_refines: 
    assumes "(ui,u)\<in>Id" 
    assumes "(pscf,f)\<in>pscf_rel ps c" 
    shows "pscf_succ pscf ui \<le> \<Down>Id (rg_succ2 ps c f u)"
  proof -
    note [refine_dref_RELATES] = pscf_rel_RELATES[of ps c]  
    
    from assms have [simp]: "ui=u" "pscf=(ps,c,f)"
      by (auto simp: pscf_rel_def)    

    show ?thesis
      unfolding pscf_succ_def rg_succ2_def
      apply (simp add: pscf_ps_def)
      apply (rule refine_IdD)
      apply (refine_rcg IdI)
      apply simp
      apply (split list.split; intro allI impI conjI; simp)
      apply (rule refine_IdD)
      apply (refine_rcg)
      apply refine_dref_type
      apply (simp_all add: pscf_rel_def)
      done
  qed

  definition "fofu5 ps c s t \<equiv> do {
    pscf \<leftarrow> pscf_init ps c;

    (pscf,_) \<leftarrow> WHILET
      (\<lambda>(_,brk). \<not>brk) 
      (\<lambda>(pscf,_). do {
        p \<leftarrow> Graph.bfs2 (res_graph_pscf pscf) (pscf_succ pscf) s t;
        case p of 
          None \<Rightarrow> RETURN (pscf,True)
        | Some p \<Rightarrow> do {
            ASSERT (p\<noteq>[]);
            f \<leftarrow> augment_flow_pscf pscf p;
            RETURN (f, False)
          }  
      })
      (pscf,False);
    RETURN (pscf_flow pscf)
  }"

  lemma fofu5_refine: "fofu5 ps c s t \<le> \<Down>Id (fofu4 ps c s t)"
  proof -
    have [refine]: "((ps,c,zero_flow), zero_flow) \<in> pscf_rel ps c"
      by (auto simp: pscf_rel_def pscf_init_def)
    (*have [refine]: "((pscf_init ps c, False), zero_flow, False) \<in> pscf_rel ps c \<times>\<^sub>r bool_rel"
      by (auto simp: pscf_rel_def pscf_init_def)*)

    note [refine_dref_RELATES] = pscf_rel_RELATES[of ps c]  

    have [refine]: "\<And>pscf f p pi x xi. \<lbrakk>(pi,p)\<in>Id; (xi,x)\<in>Id; (pscf,f)\<in>pscf_rel ps c\<rbrakk> 
      \<Longrightarrow> augment_pscf pscf pi xi \<le> \<Down>(pscf_rel ps c) (augment_impl c f p x)"  
      unfolding augment_pscf_def augment_impl_def augment_edge_pscf_def augment_edge_impl_def
      apply (refine_rcg)
      apply refine_dref_type
      apply (auto simp: pscf_rel_def pscf_c_def pscf_f_def pscf_set_f_def
        split: list.split)
      apply (simp only: refine_pw_simps pw_le_iff)
      apply fastforce
      apply (simp only: refine_pw_simps pw_le_iff)
      apply fastforce
      done

    have [intro!]: "\<And>l. distinct l \<Longrightarrow> (l,set l)\<in>\<langle>Id\<rangle>list_set_rel"
      by (auto simp: list_set_rel_def br_def)

    have [refine_dref_RELATES]: "RELATES (\<langle>nat_rel\<times>\<^sub>rnat_rel\<rangle>list_set_rel)" by (simp add: RELATES_def)

    have [refine]: "\<And>pscf f p pi. \<lbrakk>(pi,p)\<in>Id; (pscf,f)\<in>pscf_rel ps c\<rbrakk> 
      \<Longrightarrow> augment_flow_pscf pscf pi \<le> \<Down>(pscf_rel ps c) (augment_flow_impl c f p)"  
      unfolding augment_flow_pscf_def augment_flow_impl_def
      unfolding bottleneck_pscf_def bottleneck_impl_def 
      apply simp
      apply (refine_rcg)
      apply (split list.split; intro allI impI conjI; simp)
      apply (refine_rcg LFO_refine)
      apply refine_dref_type
      apply vc_solve
      done

    show ?thesis
      unfolding fofu5_def fofu4_def pscf_init_def
      apply (refine_rcg bfs2_refine_succ pscf_succ_refines)
      apply refine_dref_type
      apply (vc_solve)
      apply (simp add: res_graph_pscf_def pscf_rel_def pscf_succ_def)
      apply (simp add: pscf_rel_def pscf_flow_def)
      done
  qed    


  definition "is_ps N ps psi \<equiv> \<exists>\<^sub>Al. psi \<mapsto>\<^sub>a l * \<up>(length l = N \<and> (\<forall>i<N. l!i = ps i) \<and> (\<forall>i\<ge>N. ps i = []))"

  lemma is_ps_precise[constraint_rules]: "precise (is_ps N)"
    apply rule
    unfolding is_ps_def
    apply clarsimp
    apply (rename_tac l l')
    apply prec_extract_eqs
    apply (rule ext)
    apply (rename_tac i)
    apply (case_tac "i<length l'")
    apply fastforce+
    done

  type_synonym pscfi = "node list Heap.array \<times> capacity mtx \<times> capacity mtx"  

  definition is_pscf :: "nat \<Rightarrow> pscf \<Rightarrow> pscfi \<Rightarrow> assn" where 
  "is_pscf N \<equiv> \<lambda> (ps,c,f) (psi,ci,fi).
    is_ps N ps psi * is_mtx N c ci * is_mtx N f fi * \<up>(
      is_pred_succ ps c \<and> Graph.V c \<subseteq> {0..<N}
    )"

  lemma is_pscf_precise[constraint_rules]: "precise (is_pscf N)"
    unfolding is_pscf_def 
    apply rule
    apply (clarsimp split: prod.splits)
    apply prec_extract_eqs
    by simp

  typedecl i_pscf

  context 
    notes [map_type_eqs] 
      = map_type_eqI[Pure.of "TYPE(pscf)" "TYPE(i_pscf)"]
  begin    
    sepref_register pscf_ps
    sepref_register pscf_c
    sepref_register pscf_f
    sepref_register pscf_set_f
    sepref_register cap_of_edge_pscf
    sepref_register pscf_init
    sepref_register augment_flow_pscf
    sepref_register pscf_flow
  end

  definition pscfi_ps :: "pscfi \<Rightarrow> node \<Rightarrow> node list Heap"
    where "pscfi_ps \<equiv> \<lambda>(psi,ci,fi) u. Array.nth psi u"

  lemma pscfi_ps_refine[sepref_fr_rules]: 
    "(uncurry pscfi_ps,uncurry pscf_ps) \<in> (is_pscf N)\<^sup>k *\<^sub>a (pure nat_rel)\<^sup>k \<rightarrow>\<^sub>a pure (\<langle>nat_rel\<rangle>list_rel)"
    apply rule apply rule
    unfolding is_pscf_def is_ps_def pscfi_ps_def pscf_ps_def  
    apply (sep_auto simp: refine_pw_simps pure_def hn_ctxt_def)
    done

  definition pscfi_c :: "nat \<Rightarrow> pscfi \<Rightarrow> edge \<Rightarrow> capacity Heap" 
    where "pscfi_c N \<equiv> \<lambda>(psi,ci,fi) e. mtx_get N ci e"
  lemma pscfi_c_refine[sepref_fr_rules]: 
    "(uncurry (pscfi_c N),uncurry pscf_c) \<in> (is_pscf N)\<^sup>k *\<^sub>a (hn_prod_aux (pure nat_rel) (pure nat_rel))\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel)"
    apply rule apply rule
    unfolding is_pscf_def is_ps_def pscfi_c_def pscf_c_def  
    apply (sep_auto simp: refine_pw_simps pure_def hn_ctxt_def)
    done

  definition pscfi_f :: "nat \<Rightarrow> pscfi \<Rightarrow> edge \<Rightarrow> capacity Heap"
    where "pscfi_f N \<equiv> \<lambda>(psi,ci,fi) e. mtx_get N fi e"
  lemma pscfi_f_refine[sepref_fr_rules]: 
    "(uncurry (pscfi_f N),uncurry pscf_f) \<in> (is_pscf N)\<^sup>k *\<^sub>a (hn_prod_aux (pure nat_rel) (pure nat_rel))\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel)"
    apply rule apply rule
    unfolding is_pscf_def is_ps_def pscfi_f_def pscf_f_def  
    apply (sep_auto simp: refine_pw_simps pure_def hn_ctxt_def)
    done

  definition pscfi_set_f :: "nat \<Rightarrow> pscfi \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> pscfi Heap"
    where "pscfi_set_f N \<equiv> \<lambda>(psi,ci,fi) e v. do {
    fi \<leftarrow> mtx_set N fi e v;
    return (psi,ci,fi)
  }"
  lemma pscfi_set_f_refine[sepref_fr_rules]: 
    "(uncurry2 (pscfi_set_f N),uncurry2 pscf_set_f) \<in> 
      (is_pscf N)\<^sup>d *\<^sub>a (hn_prod_aux (pure nat_rel) (pure nat_rel))\<^sup>k *\<^sub>a (pure nat_rel)\<^sup>k \<rightarrow>\<^sub>a is_pscf N"
    apply rule apply rule
    unfolding is_pscf_def is_ps_def pscfi_set_f_def pscf_set_f_def  
    apply (sep_auto simp: refine_pw_simps pure_def hn_ctxt_def fun_upd_def)
    done


  definition pscfi_init :: "nat \<Rightarrow> (node \<Rightarrow> node list) \<Rightarrow> graph \<Rightarrow> pscfi Heap"
    where 
    "pscfi_init N ps c \<equiv> do {
      psi \<leftarrow> Array.make N ps;
      ci \<leftarrow> mtx_new N c;
      fi \<leftarrow> mtx_new N zero_flow;
      return (psi,ci,fi)
    }"

  lemma pscfi_init_refine[sepref_fr_rules]:
    shows "(uncurry (pscfi_init N), uncurry (pscf_init)) \<in>
    [\<lambda>(ps,c). DEP_SIDE_PRECOND (Graph.V c \<subseteq> {0..<N})]\<^sub>a
    (pure Id)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow> is_pscf N"  
    apply rule apply rule
    apply (clarsimp simp: pure_def)
  proof -
    fix ps c
    assume GV: "Graph.V c \<subseteq> {0..<N}" and "nofail (pscf_init ps c)"
    hence [simp]: 
      "\<And>x. x\<in>Graph.V c \<Longrightarrow> x<N" 
      and APS: "is_pred_succ ps c"
      by (auto simp:  pscf_init_def refine_pw_simps)
    have [simp]: 
      "Graph.V (\<lambda>_. 0) = {}"
      by (auto simp: Graph.V_def Graph.E_def)
      
    from APS have [simp]: "\<And>i. i\<ge>N \<Longrightarrow> ps i = []"
      unfolding is_pred_succ_def
      using GV
      by (force simp: Graph.V_def)

    show "<emp> pscfi_init N ps c <\<lambda>r. \<exists>\<^sub>Ax. is_pscf N x r * true * \<up> (RETURN x \<le> pscf_init ps c)>"
      unfolding pscfi_init_def pscf_init_def is_pscf_def is_ps_def
      by (sep_auto simp: APS)
  qed    

  definition pscfi_flow :: "pscfi \<Rightarrow> capacity mtx Heap" where
    "pscfi_flow \<equiv> \<lambda>(ps,ci,fi). return fi"

  lemma pscfi_flow_refine[sepref_fr_rules]: "(pscfi_flow,RETURN o pscf_flow) \<in> (is_pscf N)\<^sup>d \<rightarrow>\<^sub>a is_mtx N"  
    apply rule apply rule
    unfolding pscfi_flow_def pscf_flow_def is_pscf_def
    by (sep_auto simp: hn_ctxt_def)

  (* TODO: Still required? In NFlow, we even have equality! *)
  lemma res_graph_V_ss: "Graph.V (res_graph_pscf (ps,c,f)) \<subseteq> Graph.V c"
    by (auto simp: res_graph_pscf_def Graph.residualGraph_def Graph.V_def Graph.E_def split: split_if_asm)  

  (* TODO: Move *)  
  lemma param_prod_swap[param]: "(prod.swap, prod.swap)\<in>A\<times>\<^sub>rB \<rightarrow> B\<times>\<^sub>rA" by auto
  lemmas [sepref_import_param] = param_prod_swap

  schematic_lemma pscf_cap_of_edge_impl:
    notes [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"] itypeI[Pure.of e "TYPE(edge)"] itypeI[Pure.of pscf "TYPE(i_pscf)"]
    notes [sepref_import_param] = IdI[of N]
    shows "hn_refine (hn_ctxt (is_pscf N) pscf pscfi * hn_prod (pure nat_rel) (pure nat_rel) e ei) (?c::?'c Heap) ?\<Gamma> ?R (cap_of_edge_pscf pscf e)"  
    unfolding cap_of_edge_pscf_def
    using [[id_debug, goals_limit = 1]]
    by sepref_keep
  concrete_definition cap_of_edge_imp uses pscf_cap_of_edge_impl
  lemmas [sepref_fr_rules] = cap_of_edge_imp.refine[to_hfref]

  schematic_lemma pscf_succ_impl:
    fixes N :: nat and pscf :: pscf
    notes [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"] itypeI[Pure.of u "TYPE(node)"] itypeI[Pure.of pscf "TYPE(i_pscf)"]
    notes [sepref_import_param] = IdI[of N]
    shows "hn_refine (hn_ctxt (is_pscf N) pscf pscfi * hn_val nat_rel u ui) (?c::?'c Heap) ?\<Gamma> ?R (pscf_succ pscf u)"
    unfolding pscf_succ_def APP_def
    using [[id_debug, goals_limit = 1]]
    apply sepref_keep
    done
  concrete_definition succ_imp uses pscf_succ_impl
  prepare_code_thms succ_imp_def
  lemmas succ_imp_fr_rl = succ_imp.refine[to_hfref]

  lemma [sepref_import_param]: "(min,min)\<in>Id\<rightarrow>Id\<rightarrow>Id" by simp

  schematic_lemma pscfi_augment_flow:
    fixes N :: nat and pscf :: pscf
    notes [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"] itypeI[Pure.of p "TYPE(path)"] itypeI[Pure.of pscf "TYPE(i_pscf)"]
    notes [sepref_import_param] = IdI[of N]
    shows "hn_refine (
      hn_ctxt (is_pscf N) pscf pscfi * 
      hn_list (hn_prod_aux (pure nat_rel) (pure nat_rel)) p pi) (?c::?'c Heap) ?\<Gamma> ?R (augment_flow_pscf pscf p)"
    unfolding augment_flow_pscf_def bottleneck_pscf_def augment_pscf_def augment_edge_pscf_def
    using [[id_debug, goals_limit = 1]]
    apply sepref_keep
    done
  concrete_definition pscfi_augment_flow uses pscfi_augment_flow
  prepare_code_thms pscfi_augment_flow_def
  lemmas [sepref_fr_rules] = pscfi_augment_flow.refine[to_hfref]


  (*interpretation Impl_Succ*)

  interpretation bfs!: Impl_Succ res_graph_pscf "TYPE(i_pscf)" pscf_succ "is_pscf N" "succ_imp N"
    apply unfold_locales
    apply constraint_rules
    apply (rule hfref_cons[OF succ_imp_fr_rl])
    by auto

  concrete_definition bfsi uses bfs.bfs_impl_def
  lemmas [sepref_fr_rules] = bfs.bfs_impl_fr_rule[unfolded bfsi.refine[abs_def]]
  prepare_code_thms bfsi_def
  print_theorems

(* TODO: Refinement to successor function: Probably earlier, 
  before fixing search strategy!? *)

  thm pscfi_init_refine[where N=N, to_hnr, OF DEP_SIDE_PRECOND_D, to_hfref]

  schematic_lemma fofu6:
    fixes N :: nat and  pscf :: pscf
    notes [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"] 
      itypeI[Pure.of s "TYPE(node)"] 
      itypeI[Pure.of t "TYPE(node)"] 
      itypeI[Pure.of ps "TYPE(node \<Rightarrow> node list)"] 
      itypeI[Pure.of c "TYPE(node \<times> node \<Rightarrow> capacity)"] 
    notes [sepref_import_param] = 
      IdI[of N]
      IdI[of s]
      IdI[of t]
      IdI[of ps]
      IdI[of c]
    assumes nodesN: "Graph.V c \<subseteq> {0..<N}"  
    (*notes [sepref_fr_rules] = pscfi_init_refine[where N=N, to_hnr, OF DEP_SIDE_PRECOND_D]*)
    shows "hn_refine (emp) (?c::?'c Heap) ?\<Gamma> ?R (fofu5 ps c s t)"
    unfolding fofu5_def APP_def
    using [[id_debug, goals_limit = 1]]
    using assms
    by sepref_keep
  concrete_definition fofu6 for N ps c s t uses fofu6
  prepare_code_thms fofu6_def
  print_theorems

  export_code fofu6 checking SML_imp

  thm fofu6_def

  context Network begin
    theorem fofu6_correct: 
      assumes VN: "Graph.V c \<subseteq> {0..<N}"
      assumes ABS_PS: "is_pred_succ ps c"
      shows "<emp> fofu6 N ps c s t <\<lambda>fi. \<exists>\<^sub>Af. is_mtx N f fi * \<up>(isMaxFlow c s t f)>\<^sub>t"
    proof -
      note fofu5_refine
      also note fofu4_refine
      also note fofu3_refine[OF ABS_PS]
      also note fofu2_refine 
      also note fofu_total_correct
      finally have "fofu5 ps c s t \<le> SPEC (isMaxFlow c s t)" .
      from hn_refine_ref[OF this fofu6.refine[OF VN]]
        show ?thesis by (simp add: hn_refine_def)
    qed
  end    

  definition example_c :: "nat \<times> nat \<Rightarrow> nat" 
    where "example_c \<equiv> (\<lambda>_. 0::nat)( (1,2) := 1, (2,3) := 1 )"

  definition example_ps :: "node \<Rightarrow> node list" 
    where "example_ps \<equiv> (\<lambda>_. [])(1:=[2], 2:=[1,3], 3:=[2])"

  lemma example_abs_ps: "is_pred_succ example_ps example_c"  
    unfolding example_c_def example_ps_def is_pred_succ_def 
    by (auto simp: Graph.E_def)

  lemma example_vn: "Graph.V example_c \<subseteq> {0..<4}"  
    by (auto simp: example_c_def Graph.V_def Graph.E_def)


  lemma example_c_reachable[simp]: "Graph.reachable example_c (Suc 0) = {1,2,3}"  
    apply (auto simp: Graph.reachable_def Graph.E_def
      Graph.isReachable_def example_c_def Graph.isPath.simps
        intro: exI[where x="[]"] 
        intro: exI[where x="[(1,2)]"] 
        intro: exI[where x="[(2,3)]"] 
        intro: exI[where x="[(1,2),(2,3)]"] 
        )
    apply (case_tac p, simp_all add: Graph.isPath.simps Graph.E_def)
    apply (case_tac list, auto simp: Graph.isPath.simps split_paired_all Graph.E_def
      split_if_asm)
    apply (case_tac lista, auto simp: Graph.isPath.simps split_paired_all Graph.E_def
      split_if_asm)
    done
    

  lemma example_c_network: "Network example_c 1 3"  
    apply default
    apply (simp_all add: Graph.E_def)
    apply (auto 
      simp: example_c_def Graph.V_def Graph.E_def Graph.isReachable_def)
    apply (auto simp: Graph.isPath.simps Graph.E_def
        intro!: finite_subset[where A = "Graph.reachable x y" and B="{1,2,3::nat}" for x y]
        intro: exI[where x="[]"] 
        intro: exI[where x="[(1,2)]"] 
        intro: exI[where x="[(2,3)]"] 
        intro: exI[where x="[(1,2),(2,3)]"] 
      )
    done

  lemmas example_c_correct = Network.fofu6_correct[OF example_c_network example_vn example_abs_ps]
  

thm nres_monad_laws

(* 
    lemma "
      do {
        (s,_) \<leftarrow> WHILET (\<lambda>(s,brk). \<not>brk) (\<lambda>(s,_). do {
          p \<leftarrow> SPEC (\<lambda>Some p \<Rightarrow> P s p | None \<Rightarrow> \<forall>p. \<not>P s p);
          case p of 
            Some p \<Rightarrow> do {
              s' \<leftarrow> f p s;
              RETURN (s',False)
            }
          | None \<Rightarrow> RETURN (s,True)  
        }) (s0, False);
        RETURN s
      }  
    \<le>
      WHILET (\<lambda>s. \<exists>p. P s p) (\<lambda>s. do {
        p \<leftarrow> SPEC (\<lambda>p. P s p);
        f p s
      }) s0
    "
    apply (rule le_nofailI)
    apply (subst (2) WHILET_eq_WHILE, simp add: nofail_def)
    apply (subst nofail_WHILE_eq_rwof[of "RETURN s0", simplified])         
      apply (subst (asm) WHILET_eq_WHILE)



    definition "fofu2 \<equiv> do {
      let f = (\<lambda>_. 0);

      WHILET 
        (\<lambda>f. \<exists>p. NFlow.isAugmenting c s t f p) 
        (\<lambda>f. do {
          p \<leftarrow> SPEC (\<lambda>p. NFlow.isAugmenting c s t f p);
          let f' = NFlow.augmentingFlow c f p;
          let f = NFlow.augment c f f';
          RETURN f
        })
        f
    }"

 *)



end
