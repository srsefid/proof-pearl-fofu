section \<open>Implementation of the Edmonds-Karp Algorithm\<close>
theory EdmondsKarp_Impl
imports 
  EdmondsKarp_Algo
  "Augmenting_Path_BFS"
  "Capacity_Matrix_Impl"
begin

  text \<open>We now implement the Edmonds-Karp algorithm.\<close>

  subsection \<open>Refinement to Residual Graph\<close>
    text \<open>As a first step towards implementation, we refine the algorithm
      to work directly on residual graphs. For this, we first have to 
      establish a relation between flows in a network and residual graphs.
      \<close>

  definition (in Network) "flow_of_cf cf e \<equiv> (if (e\<in>E) then c e - cf e else 0)"
  
  locale RGraph -- \<open>Locale that characterizes a residual graph of a network\<close>
  = Network +
    fixes cf
    assumes EX_RG: "\<exists>f. NFlow c s t f \<and> cf = residualGraph f"
  begin  

    lemma this_loc: "RGraph c s t cf"
      by unfold_locales

    definition "f \<equiv> flow_of_cf cf"

    lemma f_unique:
      assumes "NFlow c s t f'"
      assumes A: "cf = residualGraph f'"
      shows "f' = f"
    proof -
      interpret f'!: NFlow c s t f' by fact
      
      show ?thesis
        unfolding f_def[abs_def] flow_of_cf_def[abs_def]
        unfolding A residualGraph_def
        apply (rule ext)
        using f'.capacity_cons
        apply (clarsimp split: prod.split simp: E_def)
        by (metis le_0_eq)
    qed

    lemma is_NFlow: "NFlow c s t (flow_of_cf cf)"
      apply (fold f_def)
      using EX_RG f_unique by metis
      
    sublocale f!: NFlow c s t f unfolding f_def by (rule is_NFlow)

    lemma rg_is_cf[simp]: "residualGraph f = cf"
      using EX_RG f_unique by auto

    lemma rg_fo_inv[simp]: "residualGraph (flow_of_cf cf) = cf"  
      using rg_is_cf
      unfolding f_def
      .
      

    sublocale cf!: Graph cf .

    lemma resV_netV[simp]: "cf.V = V"
      using f.resV_netV by simp

    sublocale cf!: Finite_Graph cf 
      apply unfold_locales
      apply simp
      done

    lemma finite_cf: "finite (cf.V)" by simp


  end

  context NFlow begin
    lemma is_RGraph: "RGraph c s t cf"
      apply unfold_locales
      apply (rule exI[where x=f])
      apply (safe; unfold_locales)
      done

    lemma fo_rg_inv: "flow_of_cf cf = f"  
      unfolding flow_of_cf_def[abs_def]
      unfolding residualGraph_def
      apply (rule ext)
      using capacity_cons
      apply (clarsimp split: prod.split simp: E_def)
      by (metis le_0_eq)

  end    

  (* For snippet*)
  lemma (in NFlow)
    "flow_of_cf (residualGraph f) = f"
    by (rule fo_rg_inv)



  subsubsection \<open>Refinement of Operations\<close>
  context Network 
  begin
    text \<open>We define the relation between residual graphs and flows\<close>
    definition "cfi_rel \<equiv> br flow_of_cf (RGraph c s t)"

    text \<open>It can also be characterized the other way round, i.e., 
      mapping flows to residual graphs:\<close>
    lemma cfi_rel_alt: "cfi_rel = {(cf,f). cf = residualGraph f \<and> NFlow c s t f}"
      unfolding cfi_rel_def br_def
      by (auto simp: NFlow.is_RGraph RGraph.is_NFlow RGraph.rg_fo_inv NFlow.fo_rg_inv)

    
    text \<open>Initially, the residual graph for the zero flow equals the original network\<close>
    lemma residualGraph_zero_flow: "residualGraph (\<lambda>_. 0) = c" 
      unfolding residualGraph_def by (auto intro!: ext simp: E_def)
    lemma flow_of_c: "flow_of_cf c = (\<lambda>_. 0)"
      by (auto simp add: flow_of_cf_def[abs_def])

    text \<open>The bottleneck capacity is naturally defined on residual graphs\<close>      
    definition "bottleNeck_cf cf p \<equiv> Min {cf e | e. e\<in>set p}"
    lemma (in NFlow) bottleNeck_cf_refine: "bottleNeck_cf cf p = bottleNeck p"
      unfolding bottleNeck_cf_def bottleNeck_def ..

    text \<open>Augmentation can be done by @{const Graph.augment_cf}.\<close> 

    
    lemma (in NFlow) (* For snippet *)
      assumes AUG: "isAugmenting p"
      shows "residualGraph (augment (augmentingFlow p)) (u,v) = (
        if (u,v)\<in>set p then (residualGraph f (u,v) - bottleNeck p)
        else if (v,u)\<in>set p then (residualGraph f (u,v) + bottleNeck p)
        else residualGraph f (u,v))"
      using augment_alt[OF AUG] by (auto simp: Graph.augment_cf_def)


    lemma augment_cf_refine:
      assumes R: "(cf,f)\<in>cfi_rel"
      assumes AUG: "NFlow.isAugmenting c s t f p"
      shows "(Graph.augment_cf cf (set p) (bottleNeck_cf cf p), 
          NFlow.augment c f (NFlow.augmentingFlow c f p)) \<in> cfi_rel"
    proof -    
      from R have FEQ: "f = flow_of_cf cf" "RGraph c s t cf"
        by (auto simp: cfi_rel_def br_def)
      then interpret cf!: RGraph c s t cf by simp  
      
      from FEQ have [simp]: "f = cf.f" by (simp add: cf.f_def)
      note AUG'=AUG[simplified]

      show "(Graph.augment_cf cf (set p) (bottleNeck_cf cf p), 
        NFlow.augment c f (NFlow.augmentingFlow c f p)) \<in> cfi_rel"
        (* TODO: Try to make this more concise! *)
        apply (subst cf.f.bottleNeck_cf_refine[simplified])
        apply (clarsimp simp: cfi_rel_def br_def; safe)
        apply (subst cf.f.augment_alt[OF AUG', simplified, symmetric])
        apply (subst NFlow.fo_rg_inv)
        apply (rule cf.f.augment_pres_nflow)
        apply fact
        apply (rule refl)
        apply (subst cf.f.augment_alt[OF AUG', simplified, symmetric])
        apply (rule NFlow.is_RGraph)
        apply (rule cf.f.augment_pres_nflow)
        apply fact
        done
    qed  

    text \<open>We rephrase the specification of shortest augmenting path to
      take a residual graph as parameter\<close>
    definition "find_shortest_augmenting_spec_cf cf \<equiv> 
      ASSERT (RGraph c s t cf) \<guillemotright>
      SPEC (\<lambda>None \<Rightarrow> \<not>Graph.conn cf s t | Some p \<Rightarrow> Graph.shortestPath cf s p t)"

    lemma (in RGraph) find_shortest_augmenting_spec_cf_refine: 
      "find_shortest_augmenting_spec_cf cf \<le> find_shortest_augmenting_spec (flow_of_cf cf)"
      unfolding f_def[symmetric]
      unfolding find_shortest_augmenting_spec_cf_def find_shortest_augmenting_spec_def
      by (auto 
        simp: pw_le_iff refine_pw_simps 
        simp: this_loc rg_is_cf
        simp: f.isAugmenting_def Graph.isReachable_def Graph.isSimplePath_def
        split: option.split)
      
    text \<open>This leads to the following refined algorithm\<close>  
    definition "edka2 \<equiv> do {
      let cf = c;

      (cf,_) \<leftarrow> WHILET 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> find_shortest_augmenting_spec_cf cf;
          case p of 
            None \<Rightarrow> RETURN (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.shortestPath cf s p t);
              let cf = Graph.augment_cf cf (set p) (bottleNeck_cf cf p);
              ASSERT (RGraph c s t cf);
              RETURN (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      let f = flow_of_cf cf;  
      RETURN f
    }"

    lemma edka2_refine: "edka2 \<le> \<Down>Id edka"
    proof -
      have [refine_dref_RELATES]: "RELATES cfi_rel" by (simp add: RELATES_def)

      show ?thesis
        unfolding edka2_def edka_def
        apply (rewrite in "let f' = NFlow.augmentingFlow c _ _ in _" Let_def)
        apply (rewrite in "let f = flow_of_cf _ in _" Let_def)
        apply (refine_rcg)
        apply refine_dref_type
        apply vc_solve

        apply (drule NFlow.is_RGraph; auto simp: cfi_rel_def br_def residualGraph_zero_flow flow_of_c; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        using RGraph.find_shortest_augmenting_spec_cf_refine
        apply (auto simp: cfi_rel_def br_def; fail)
        apply (auto simp: cfi_rel_def br_def simp: RGraph.rg_fo_inv; fail)
        apply (drule (1) augment_cf_refine; simp add: cfi_rel_def br_def; fail)
        apply (simp add: augment_cf_refine; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        apply (auto simp: cfi_rel_def br_def; fail)
        done
    qed    

    subsection \<open>Implementation of Bottleneck Computation and Augmentation\<close>  
    text \<open>We will access the capacities in the residual graph
      only by a get-operation, which asserts that the edges are valid\<close>
    
    abbreviation (input) valid_edge :: "edge \<Rightarrow> bool" where
      "valid_edge \<equiv> \<lambda>(u,v). u\<in>V \<and> v\<in>V"

    definition cf_get :: "graph \<Rightarrow> edge \<Rightarrow> capacity nres" 
      where "cf_get cf e \<equiv> ASSERT (valid_edge e) \<guillemotright> RETURN (cf e)"  
    definition cf_set :: "graph \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> graph nres"
      where "cf_set cf e cap \<equiv> ASSERT (valid_edge e) \<guillemotright> RETURN (cf(e:=cap))"  


    definition bottleNeck_cf_impl :: "graph \<Rightarrow> path \<Rightarrow> capacity nres" 
    where "bottleNeck_cf_impl cf p \<equiv> 
      case p of
        [] \<Rightarrow> RETURN (0::capacity)
      | (e#p) \<Rightarrow> do {
          cap \<leftarrow> cf_get cf e;
          ASSERT (distinct p);
          nfoldli 
            p (\<lambda>_. True)
            (\<lambda>e cap. do {
              cape \<leftarrow> cf_get cf e;
              RETURN (min cape cap)
            }) 
            cap
        }"

    lemma (in RGraph) bottleNeck_cf_impl_refine:   
      assumes AUG: "cf.isSimplePath s p t"
      shows "bottleNeck_cf_impl cf p \<le> SPEC (\<lambda>r. r = bottleNeck_cf cf p)"
    proof -
      (* TODO: Can we exploit Min.set_eq_fold *)

      note [simp del] = Min_insert
      note [simp] = Min_insert[symmetric]
      from AUG[THEN cf.isSPath_distinct]
      have "distinct p" .
      moreover from AUG cf.isPath_edgeset have "set p \<subseteq> cf.E"
        by (auto simp: cf.isSimplePath_def)
      hence "set p \<subseteq> Collect valid_edge"  
        using cf.E_ss_VxV by simp
      moreover from AUG have "p\<noteq>[]" by (auto simp: s_not_t) 
        then obtain e p' where "p=e#p'" by (auto simp: neq_Nil_conv)
      ultimately show ?thesis  
        unfolding bottleNeck_cf_impl_def bottleNeck_cf_def cf_get_def
        apply (simp only: list.case)
        apply (refine_vcg nfoldli_rule[where 
            I = "\<lambda>l l' cap. cap = Min (cf`insert e (set l)) \<and> set (l@l') \<subseteq> Collect valid_edge"])
        apply auto []
        apply auto []
        apply auto []
        apply auto []
        apply auto []
        apply auto []
        apply auto []
        apply simp
        apply (fo_rule arg_cong; auto)
        apply auto []
        apply auto []
        apply simp
        apply (fo_rule arg_cong; auto)
        done
    qed    

    definition (in Graph) 
      "augment_edge e cap \<equiv> (c(e := c e - cap, prod.swap e := c (prod.swap e) + cap))"

    lemma (in Graph) augment_cf_inductive:
      fixes e cap
      defines "c' \<equiv> augment_edge e cap"
      assumes P: "isSimplePath s (e#p) t"
      shows "augment_cf (insert e (set p)) cap = Graph.augment_cf c' (set p) cap"
      and "\<exists>s'. Graph.isSimplePath c' s' p t"  
    proof -
      obtain u v where [simp]: "e=(u,v)" by (cases e)

      from isSPath_no_selfloop[OF P] have [simp]: "\<And>u. (u,u)\<notin>set p" "u\<noteq>v" by auto

      from isSPath_nt_parallel[OF P] have [simp]: "(v,u)\<notin>set p" by auto
      from isSPath_distinct[OF P] have [simp]: "(u,v)\<notin>set p" by auto

      (*have [simp]: "\<And>u v. prod.swap (u,v) = (u,v) \<longleftrightarrow> u=v" by auto*)

      show "augment_cf (insert e (set p)) cap = Graph.augment_cf c' (set p) cap"
        apply (rule ext)  
        unfolding Graph.augment_cf_def c'_def Graph.augment_edge_def
        by auto

      have "Graph.isSimplePath c' v p t"  
        unfolding Graph.isSimplePath_def
        apply rule
        apply (rule transfer_path)
        apply (auto simp: c'_def Graph.augment_edge_def Graph.E_def) []
        using P apply (auto simp: isSimplePath_def) []
        using P apply (auto simp: isSimplePath_def) []
        done
      thus "\<exists>s'. Graph.isSimplePath c' s' p t" .. 

    qed    
        
    definition "augment_edge_impl cf e cap \<equiv> do {
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v-cap);
      let e = prod.swap e;
      v \<leftarrow> cf_get cf e; cf \<leftarrow> cf_set cf e (v+cap);
      RETURN cf
    }"

    lemma augment_edge_impl_refine: 
      "\<lbrakk>valid_edge e; \<forall>u. e\<noteq>(u,u)\<rbrakk> \<Longrightarrow> augment_edge_impl cf e cap \<le> SPEC (\<lambda>r. r = Graph.augment_edge cf e cap)"
      unfolding augment_edge_impl_def Graph.augment_edge_def cf_get_def cf_set_def
      apply refine_vcg
      apply auto
      done
      
    definition augment_cf_impl :: "graph \<Rightarrow> path \<Rightarrow> capacity \<Rightarrow> graph nres" where
      "augment_cf_impl cf p x \<equiv> do {
        RECT (\<lambda>D. \<lambda>
          ([],cf) \<Rightarrow> RETURN cf
        | (e#p,cf) \<Rightarrow> do {
            cf \<leftarrow> augment_edge_impl cf e x;
            D (p,cf)
          }  
        ) (p,cf)
      }"

    lemma augment_cf_impl_simps[simp]: 
      "augment_cf_impl cf [] x = RETURN cf"
      "augment_cf_impl cf (e#p) x = do { cf \<leftarrow> augment_edge_impl cf e x; augment_cf_impl cf p x}"
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      
      apply (simp add: augment_cf_impl_def)
      apply (subst RECT_unfold, refine_mono)
      apply simp
      done      

    lemma augment_cf_impl_aux:    
      assumes "\<forall>e\<in>set p. valid_edge e"
      assumes "\<exists>s. Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> RETURN (Graph.augment_cf cf (set p) x)"
      using assms
      apply (induction p arbitrary: cf)
      apply (simp add: Graph.augment_cf_empty)

      apply clarsimp
      apply (subst Graph.augment_cf_inductive, assumption)

      apply (refine_vcg augment_edge_impl_refine[THEN order_trans])
      apply simp
      apply simp
      apply (auto dest: Graph.isSPath_no_selfloop) []
      apply (rule order_trans, rprems)
        apply (drule Graph.augment_cf_inductive(2)[where cap=x]; simp)
        apply simp
      done  
      
    lemma (in RGraph) augment_cf_impl_refine:     
      assumes "Graph.isSimplePath cf s p t"
      shows "augment_cf_impl cf p x \<le> RETURN (Graph.augment_cf cf (set p) x)"
      apply (rule augment_cf_impl_aux)
      using assms cf.E_ss_VxV apply (auto simp: cf.isSimplePath_def dest!: cf.isPath_edgeset) []
      using assms by blast
      
    definition "edka3 \<equiv> do {
      let cf = c;

      (cf,_) \<leftarrow> WHILET 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> find_shortest_augmenting_spec_cf cf;
          case p of 
            None \<Rightarrow> RETURN (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.shortestPath cf s p t);
              bn \<leftarrow> bottleNeck_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              ASSERT (RGraph c s t cf);
              RETURN (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      let f = flow_of_cf cf;  
      RETURN f
    }"

    lemma edka3_refine: "edka3 \<le> \<Down>Id edka2"
      unfolding edka3_def edka2_def
      apply (rewrite in "let cf = Graph.augment_cf _ _ _ in _" Let_def)
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve)
      apply (drule Graph.shortestPath_is_simple)
      apply (frule (1) RGraph.bottleNeck_cf_impl_refine)
      apply (frule (1) RGraph.augment_cf_impl_refine)
      apply (auto simp: pw_le_iff refine_pw_simps)
      done
      
    
    subsection \<open>Refinement to use BFS\<close>

    text \<open>We refine the Edmonds-Karp algorithm to use breadth first search (BFS)\<close>
    definition "edka4 \<equiv> do {
      let cf = c;

      (cf,_) \<leftarrow> WHILET 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> Graph.bfs cf s t;
          case p of 
            None \<Rightarrow> RETURN (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.shortestPath cf s p t);
              bn \<leftarrow> bottleNeck_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              ASSERT (RGraph c s t cf);
              RETURN (cf, False)
            }  
        })
        (cf,False);
      ASSERT (RGraph c s t cf);
      let f = flow_of_cf cf;  
      RETURN f
    }"

    text \<open>A shortest path can be obtained by BFS\<close>  
    lemma bfs_refines_shortest_augmenting_spec: 
      "Graph.bfs cf s t \<le> find_shortest_augmenting_spec_cf cf"
      unfolding find_shortest_augmenting_spec_cf_def
      apply (rule le_ASSERTI)
      apply (rule order_trans)
      apply (rule Graph.bfs_correct)
      apply (simp add: RGraph.resV_netV s_node)
      apply (simp add: RGraph.resV_netV)
      apply (simp)
      done

    lemma edka4_refine: "edka4 \<le> \<Down>Id edka3"
      unfolding edka4_def edka3_def
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: bfs_refines_shortest_augmenting_spec)
      done


    subsection \<open>Implementing the Successor Function for BFS\<close>  

    definition "rg_succ ps cf u \<equiv>  
      filter (\<lambda>v. cf (u,v) > 0) (ps u)"
  
    lemma (in NFlow) E_ss_cfinvE: "E \<subseteq> Graph.E cf \<union> (Graph.E cf)\<inverse>"
      unfolding residualGraph_def Graph.E_def
      apply (clarsimp)
      using no_parallel_edge (* Speed optimization: Adding this directly takes very long *)
      apply simp
      done

    lemma (in RGraph) E_ss_cfinvE: "E \<subseteq> cf.E \<union> cf.E\<inverse>"  
      using f.E_ss_cfinvE by simp

    lemma (in NFlow) cfE_ss_invE: "Graph.E cf \<subseteq> E \<union> E\<inverse>"
      unfolding residualGraph_def Graph.E_def
      by auto

    lemma (in RGraph) cfE_ss_invE: "cf.E \<subseteq> E \<union> E\<inverse>"
      using f.cfE_ss_invE by simp
      

    lemma (in RGraph) rg_succ_ref1: "\<lbrakk>is_pred_succ ps c\<rbrakk> 
      \<Longrightarrow> (rg_succ ps cf u, Graph.E cf``{u}) \<in> \<langle>Id\<rangle>list_set_rel"
      apply (auto simp: list_set_rel_def br_def rg_succ_def Graph.E_def)
      using cfE_ss_invE apply (auto simp: is_pred_succ_def Graph.E_def) []
      apply (auto simp: is_pred_succ_def) []
      done

    definition ps_get_op :: "_ \<Rightarrow> node \<Rightarrow> node list nres" 
      where "ps_get_op ps u \<equiv> ASSERT (u\<in>V) \<guillemotright> RETURN (ps u)"

    definition "rg_succ2 ps cf u \<equiv> do {
      l \<leftarrow> ps_get_op ps u;
      RECT (\<lambda>D l. case l of 
        [] \<Rightarrow> RETURN [] 
      | (v#l) \<Rightarrow> do {
          rl \<leftarrow> D l;
          x \<leftarrow> cf_get cf (u,v);
          if x > 0 then RETURN (v#rl) else RETURN rl   
        }) l
      }"
  
    lemma (in RGraph) rg_succ_ref2: "\<lbrakk>is_pred_succ ps c; u\<in>V\<rbrakk> 
      \<Longrightarrow> rg_succ2 ps cf u \<le> RETURN (rg_succ ps cf u)"
    proof -
      def l \<equiv> "ps u"
  
      assume VN: "u\<in>V"
      assume V: "is_pred_succ ps c"
  
      have "\<forall>v\<in>set l. valid_edge (u,v)"
        using V VN 
        by (auto simp: is_pred_succ_def l_def Graph.V_def)
  
      thus ?thesis
        unfolding rg_succ2_def cf_get_def ps_get_op_def
        apply simp
        apply refine_vcg
        apply (simp add: VN) []
        apply (simp add: rg_succ_def l_def[symmetric])
    
        apply (induction l)
          apply (simp add: rg_succ_def) apply (subst RECT_unfold, refine_mono)
          apply simp
    
          apply (subst RECT_unfold, refine_mono)
          apply (simp split del: split_if)
          apply (simp add: pw_le_iff refine_pw_simps) 
          apply fastforce
        done
    qed    
  
    (* Snippet *)
    lemma (in RGraph) rg_succ_ref:
      assumes A: "is_pred_succ ps c"
      assumes B: "u\<in>V"
      shows "rg_succ2 ps cf u \<le> SPEC (\<lambda>l. (l,cf.E``{u}) \<in> \<langle>Id\<rangle>list_set_rel)"
      using rg_succ_ref1[OF A, of u] rg_succ_ref2[OF A B]
      by (auto simp: pw_le_iff refine_pw_simps)


    definition init_cf :: "graph nres" where "init_cf \<equiv> RETURN c"
    definition init_ps :: "(node \<Rightarrow> node list) \<Rightarrow> _" where 
      "init_ps ps \<equiv> ASSERT (is_pred_succ ps c) \<guillemotright> RETURN ps"

    definition compute_rflow :: "graph \<Rightarrow> flow nres" where
      "compute_rflow cf \<equiv> ASSERT (RGraph c s t cf) \<guillemotright> RETURN (flow_of_cf cf)"

    definition "bfs2_op ps cf \<equiv> Graph.bfs2 cf (rg_succ2 ps cf) s t"

    definition "edka5 ps \<equiv> do {
      cf \<leftarrow> init_cf;
      ps \<leftarrow> init_ps ps;

      (cf,_) \<leftarrow> WHILET 
        (\<lambda>(cf,brk). \<not>brk) 
        (\<lambda>(cf,_). do {
          ASSERT (RGraph c s t cf);
          p \<leftarrow> bfs2_op ps cf;
          case p of 
            None \<Rightarrow> RETURN (cf,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (Graph.shortestPath cf s p t);
              bn \<leftarrow> bottleNeck_cf_impl cf p;
              cf \<leftarrow> augment_cf_impl cf p bn;
              ASSERT (RGraph c s t cf);
              RETURN (cf, False)
            }  
        })
        (cf,False);
      f \<leftarrow> compute_rflow cf;  
      RETURN f
    }"
      

    lemma edka5_refine: "\<lbrakk>is_pred_succ ps c\<rbrakk> \<Longrightarrow> edka5 ps \<le> \<Down>Id edka4"
      unfolding edka5_def edka4_def init_cf_def compute_rflow_def
                init_ps_def Let_def nres_monad_laws bfs2_op_def
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve simp: )
      apply (rule refine_IdD)
      apply (rule Graph.bfs2_refine)
      apply (simp add: RGraph.resV_netV)
      apply (simp add: RGraph.rg_succ_ref)
      done

  end    

  subsection \<open>Imperative Implementation\<close>  

  locale Edka_Impl = Network +
    fixes N :: nat
    assumes V_ss: "V\<subseteq>{0..<N}"
  begin  
    lemma this_loc: "Edka_Impl c s t N" by unfold_locales

    lemmas [id_rules] = 
      itypeI[Pure.of N "TYPE(nat)"]  
      itypeI[Pure.of s "TYPE(node)"]  
      itypeI[Pure.of t "TYPE(node)"]  
      itypeI[Pure.of c "TYPE(graph)"]  
    lemmas [sepref_import_param] = 
      IdI[of N]
      IdI[of s]
      IdI[of t]
      IdI[of c]


    definition "is_ps ps psi \<equiv> \<exists>\<^sub>Al. psi \<mapsto>\<^sub>a l * \<up>(length l = N \<and> (\<forall>i<N. l!i = ps i) \<and> (\<forall>i\<ge>N. ps i = []))"
  
    lemma is_ps_precise[constraint_rules]: "precise (is_ps)"
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

    typedecl i_ps  

    definition (in -) "ps_get_imp psi u \<equiv> Array.nth psi u"

    lemma [def_pat_rules]: "Network.ps_get_op$c \<equiv> UNPROTECT ps_get_op" by simp
    sepref_register "PR_CONST ps_get_op" "i_ps \<Rightarrow> node \<Rightarrow> node list nres"

    lemma ps_get_op_refine[sepref_fr_rules]: 
      "(uncurry ps_get_imp, uncurry (PR_CONST ps_get_op)) \<in> is_ps\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a hn_list_aux (pure Id)"
      unfolding hn_list_pure_conv
      apply rule apply rule
      using V_ss
      by (sep_auto simp: is_ps_def pure_def ps_get_imp_def ps_get_op_def refine_pw_simps)


    lemma [def_pat_rules]: "Network.cf_get$c \<equiv> UNPROTECT cf_get" by simp
    lemma [def_pat_rules]: "Network.cf_set$c \<equiv> UNPROTECT cf_set" by simp

    sepref_register "PR_CONST cf_get" "capacity i_mtx \<Rightarrow> edge \<Rightarrow> capacity nres"
    sepref_register "PR_CONST cf_set" "capacity i_mtx \<Rightarrow> edge \<Rightarrow> capacity \<Rightarrow> capacity i_mtx nres"

    lemma [sepref_fr_rules]: "(uncurry (mtx_get N), uncurry (PR_CONST cf_get)) \<in> (is_mtx N)\<^sup>k *\<^sub>a (hn_prod_aux (pure Id) (pure Id))\<^sup>k \<rightarrow>\<^sub>a pure Id"
      apply rule apply rule
      using V_ss
      by (sep_auto simp: cf_get_def refine_pw_simps pure_def)

    lemma [sepref_fr_rules]: "(uncurry2 (mtx_set N), uncurry2 (PR_CONST cf_set)) 
      \<in> (is_mtx N)\<^sup>d *\<^sub>a (hn_prod_aux (pure Id) (pure Id))\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a (is_mtx N)"
      apply rule apply rule
      using V_ss
      by (sep_auto simp: cf_set_def refine_pw_simps pure_def hn_ctxt_def)

    lemma is_pred_succ_no_node: "\<lbrakk>is_pred_succ a c; u\<notin>V\<rbrakk> \<Longrightarrow> a u = []"
      unfolding is_pred_succ_def V_def
      by auto

    lemma [sepref_fr_rules]: "(Array.make N, PR_CONST init_ps) \<in> (pure Id)\<^sup>k \<rightarrow>\<^sub>a is_ps" 
      apply rule apply rule
      using V_ss
      by (sep_auto simp: init_ps_def refine_pw_simps is_ps_def pure_def
        intro: is_pred_succ_no_node)

    lemma [def_pat_rules]: "Network.init_ps$c \<equiv> UNPROTECT init_ps" by simp
    sepref_register "PR_CONST init_ps" "(node \<Rightarrow> node list) \<Rightarrow> i_ps nres"

    lemma init_cf_imp_refine[sepref_fr_rules]: 
      "(uncurry0 (mtx_new N c), uncurry0 (PR_CONST init_cf)) \<in> (pure unit_rel)\<^sup>k \<rightarrow>\<^sub>a is_mtx N"
      apply rule apply rule
      using V_ss
      by (sep_auto simp: init_cf_def)

    lemma [def_pat_rules]: "Network.init_cf$c \<equiv> UNPROTECT init_cf" by simp
    sepref_register "PR_CONST init_cf" "capacity i_mtx nres"


    definition (in Network) "is_rflow N f cfi \<equiv> \<exists>\<^sub>Acf. is_mtx N cf cfi * \<up>(f = flow_of_cf cf)"
    lemma is_rflow_precise[constraint_rules]: "precise (is_rflow N)"
      apply rule
      unfolding is_rflow_def
      apply clarsimp
      apply (rename_tac l l')
      apply prec_extract_eqs
      apply simp
      done

    typedecl i_rflow 

    lemma [sepref_fr_rules]: "(\<lambda>cfi. return cfi, PR_CONST compute_rflow) \<in> (is_mtx N)\<^sup>d \<rightarrow>\<^sub>a is_rflow N"
      apply rule
      apply rule
      apply (sep_auto simp: compute_rflow_def is_rflow_def refine_pw_simps hn_ctxt_def)
      done

    lemma [def_pat_rules]: "Network.compute_rflow$c$s$t \<equiv> UNPROTECT compute_rflow" by simp
    sepref_register "PR_CONST compute_rflow" "capacity i_mtx \<Rightarrow> i_rflow nres"


    schematic_lemma rg_succ2_impl:
      fixes ps :: "node \<Rightarrow> node list" and cf :: graph
      notes [id_rules] = 
        itypeI[Pure.of u "TYPE(node)"]
        itypeI[Pure.of ps "TYPE(i_ps)"]
        itypeI[Pure.of cf "TYPE(capacity i_mtx)"]
      notes [sepref_import_param] = IdI[of N]
      shows "hn_refine (hn_ctxt is_ps ps psi * hn_ctxt (is_mtx N) cf cfi * hn_val nat_rel u ui) (?c::?'c Heap) ?\<Gamma> ?R (rg_succ2 ps cf u)"
      unfolding rg_succ2_def APP_def 
      using [[id_debug, goals_limit = 1]]
      by sepref_keep
    concrete_definition (in -) succ_imp uses Edka_Impl.rg_succ2_impl
    prepare_code_thms (in -) succ_imp_def

    lemma succ_imp_refine[sepref_fr_rules]: "(uncurry2 (succ_imp N), uncurry2 (PR_CONST rg_succ2)) \<in> is_ps\<^sup>k *\<^sub>a (is_mtx N)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a hn_list_aux (pure Id)"
      apply rule
      using succ_imp.refine[OF this_loc]            
      by (auto simp: hn_ctxt_def hn_prod_aux_def mult_ac split: prod.split)

    lemma [def_pat_rules]: "Network.rg_succ2$c \<equiv> UNPROTECT rg_succ2" by simp
    sepref_register "PR_CONST rg_succ2" "i_ps \<Rightarrow> capacity i_mtx \<Rightarrow> node \<Rightarrow> node list nres"

    
    lemma [sepref_import_param]: "(min,min)\<in>Id\<rightarrow>Id\<rightarrow>Id" by simp

    abbreviation "is_path \<equiv> hn_list_aux (hn_prod_aux (pure Id) (pure Id))"

    schematic_lemma bottleNeck_imp_impl:
      fixes ps :: "node \<Rightarrow> node list" and cf :: graph
      notes [id_rules] = 
        itypeI[Pure.of p "TYPE(edge list)"]
        itypeI[Pure.of cf "TYPE(node i_mtx)"]
      notes [sepref_import_param] = IdI[of N]
      shows "hn_refine (hn_ctxt (is_mtx N) cf cfi * hn_ctxt is_path p pi) (?c::?'c Heap) ?\<Gamma> ?R (bottleNeck_cf_impl cf p)"
      unfolding bottleNeck_cf_impl_def APP_def
      using [[id_debug, goals_limit = 1]]
      by sepref_keep
    concrete_definition (in -) bottleNeck_imp uses Edka_Impl.bottleNeck_imp_impl
    prepare_code_thms (in -) bottleNeck_imp_def

    lemma bottleNeck_impl_refine[sepref_fr_rules]: 
      "(uncurry (bottleNeck_imp N), uncurry (PR_CONST bottleNeck_cf_impl)) 
        \<in> (is_mtx N)\<^sup>k *\<^sub>a (is_path)\<^sup>k \<rightarrow>\<^sub>a (pure Id)"
      apply rule
      apply (rule hn_refine_preI)
      apply (clarsimp simp: uncurry_def hn_list_pure_conv hn_ctxt_def split: prod.split)
      apply (clarsimp simp: pure_def)
      apply (rule hn_refine_cons'[OF _ bottleNeck_imp.refine[OF this_loc] _])
      apply (simp add: hn_list_pure_conv hn_ctxt_def)
      apply (simp add: pure_def)
      apply (simp add: hn_ctxt_def)
      apply (simp add: pure_def)
      done

    lemma [def_pat_rules]: "Network.bottleNeck_cf_impl$c \<equiv> UNPROTECT bottleNeck_cf_impl" by simp
    sepref_register "PR_CONST bottleNeck_cf_impl" "capacity i_mtx \<Rightarrow> path \<Rightarrow> capacity nres"
    
    schematic_lemma augment_imp_impl:
      fixes ps :: "node \<Rightarrow> node list" and cf :: graph
      notes [id_rules] = 
        itypeI[Pure.of p "TYPE(edge list)"]
        itypeI[Pure.of cf "TYPE(node i_mtx)"]
        itypeI[Pure.of cap "TYPE(capacity)"]
      notes [sepref_import_param] = IdI[of N]
      shows "hn_refine (hn_ctxt (is_mtx N) cf cfi * hn_ctxt is_path p pi * hn_val Id cap capi) (?c::?'c Heap) ?\<Gamma> ?R (augment_cf_impl cf p cap)"
      unfolding augment_cf_impl_def augment_edge_impl_def APP_def
      using [[id_debug, goals_limit = 1]]
      by sepref_keep
    concrete_definition (in -) augment_imp uses Edka_Impl.augment_imp_impl
    prepare_code_thms (in -) augment_imp_def

    thm augment_imp_def augment_cf_impl_def

    lemma augment_impl_refine[sepref_fr_rules]: 
      "(uncurry2 (augment_imp N), uncurry2 (PR_CONST augment_cf_impl)) 
        \<in> (is_mtx N)\<^sup>d *\<^sub>a (is_path)\<^sup>k *\<^sub>a (pure Id)\<^sup>k \<rightarrow>\<^sub>a is_mtx N"
      apply rule
      apply (rule hn_refine_preI)
      apply (clarsimp simp: uncurry_def hn_list_pure_conv hn_ctxt_def split: prod.split)
      apply (clarsimp simp: pure_def)
      apply (rule hn_refine_cons'[OF _ augment_imp.refine[OF this_loc] _])
      apply (simp add: hn_list_pure_conv hn_ctxt_def)
      apply (simp add: pure_def)
      apply (simp add: hn_ctxt_def)
      apply (simp add: pure_def)
      done

    lemma [def_pat_rules]: "Network.augment_cf_impl$c \<equiv> UNPROTECT augment_cf_impl" by simp
    sepref_register "PR_CONST augment_cf_impl" "capacity i_mtx \<Rightarrow> path \<Rightarrow> capacity \<Rightarrow> capacity i_mtx nres"

    thm succ_imp_def
    sublocale bfs!: Impl_Succ "snd" "TYPE(i_ps \<times> capacity i_mtx)" 
      "\<lambda>(ps,cf). rg_succ2 ps cf" "hn_prod_aux is_ps (is_mtx N)" "\<lambda>(ps,cf). succ_imp N ps cf"
      unfolding APP_def
      apply unfold_locales
      apply constraint_rules
      apply (simp add: fold_partial_uncurry)
      apply (rule hfref_cons[OF succ_imp_refine[unfolded PR_CONST_def]])
      by auto
      
    (*lemmas bfs_impl_def = bfs.bfs_impl_def

    concrete_definition (in -) bfsi uses Edka_Impl.bfs_impl_def
    (*lemmas [sepref_fr_rules] = bfs.bfs_impl_fr_rule[unfolded bfsi.refine[OF this_loc,abs_def]]*)
    prepare_code_thms (in -) bfsi_def*)
   
    (*thm bfs.bfs_impl_fr_rule[unfolded bfsi.refine[OF this_loc,abs_def]]*)
    thm bfs.bfs_impl_fr_rule
    term bfs_impl
    definition (in -) "bfsi' N s t psi cfi \<equiv> bfs_impl (\<lambda>(ps, cf). succ_imp N ps cf) (psi,cfi) s t"

    lemma [sepref_fr_rules]: "(uncurry (bfsi' N s t),uncurry (PR_CONST bfs2_op)) \<in> is_ps\<^sup>k *\<^sub>a (is_mtx N)\<^sup>k \<rightarrow>\<^sub>a hn_option_aux is_path"
      unfolding bfsi'_def[abs_def]
      using bfs.bfs_impl_fr_rule
      apply (simp add: uncurry_def bfs.op_bfs_def[abs_def] bfs2_op_def)
      apply (clarsimp simp: hfref_def all_to_meta)
      apply (rule hn_refine_cons[rotated])
      apply rprems
      apply (sep_auto simp: pure_def)
      apply (sep_auto simp: pure_def)
      apply (sep_auto simp: pure_def)
      done

    lemma [def_pat_rules]: "Network.bfs2_op$c$s$t \<equiv> UNPROTECT bfs2_op" by simp
    sepref_register "PR_CONST bfs2_op" "i_ps \<Rightarrow> capacity i_mtx \<Rightarrow> path option nres"  


    schematic_lemma edka_imp_impl:
      fixes ps :: "node \<Rightarrow> node list" and cf :: graph
      notes [id_rules] = 
        itypeI[Pure.of ps "TYPE(node \<Rightarrow> node list)"]
      notes [sepref_import_param] = IdI[of ps]
      shows "hn_refine (emp) (?c::?'c Heap) ?\<Gamma> ?R (edka5 ps)"
      unfolding edka5_def
      using [[id_debug, goals_limit = 1]]
      by sepref_keep

    concrete_definition (in -) edka_imp uses Edka_Impl.edka_imp_impl
    lemmas edka_imp_refine = edka_imp.refine[OF this_loc]
  end

  export_code edka_imp checking SML_imp



  context Network begin
    theorem edka_imp_correct: 
      assumes VN: "Graph.V c \<subseteq> {0..<N}"
      assumes ABS_PS: "is_pred_succ ps c"
      shows "<emp> edka_imp c s t N ps <\<lambda>fi. \<exists>\<^sub>Af. is_rflow N f fi * \<up>(isMaxFlow c s t f)>\<^sub>t"
    proof -
      interpret Edka_Impl by unfold_locales fact

      note edka5_refine[OF ABS_PS]
      also note edka4_refine                 
      also note edka3_refine    
      also note edka2_refine 
      also note edka_refine
      also note fofu_total_correct
      finally have "edka5 ps \<le> SPEC (isMaxFlow c s t)" .
      from hn_refine_ref[OF this edka_imp_refine]
      show ?thesis 
        by (simp add: hn_refine_def)
    qed
  end    
end
