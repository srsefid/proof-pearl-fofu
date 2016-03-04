theory Ford_Fulkerson
imports Augmenting ResidualGraph
begin




  (* Ford-Fulkerson theorem *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context FoFu
  begin
    lemma fofu_I_II: "isMaxFlow c s t f \<Longrightarrow> \<not> (\<exists> p. isAugmenting p)"
      unfolding isMaxFlow_def
      proof (rule ccontr)
        assume asm: "NFlow c s t f \<and> (\<forall>f'. NFlow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
        assume asm_c: "\<not> \<not> (\<exists> p. isAugmenting p)"
        then obtain p where obt: "isAugmenting p" by blast
        have fct1: "Flow cf s t (augmentingFlow p)" using obt augFlow_resFlow by auto
        have fct2: "Flow.val cf s (augmentingFlow p) > 0" using obt augFlow_val
          bottleNeck_gzero isAugmenting_def cf.isSimplePath_def by auto
        have "NFlow c s t (augment (augmentingFlow p))" 
          using fct1 augment_flow_presv Network_axioms unfolding NFlow_def by auto
        moreover have "Flow.val c s (augment (augmentingFlow p)) > val" 
          using fct1 fct2 augment_flow_value by auto
        ultimately show "False" using asm by auto
      qed
      
    lemma fofu_II_III: "\<not> (\<exists> p. isAugmenting p) \<Longrightarrow> \<exists>k'. NCut c s t k' \<and> val = NCut.cap c k'" 
      proof -
        assume asm: "\<not> (\<exists> p. isAugmenting p) "
        then have fct1: "\<not> (\<exists> p. Graph.isPath cf s p t)" using
          isAugmenting_def Graph.isSPath_pathLE by metis
        {
          have "Graph.reachableNodes cf s \<subseteq> V"  using cf.reachable_ss_V s_node resV_netV by auto
          moreover have "s \<in> Graph.reachableNodes cf s" unfolding Graph.reachableNodes_def 
            Graph.connected_def by (metis Graph.isPath.simps(1) mem_Collect_eq)
          moreover have "t \<notin> Graph.reachableNodes cf s" unfolding Graph.reachableNodes_def
            Graph.connected_def using fct1 by auto
          ultimately have "NCut c s t (Graph.reachableNodes cf s)" unfolding NCut_def Cut_def 
            NCut_axioms_def using Network_axioms by auto
        } note fct2 = this
        then have "FoFu c s t (Graph.reachableNodes cf s) f" (is "FoFu c s t ?K' f")
          unfolding FoFu_def using NFlow_axioms by auto
        then have "val = (\<Sum>e \<in> outgoing' ?K'. f e) - (\<Sum>e \<in> incoming' ?K'. f e)" 
          using FoFu.flow_value FoFu.netFlow_def by fastforce
        moreover {
          {
            fix e
            assume "e \<in> outgoing' ?K'"
            then obtain u v where obt: "e = (u, v)" by (metis nat_gcd.cases)
            then have fct_s: "u \<in> ?K' \<and> v \<notin> ?K' \<and> (u, v) \<in> E" 
              using `e \<in> outgoing' ?K'` outgoing'_def by auto
            
            have "f e = c e"
              proof (rule ccontr)
                assume "\<not> f e = c e"
                then have "f e < c e" using capacity_const by (metis (no_types) eq_iff not_le)
                then have "cf (u, v) \<noteq> 0" unfolding residualGraph_def using obt fct_s by auto
                then have "(u, v) \<in> Graph.E cf" unfolding Graph.E_def by simp
                then have "Graph.isPath cf u [(u, v)] v"
                  by (metis (poly_guards_query) Graph.isPath.simps(1) Graph.isPath.simps(2))
                moreover obtain p where "Graph.isPath cf s p u" 
                  using fct_s cf.reachableNodes_def cf.connected_def by auto
                ultimately have "Graph.isPath cf s (p @ [(u, v)]) v" 
                  using cf.isPath_append by auto
                thus "False" using fct_s cf.reachableNodes_def cf.connected_def by auto
              qed
          }
          then have "(\<Sum>e \<in> outgoing' ?K'. f e) = NCut.cap c ?K'"
            using NCut.cap_def[OF fct2] by auto
        }
        moreover {
          {
            fix e
            assume "e \<in> incoming' ?K'"
            then obtain u v where obt: "e = (v, u)" by (metis nat_gcd.cases)
            then have fct_s: "u \<in> ?K' \<and> v \<notin> ?K' \<and> (v, u) \<in> E" 
              using `e \<in> incoming' ?K'` incoming'_def by auto
            then have fct_s2: "(u, v) \<notin> E" using no_parallel_edge E_def by auto
              
            have "f e = 0"
              proof (rule ccontr)
                assume "\<not> f e = 0"
                then have "cf (u, v) \<noteq> 0" unfolding residualGraph_def
                  using obt fct_s fct_s2 by (auto simp: E_def)
                then have "(u, v) \<in> Graph.E cf" unfolding Graph.E_def by simp
                then have "Graph.isPath cf u [(u, v)] v"
                  by (metis Graph.isPath.simps(1) Graph.isPath.simps(2))
                moreover obtain p where "Graph.isPath cf s p u" 
                  using fct_s cf.reachableNodes_def cf.connected_def by auto
                ultimately have "Graph.isPath cf s (p @ [(u, v)]) v" 
                  using cf.isPath_append by auto
                thus "False" using fct_s cf.reachableNodes_def cf.connected_def by auto   
              qed
          }
          then have "(\<Sum>e \<in> incoming' ?K'. f e) = 0" using NCut.cap_def[OF fct2] by auto
        }
        ultimately have "NCut c s t ?K' \<and> val = NCut.cap c (Graph.reachableNodes cf s)" 
          using fct2 by auto
        thus ?thesis by auto
      qed
      
    lemma fofu_III_I: "val = cap \<Longrightarrow> isMaxFlow c s t f"
      proof -
        assume asm: "val = cap"
        {
          fix f'
          assume "NFlow c s t f'"
          then have "FoFu c s t k f'" unfolding FoFu_def using NCut_axioms by auto
          then have "Flow.val c s f' \<le> cap" using FoFu.weak_duality by fastforce
          then have "Flow.val c s f' \<le> val" using asm by auto
        }
        moreover have "NFlow c s t f" using FoFu_def FoFu_axioms by blast
        ultimately show ?thesis unfolding isMaxFlow_def by auto
      qed

    (* Snippet for presentation. 
      Needs explanation on II: We are in a context with a fixed cut and flow. *)  
    theorem ford_fulkerson:
      "isMaxFlow c s t f \<Longrightarrow> \<not> Ex isAugmenting"
      "\<not> Ex isAugmenting \<Longrightarrow> \<exists>k'. NCut c s t k' \<and> val = NCut.cap c k'"
      "val = cap \<Longrightarrow> isMaxFlow c s t f"
      using fofu_I_II fofu_II_III fofu_III_I by auto


  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Extra results *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    lemma maxFlow_iff_noAugPath: "\<not> (\<exists> p. isAugmenting p) \<longleftrightarrow> isMaxFlow c s t f"
      proof -
        let ?S = "{s}"
        have "?S \<subseteq> V" using s_node by blast
        moreover have "s \<in> ?S" by blast
        moreover have "t \<notin> ?S" using s_not_t by blast
        ultimately have "NCut c s t ?S" unfolding NCut_def NCut_axioms_def Cut_def 
          using Network_axioms by auto
        then interpret nc'!: FoFu c s t ?S f unfolding FoFu_def using NFlow_axioms by auto
        show ?thesis
          proof
            assume "\<not> (\<exists> p. isAugmenting p)"
            from nc'.fofu_II_III[OF this] obtain k' where 
              "NCut c s t k'" and 1: "val = NCut.cap c k'" by blast
            then interpret nc''!: NCut c s t k' by simp
            interpret nc''!: FoFu c s t k' f by unfold_locales
            from nc''.fofu_III_I[OF 1] show "isMaxFlow c s t f" .
          qed (blast dest: nc'.fofu_I_II)
      qed
  end
  
  
  context FoFu
  begin
    lemma maxFlow_minCut: "\<lbrakk>isMaxFlow c s t f; isMinCut c s t k\<rbrakk> \<Longrightarrow> val = cap"
      proof -
        assume asm1: "isMaxFlow c s t f"
        assume asm2: "isMinCut c s t k"
        note f1 = fofu_I_II[OF asm1]
        note f2 = fofu_II_III[OF f1]
        obtain k' where obt1: "NCut c s t k'" and obt2: "val = NCut.cap c k'" using f2 by blast
        {
          fix k''
          assume asm3: "NCut c s t k''"
          then interpret ff_k''!: FoFu c s t k'' f using FoFu_axioms unfolding FoFu_def by simp
          interpret ff_k'!: FoFu c s t k' f using obt1 FoFu_axioms unfolding FoFu_def by simp
          have "val \<le> ff_k''.cap" using ff_k''.weak_duality by simp
          then have "ff_k'.cap \<le> ff_k''.cap" using obt2 by simp 
        }
        then have "isMinCut c s t k'" unfolding isMinCut_def using obt1 by simp
        then have "NCut.cap c k' = cap" using asm2 unfolding isMinCut_def by force
        thus ?thesis using obt2 by simp
      qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
end
