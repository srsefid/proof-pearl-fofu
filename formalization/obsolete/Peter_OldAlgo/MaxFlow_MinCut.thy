theory MaxFlow_MinCut
imports Augmenting
begin

  context FoFu
  begin
    lemma maxFlow_minCut_I_II: "isMaxFlow c s t f \<Longrightarrow> \<not> (\<exists> p. isAugmenting p)"
      unfolding isMaxFlow_def
      proof (rule ccontr)
        assume asm: "NFlow c s t f \<and> (\<forall>f'. NFlow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
        assume asm_c: "\<not> \<not> (\<exists> p. isAugmenting p)"
        then obtain p where obt: "isAugmenting p" by blast
        have fct1: "Flow cf s t (augmentingFlow p)" using obt augFlow_resFlow by auto
        have fct2: "Flow.val cf s (augmentingFlow p) > 0" using obt augFlow_val
          bottleNeck_gzero isAugmenting_def Graph.isSimplePath_def by auto
        have "NFlow c s t (augment (augmentingFlow p))" 
          using fct1 augment_flow_presv Network_axioms NFlow_def by auto
        moreover have "Flow.val c s (augment (augmentingFlow p)) > val" 
          using fct1 fct2 augment_flow_value by auto
        ultimately show "False" using asm by auto
      qed
      
    lemma maxFlow_minCut_II_III: "\<not> (\<exists> p. isAugmenting p) \<Longrightarrow> \<exists>k'. NCut c s t k' \<and> val = NCut.cap c k'" 
      proof -
        assume asm: "\<not> (\<exists> p. isAugmenting p) "
        then have fct1: "\<not> (\<exists> p. Graph.isPath cf s p t)" using
          isAugmenting_def Graph.isSPath_pathLE by metis
        {
          have "Graph.reachable cf s \<subseteq> V"  using Graph.reachable_ss_V s_node resV_netV by auto
          moreover have "s \<in> Graph.reachable cf s" unfolding Graph.reachable_def 
            Graph.isReachable_def by (metis Graph.isPath.simps(1) mem_Collect_eq)
          moreover have "t \<notin> Graph.reachable cf s" unfolding Graph.reachable_def
            Graph.isReachable_def using fct1 by auto
          ultimately have "NCut c s t (Graph.reachable cf s)" unfolding NCut_def Cut_def 
            NCut_axioms_def using Network_axioms by auto
        } note fct2 = this
        then have "FoFu c s t (Graph.reachable cf s) f" (is "FoFu c s t ?K' f")
          unfolding FoFu_def using NFlow_axioms by auto
        then have "val = (\<Sum>e \<in> outgoing' ?K'. f e) - (\<Sum>e \<in> incoming' ?K'. f e)" 
          using FoFu.flow_value FoFu.netFlow_def by auto
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
                then have "f e < c e" using capacity_cons by (metis le_neq_implies_less)
                then have "cf (u, v) \<noteq> 0" unfolding residualGraph_def using obt fct_s by auto
                then have "(u,v)\<in>Graph.E cf" by (simp add: Graph.E_def)
                then have "Graph.isPath cf u [(u, v)] v"
                  by (metis (poly_guards_query) Graph.isPath.simps(1) Graph.isPath.simps(2))
                moreover obtain p where "Graph.isPath cf s p u" 
                  using fct_s Graph.reachable_def Graph.isReachable_def by auto
                ultimately have "Graph.isPath cf s (p @ [(u, v)]) v" 
                  using Graph.isPath_append by auto
                thus "False" using fct_s Graph.reachable_def Graph.isReachable_def by auto
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
                then have "cf (u, v) \<noteq> 0" unfolding residualGraph_def using obt fct_s fct_s2 by (auto simp: E_def)
                then have "(u,v)\<in>Graph.E cf" by (simp add: Graph.E_def)
                then have "Graph.isPath cf u [(u, v)] v"
                  by (metis Graph.isPath.simps(1) Graph.isPath.simps(2))
                moreover obtain p where "Graph.isPath cf s p u" 
                  using fct_s Graph.reachable_def Graph.isReachable_def by auto
                ultimately have "Graph.isPath cf s (p @ [(u, v)]) v" 
                  using Graph.isPath_append by auto
                thus "False" using fct_s Graph.reachable_def Graph.isReachable_def by auto   
              qed
          }
          then have "(\<Sum>e \<in> incoming' ?K'. f e) = 0" using NCut.cap_def[OF fct2] by auto
        }
        ultimately have "NCut c s t ?K' \<and> val = NCut.cap c (Graph.reachable cf s)" 
          using fct2 by auto
        thus ?thesis by auto
      qed
      
    lemma maxFlow_minCut_III_I: "val = cap \<Longrightarrow> isMaxFlow c s t f"
      proof -
        assume asm: "val = cap"
        {
          fix f'
          assume "NFlow c s t f'"
          then have "FoFu c s t k f'" unfolding FoFu_def using NCut_axioms by auto
          then have "Flow.val c s f' \<le> cap" using FoFu.weak_duality by auto
          then have "Flow.val c s f' \<le> val" using asm by auto
        }
        moreover have "NFlow c s t f" using FoFu_def FoFu_axioms by blast
        ultimately show ?thesis unfolding isMaxFlow_def by auto
      qed


    (* moved this corollay ro NFlow *)  
    (* corollary maxFlow_iff_no_augmenting: "\<not> (\<exists> p. isAugmenting p) \<longleftrightarrow> isMaxFlow"  
      proof
        assume "\<not> (\<exists> p. isAugmenting p)"
        from maxFlow_minCut_II_III[OF this] obtain k' where 
          "NCut c s t k'" and 1: "val = NCut.cap c k'" by blast
        then interpret nc'!: NCut c s t k' by simp
        interpret nc'!: FoFu c s t k' f by unfold_locales
        from nc'.maxFlow_minCut_III_I[OF 1] show isMaxFlow .
      qed (blast dest: maxFlow_minCut_I_II) *)
  end
  
  context NFlow
  begin
    corollary maxFlow_iff_noAugPath: "\<not> (\<exists> p. isAugmenting p) \<longleftrightarrow> isMaxFlow c s t f"
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
            from nc'.maxFlow_minCut_II_III[OF this] obtain k' where 
              "NCut c s t k'" and 1: "val = NCut.cap c k'" by blast
            then interpret nc''!: NCut c s t k' by simp
            interpret nc''!: FoFu c s t k' f by unfold_locales
            from nc''.maxFlow_minCut_III_I[OF 1] show "isMaxFlow c s t f" .
          qed (blast dest: nc'.maxFlow_minCut_I_II)
      qed
  end
  
end