(* TODO: To be merged with Graph, once graph 
  has been merged with generic capacity version. *)
theory Temporary_Graph_Add
imports Misc Graph
begin

  (* Graph: Finite Graphs *)  
  context Graph
  begin
    lemma E_ss_VxV: "E \<subseteq> V\<times>V" by (auto simp: V_def)

    lemma Vfin_imp_Efin[simp, intro]: assumes "finite V" shows "finite E"
      using E_ss_VxV assms by (auto intro: finite_subset)

    lemma Efin_imp_Vfin: "finite E \<Longrightarrow> finite V"
      unfolding V_alt by auto

  end

  (* TODO: Move *)
  locale Finite_Graph = Graph +
    assumes finite_V[simp, intro!]: "finite V"
  begin  
    lemma finiteE[simp,intro!]: "finite E" by simp
  end


  lemma (in Graph) Finite_Graph_EI: "finite E \<Longrightarrow> Finite_Graph c"
    apply unfold_locales
    by (rule Efin_imp_Vfin)


    



  (* Graph: Paths *)  
  context Graph 
  begin

    lemma transfer_path:
      -- \<open>Transfer path to another graph\<close>
      assumes "set p\<inter>E \<subseteq> Graph.E c'"
      assumes "isPath u p v"
      shows "Graph.isPath c' u p v"
      using assms
      apply (induction u p v rule: isPath.induct)
      apply (auto simp: Graph.isPath.simps)
      done


    lemma isPath_append_edge: "isPath v p v' \<Longrightarrow> (v',v'')\<in>E \<Longrightarrow> isPath v (p@[(v',v'')]) v''"  
      by (auto simp: isPath_append E_def)

    lemma split_path_at_vertex:
      assumes "isPath s p t" "pathVertices s p = pv1@u#pv2" 
      obtains p1 p2 where 
        "p=p1@p2" 
        "isPath s p1 u" "pathVertices s p1 = pv1@[u]" 
        "isPath u p2 t" "pathVertices u p2 = u#pv2" 
    proof -
      show thesis    
        using assms
        apply (cases p rule: rev_cases; clarsimp simp: pathVertices_alt)
          apply (rule that[of "[]" "[]"]; simp)

          apply (cases pv2; clarsimp)
          apply (rule that[of p "[]"]; auto simp add: isPath_append pathVertices_alt)      
      
          apply (clarsimp simp: append_eq_append_conv2; 
            auto elim!: map_eq_concE map_eq_consE list_append_eq_Cons_cases
                simp: isPath_append)

            apply (rename_tac l)
            apply (erule that) apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)

            apply (rename_tac l)
            apply (erule that) apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)

            apply (rename_tac l u1 u2 u3)
            apply (erule that) apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)
            apply (auto simp: isPath_append) []
            apply (auto simp: pathVertices_alt) []
            
            apply (rename_tac l)
            apply (erule that) apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)
        done
    qed

    lemma pathVertices_singleton_iff[simp]: "pathVertices s p = [u] \<longleftrightarrow> (p=[] \<and> s=u)"
      apply (cases p rule: rev_cases)
      apply (auto simp: pathVertices_alt)
      done

    lemma length_pathVertices_eq[simp]: "length (pathVertices u p) = length p + 1"
      apply (cases "p=[]")
      apply (auto simp: pathVertices_alt)
      done

    lemma pathVertices_edgeset: "\<lbrakk>u\<in>V; isPath u p v\<rbrakk> \<Longrightarrow> set (pathVertices u p) \<subseteq> V"
      apply (cases p rule: rev_cases; simp)
      using isPath_edgeset[of u p v]
      apply (fastforce simp: pathVertices_alt V_def)
      done

    lemma simplePath_length_less_V:
      assumes FIN: "finite V"
      assumes UIV: "u\<in>V"
      assumes P: "isSimplePath u p v" 
      shows "length p < card V"
    proof -
      from P have 1: "isPath u p v" and 2: "distinct (pathVertices u p)"
        by (auto simp: isSimplePath_def)
      from pathVertices_edgeset[OF UIV 1] have "set (pathVertices u p) \<subseteq> V" .
      with 2 FIN have "length (pathVertices u p) \<le> card V"
        using distinct_card card_mono by metis
      hence "length p + 1 \<le> card V" by simp
      thus ?thesis by auto
    qed      




    lemma split_simple_path: "isSimplePath u (p1@p2) v 
      \<Longrightarrow> (\<exists>w. isSimplePath u p1 w \<and> isSimplePath w p2 v)"
      apply (auto simp: isSimplePath_def isPath_append)
      apply (rule exI; intro conjI; assumption?)
      apply (cases p1 rule: rev_cases) []
      apply simp
      apply (cases p2)
      apply simp
      apply (clarsimp simp: pathVertices_alt isPath_append)

      apply (cases p1 rule: rev_cases) []
      apply simp
      apply (cases p2  rule: rev_cases)
      apply simp
      apply (clarsimp simp: pathVertices_alt isPath_append)
      done  
      
    lemma simplePath_empty_conv[simp]: "isSimplePath s [] t \<longleftrightarrow> s=t"
      by (auto simp: isSimplePath_def)

    lemma simplePath_same_conv[simp]: "isSimplePath s p s \<longleftrightarrow> p=[]"  
      apply rule
      apply (cases p; simp)
      apply (rename_tac e pp)
      apply (case_tac pp rule: rev_cases; simp)
      apply (auto simp: isSimplePath_def pathVertices_alt isPath_append) [2]
      apply simp
      done



  end

  (* Graph: Distance and shortest Path *)  
  context Graph
  begin
    subsubsection \<open>Distance\<close>
    text \<open>We define predicates to reason about distance and minimum distance between nodes\<close>
    definition dist :: "node \<Rightarrow> nat \<Rightarrow> node \<Rightarrow> bool" 
      -- \<open>There is a path of given length between the nodes\<close>
      where "dist v d v' \<equiv> \<exists>p. isPath v p v' \<and> length p = d"
    (*abbreviation (input) connected :: "node \<Rightarrow> node \<Rightarrow> bool"
      -- \<open>Predicate that two nodes are connected\<close> (* TODO: Rename isReachable to connected! *)
      where "connected \<equiv> isReachable"*)
    definition min_dist :: "node \<Rightarrow> node \<Rightarrow> nat"
      -- \<open>Minimum distance between two connected nodes\<close>
      where "min_dist v v' = (LEAST d. dist v d v')"
    
    lemma connected_by_dist: "connected v v' = (\<exists>d. dist v d v')"
      by (auto simp: dist_def connected_def)

    lemma isPath_distD: "isPath u p v \<Longrightarrow> dist u (length p) v"
      by (auto simp: dist_def)



    lemma
      shows connI[intro]: "dist v d v' \<Longrightarrow> connected v v'"
        and connI_id[intro!, simp]: "connected v v"
        and connI_succ: "connected v v' \<Longrightarrow> (v',v'') \<in> E \<Longrightarrow> connected v v''"
      by (auto simp: dist_def connected_def intro: isPath_append_edge)
      
  
    lemma min_distI2: 
      "\<lbrakk> connected v v' ; \<And>d. \<lbrakk> dist v d v'; \<And>d'. dist v d' v' \<Longrightarrow> d \<le> d' \<rbrakk> \<Longrightarrow> Q d \<rbrakk> 
        \<Longrightarrow> Q (min_dist v v')"
      unfolding min_dist_def
      apply (rule LeastI2_wellorder[where Q=Q and a="SOME d. dist v d v'"])
      apply (auto simp: connected_by_dist intro: someI)
      done
  
    lemma min_distI_eq:
      "\<lbrakk> dist v d v'; \<And>d'. dist v d' v' \<Longrightarrow> d \<le> d' \<rbrakk> \<Longrightarrow> min_dist v v' = d"
      by (force intro: min_distI2 simp: connected_by_dist)
  
    text {* Two nodes are connected by a path of length @{text "0"}, 
      iff they are equal. *}
    lemma dist_z_iff[simp]: "dist v 0 v' \<longleftrightarrow> v'=v"
      by (auto simp: dist_def)
  

    lemma dist_z[simp, intro!]: "dist v 0 v" by simp
    lemma dist_suc: "\<lbrakk>dist v d v'; (v',v'')\<in>E\<rbrakk> \<Longrightarrow> dist v (Suc d) v''"
      by (auto simp: dist_def intro: isPath_append_edge)

    lemma dist_cases[case_names dist_z dist_suc, consumes 1, cases pred]:
      assumes "dist v d v'"
      obtains "v=v'" "d=0"
       | vh dd where "d=Suc dd" "dist v dd vh" "(vh,v')\<in>E"
      using assms 
      apply (cases d)
      apply (auto simp: dist_def length_Suc_rev_conv isPath_append) 
      apply force
      done


    text {* The same holds for @{text "min_dist"}, i.e., 
      the shortest path between two nodes has length @{text "0"}, 
      iff these nodes are equal. *}
    lemma min_dist_z[simp]: "min_dist v v = 0"
      by (rule min_distI2) auto
  
    lemma min_dist_z_iff[simp]: "connected v v' \<Longrightarrow> min_dist v v' = 0 \<longleftrightarrow> v'=v" 
      by (rule min_distI2) (auto)
      
    lemma min_dist_is_dist: "connected v v' \<Longrightarrow> dist v (min_dist v v') v'"
      by (auto intro: min_distI2)
    lemma min_dist_minD: "dist v d v' \<Longrightarrow> min_dist v v' \<le> d"
      by (auto intro: min_distI2)
  
    text {* We also provide introduction and destruction rules for the
      pattern @{text "min_dist v v' = Suc d"}.
      *}
  
    lemma min_dist_succ: 
      "\<lbrakk> connected v v'; (v',v'') \<in> E \<rbrakk> \<Longrightarrow> min_dist v v'' \<le> Suc (min_dist v v') "
      apply (rule min_distI2[where v'=v'])
      apply (auto intro!: min_dist_minD intro: dist_suc)
      done
  
    lemma min_dist_suc:
      assumes c: "connected v v'" "min_dist v v' = Suc d"
      shows "\<exists>v''. connected v v'' \<and> (v'',v') \<in> E \<and> min_dist v v'' = d"
    proof -
      from min_dist_is_dist[OF c(1)]
      have "min_dist v v' = Suc d \<longrightarrow> ?thesis"
      proof cases
        case (dist_suc v'' d') then show ?thesis
          using min_dist_succ[of v v'' v'] min_dist_minD[of v d v'']
          by (auto simp: connI)
      qed simp
      with c show ?thesis by simp
    qed
  
    text {*
      If there is a node with a shortest path of length @{text "d"}, 
      then, for any @{text "d'<d"}, there is also a node with a shortest path
      of length @{text "d'"}.
      *}
    lemma min_dist_less:
      assumes "connected src v" "min_dist src v = d" and "d' < d"
      shows "\<exists>v'. connected src v' \<and> min_dist src v' = d'"
      using assms
    proof (induct d arbitrary: v)
      case (Suc d) with min_dist_suc[of src v] show ?case
        by (cases "d' = d") auto
    qed auto
  
    text {*
      Lemma @{text "min_dist_less"} can be weakened to @{text "d'\<le>d"}.
      *}
  
    corollary min_dist_le:
      assumes c: "connected src v" and d': "d' \<le> min_dist src v"
      shows "\<exists>v'. connected src v' \<and> min_dist src v' = d'"
      using min_dist_less[OF c, of "min_dist src v" d'] d' c
      by (auto simp: le_less)


    lemma dist_trans[trans]: "dist u d1 w \<Longrightarrow> dist w d2 v \<Longrightarrow> dist u (d1+d2) v"  
      apply (clarsimp simp: dist_def)
      apply (rename_tac p1 p2)
      apply (rule_tac x="p1@p2" in exI)
      by (auto simp: isPath_append)


    lemma min_dist_split:
      assumes D1: "dist u d1 w" and D2: "dist w d2 v" and MIN: "min_dist u v = d1+d2"
      shows "min_dist u w = d1" "min_dist w v = d2"
      apply (metis assms ab_semigroup_add_class.add.commute add_le_cancel_left dist_trans min_distI_eq min_dist_minD)
      by (metis assms add_le_cancel_left dist_trans min_distI_eq min_dist_minD)
      
    lemma -- \<open>Manual proof\<close>
      assumes D1: "dist u d1 w" and D2: "dist w d2 v" and MIN: "min_dist u v = d1+d2"
      shows "min_dist u w = d1" "min_dist w v = d2"
    proof -
      from min_dist_minD[OF \<open>dist u d1 w\<close>] have "min_dist u w \<le> d1" .
      moreover {
        have "dist u (min_dist u w) w"
          apply (rule min_dist_is_dist)
          using D1 by auto
        also note D2
        finally have "dist u (min_dist u w + d2) v" .
        moreover assume "min_dist u w < d1"
        moreover note MIN
        ultimately have False by (auto dest: min_dist_minD)
      } ultimately show "min_dist u w = d1"
        unfolding not_less[symmetric] using nat_neq_iff by blast

      from min_dist_minD[OF \<open>dist w d2 v\<close>] have "min_dist w v \<le> d2" .
      moreover {
        note D1
        also have "dist w (min_dist w v) v"
          apply (rule min_dist_is_dist)
          using D2 by auto
        finally have "dist u (d1 + min_dist w v) v" .
        moreover assume "min_dist w v < d2"
        moreover note MIN
        ultimately have False by (auto dest: min_dist_minD)
      } ultimately show "min_dist w v = d2"
        unfolding not_less[symmetric] using nat_neq_iff by blast
    qed    

    subsubsection \<open>Shortest Paths\<close>

    (*definition isShortestPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
      -- \<open>A shortest path between two nodes\<close> (* TODO: Rename: isShortestPath *)
      where  
      "isShortestPath u p v \<equiv> isPath u p v \<and> (\<forall>p'. isPath u p' v \<longrightarrow> length p \<le> length p')"
    *)  


    -- \<open>Characterization of shortest path in terms of minimum distance\<close>
    lemma isShortestPath_min_dist_def: "isShortestPath u p v \<longleftrightarrow> isPath u p v \<and> length p = min_dist u v"  
      unfolding isShortestPath_def min_dist_def dist_def
      apply (rule iffI; clarsimp)
      apply (rule Least_equality[symmetric]; auto; fail)
      apply (rule Least_le; auto; fail)
      done      

    lemma obtain_shortest_path: 
      assumes CONN: "connected u v"  
      obtains p where "isShortestPath u p v"
      using min_dist_is_dist[OF CONN]
      unfolding dist_def isShortestPath_min_dist_def
      by blast

    lemma isShortestPath_is_simple:
      assumes "isShortestPath s p t"
      shows "isSimplePath s p t"
    proof (rule ccontr)
      from assms have PATH: "isPath s p t" 
        and SHORTEST: "\<forall>p'. isPath s p' t \<longrightarrow> length p \<le> length p'"
        by (auto simp: isShortestPath_def)

      assume "\<not>isSimplePath s p t"  
      with PATH have "\<not>distinct (pathVertices s p)" by (auto simp: isSimplePath_def)

      then obtain pv1 u pv2 pv3 where PV: "pathVertices s p = pv1@u#pv2@u#pv3" 
        by (auto dest: not_distinct_decomp)
      from split_path_at_vertex[OF PATH PV] obtain p1 p23 where
        [simp]: "p=p1@p23" and 
          P1: "isPath s p1 u" "pathVertices s p1 = pv1@[u]" and
          P23: "isPath u p23 t" "pathVertices u p23 = (u#pv2)@u#pv3"
          by auto
          
      from split_path_at_vertex[OF P23] obtain p2 p3 where
        [simp]: "p23 = p2@p3" and
        P2: "isPath u p2 u" "pathVertices u p2 = u#pv2@[u]" and
        P3: "isPath u p3 t" "pathVertices u p3 = u#pv3"
        by auto

      from P1(1) P3(1) have SHORTER_PATH: "isPath s (p1@p3) t" by (auto simp: isPath_append)
      
      from P2 have "p2\<noteq>[]" by auto
      hence LESS: "length (p1@p3) < length p" by auto
      with SHORTER_PATH SHORTEST show False by auto
    qed    

    text \<open>We provide yet another characterization of shortest paths:\<close>
    lemma isShortestPath_alt: "isShortestPath u p v \<longleftrightarrow> isSimplePath u p v \<and> length p = min_dist u v"
      using isShortestPath_is_simple isShortestPath_min_dist_def
      unfolding isSimplePath_def by auto

      
    text \<open>In a finite graph, the length of a shortest path is less 
      than the number of nodes\<close>  
    lemma isShortestPath_length_less_V:   
      assumes FIN: "finite V" and SV: "s\<in>V"
      assumes PATH: "isShortestPath s p t"
      shows "length p < card V"
      using simplePath_length_less_V[OF FIN SV]
      using isShortestPath_is_simple[OF PATH] .

    corollary min_dist_less_V:
      assumes FIN: "finite V"
      assumes SV: "s\<in>V"
      assumes CONN: "connected s t"
      shows "min_dist s t < card V"
      apply (rule obtain_shortest_path[OF CONN])
      apply (frule isShortestPath_length_less_V[OF FIN SV])
      unfolding isShortestPath_min_dist_def by auto

    lemma split_shortest_path: "isShortestPath u (p1@p2) v 
      \<Longrightarrow> (\<exists>w. isShortestPath u p1 w \<and> isShortestPath w p2 v)"
      apply (auto simp: isShortestPath_min_dist_def isPath_append)
      apply (rule exI; intro conjI; assumption?)
      apply (drule isPath_distD)+ using min_dist_split apply auto []
      apply (drule isPath_distD)+ using min_dist_split apply auto []
      done

    text \<open>Edges in a shortest path connect nodes with increasing 
      minimum distance from the source\<close>
    lemma isShortestPath_level_edge:  
      assumes SP: "isShortestPath s p t" 
      assumes EIP: "(u,v)\<in>set p"
      shows 
        "connected s u" "connected u v" "connected v t" and
        "min_dist s v = min_dist s u + 1" (is ?G1) and
        "min_dist u t = 1 + min_dist v t" (is ?G2) and
        "min_dist s t = min_dist s u + 1 + min_dist v t" (is ?G3) 
    proof -  
      -- \<open>Split the original path at the edge\<close>
      from EIP obtain p1 p2 where [simp]: "p=p1@(u,v)#p2"
        by (auto simp: in_set_conv_decomp)
      from \<open>isShortestPath s p t\<close> have 
        MIN: "min_dist s t = length p" and P: "isPath s p t" and DV: "distinct (pathVertices s p)"
        by (auto simp: isShortestPath_alt isSimplePath_def)
      from P have DISTS: "dist s (length p1) u" "dist u 1 v" "dist v (length p2) t"
        by (auto simp: isPath_append dist_def intro: exI[where x="[(u,v)]"])
        
      from DISTS show "connected s u" "connected u v" "connected v t" by auto

      -- \<open>Express the minimum distances in terms of the split original path\<close>  
      from MIN have MIN': "min_dist s t = length p1 + 1 + length p2" by auto
      
      from min_dist_split[OF dist_trans[OF DISTS(1,2)] DISTS(3) MIN'] have
        MDSV: "min_dist s v = length p1 + 1" and [simp]: "length p2 = min_dist v t" by simp_all
      from min_dist_split[OF DISTS(1) dist_trans[OF DISTS(2,3)]] MIN' have
        MDUT: "min_dist u t = 1 + length p2" and [simp]: "length p1 = min_dist s u" by simp_all

      from MDSV MDUT MIN' show ?G1 ?G2 ?G3 by auto  
    qed  

  end    

end
