section \<open>Edmonds-Karp Algorithm\<close>
theory EdmondsKarp_Algo
imports FordFulkerson_Algo Temporary_Graph_Add "~~/src/HOL/Library/Rewrite"
begin

  subsection \<open>Algorithm\<close>
  text \<open>
    In this theory, we formalize an abstract version of
    Edmonds-Karp algorithm, which we obtain by refining the 
    Ford-Fulkerson algorithm to always use shortest augmenting paths.
  \<close>

  context Network 
  begin

    text \<open>First, we specify the refined procedure for finding augmenting paths\<close>
    definition "find_shortest_augmenting_spec f \<equiv> ASSERT (NFlow c s t f) \<guillemotright> 
      SPEC (\<lambda> Some p \<Rightarrow> Graph.shortestPath (residualGraph f) s p t
            | None \<Rightarrow> \<forall>p. \<not>NFlow.isAugmenting c s t f p)"

    text \<open>Note, if there is an augmenting path, there is always a shortest one\<close>
    lemma (in NFlow) augmenting_path_imp_shortest: 
      "isAugmenting p \<Longrightarrow> \<exists>p. Graph.shortestPath cf s p t"
      using Graph.obtain_shortest_path unfolding isAugmenting_def
      by (fastforce simp: Graph.isSimplePath_def Graph.isReachable_def)

    lemma (in NFlow) shortest_is_augmenting: 
      "Graph.shortestPath cf s p t \<Longrightarrow> isAugmenting p"
      unfolding isAugmenting_def using Graph.shortestPath_is_simple
      by (fastforce)

    text \<open>We show that our refined procedure is actually a refinement\<close>  
    lemma find_shortest_augmenting_refine[refine]: 
      "(f',f)\<in>Id \<Longrightarrow> find_shortest_augmenting_spec f' \<le> \<Down>Id (find_augmenting_spec f)"  
      unfolding find_shortest_augmenting_spec_def find_augmenting_spec_def
      apply (refine_vcg)
      using NFlow.augmenting_path_imp_shortest NFlow.shortest_is_augmenting
      by (auto split: option.split)

    text \<open>Next, we specify the Edmonds-Karp algorithm\<close>  
    definition "edka \<equiv> do {
      let f = (\<lambda>_. 0);

      (f,_) \<leftarrow> WHILEIT fofu_invar
        (\<lambda>(f,brk). \<not>brk) 
        (\<lambda>(f,_). do {
          p \<leftarrow> find_shortest_augmenting_spec f;
          case p of 
            None \<Rightarrow> RETURN (f,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (NFlow.isAugmenting c s t f p);
              ASSERT (Graph.shortestPath (residualGraph f) s p t);
              let f' = NFlow.augmentingFlow c f p;
              let f = NFlow.augment c f f';
              ASSERT (NFlow c s t f);
              RETURN (f, False)
            }  
        })
        (f,False);
      ASSERT (NFlow c s t f);
      RETURN f 
    }"

    lemma edka_refine[refine]: "edka \<le> \<Down>Id fofu"
      unfolding edka_def fofu_def
      apply (refine_rcg bind_refine')
      apply (refine_dref_type)
      apply (vc_solve simp: find_shortest_augmenting_spec_def)
      done


  end

  subsection \<open>Complexity Analysis\<close>
  text \<open>
    In this section, we show that the loop iterations of the Edmonds-Karp algorithm
    are bounded by $O(|V||E|)$.

    The basic idea of the proof is, that a path that
    takes an edge reverse to an edge on some shortest path 
    cannot be a shortest path itself.

    As augmentation flips at least one edge, this yields a termination argument:
      After augmentation, either the minimum distance between source and target
      increases, or it remains the same, but the number of edges that lay on a
      shortest path decreases. As the minimum distance is bounded by $|V|$, 
      we get termination within $O(|V||E|)$ loop iterations.
  \<close>

  context Graph begin

    text \<open>
      The basic idea is expressed in the following lemma, which, however, 
      is not general enough to be applied for the correctness proof, where
      we flip more than one edge simultaneously.
      \<close>
    lemma shortestPath_flip_edge:
      assumes "shortestPath s p t" "(u,v)\<in>set p"
      assumes "isPath s p' t" "(v,u)\<in>set p'"
      shows "length p' \<ge> length p + 2"
      using assms
    proof -
      from \<open>shortestPath s p t\<close> have 
        MIN: "min_dist s t = length p" and P: "isPath s p t" and DV: "distinct (pathVertices s p)"
        by (auto simp: shortestPath_alt isSimplePath_def)
        
      from \<open>(u,v)\<in>set p\<close> obtain p1 p2 where [simp]: "p=p1@(u,v)#p2"
        by (auto simp: in_set_conv_decomp)
        
      from P DV have [simp]: "u\<noteq>v"
        by (cases p2) (auto simp add: isPath_append pathVertices_append)

      from P have DISTS: "dist s (length p1) u" "dist u 1 v" "dist v (length p2) t"
        by (auto simp: isPath_append dist_def intro: exI[where x="[(u,v)]"])

      from MIN have MIN': "min_dist s t = length p1 + 1 + length p2" by auto

      from min_dist_split[OF dist_trans[OF DISTS(1,2)] DISTS(3) MIN'] have
        MDSV: "min_dist s v = length p1 + 1" by simp
        
      from min_dist_split[OF DISTS(1) dist_trans[OF DISTS(2,3)]] MIN' have
        MDUT: "min_dist u t = 1 + length p2" by simp

      from \<open>(v,u)\<in>set p'\<close> obtain p1' p2' where [simp]: "p'=p1'@(v,u)#p2'"
        by (auto simp: in_set_conv_decomp)

      from \<open>isPath s p' t\<close> have DISTS': "dist s (length p1') v" "dist v 1 u" "dist u (length p2') t"
        by (auto simp: isPath_append dist_def intro: exI[where x="[(v,u)]"])
      
      from DISTS'(1,3)[THEN min_dist_minD, unfolded MDSV MDUT] show
        "length p + 2 \<le> length p'" by auto
    qed    


    text \<open>
      To be used for the analysis of augmentation, we have to generalize the 
      lemma to simultaneous flipping of edges:
      \<close> 
    lemma shortestPath_flip_edges:
      assumes "Graph.E c' \<supseteq> E - edges" "Graph.E c' \<subseteq> E \<union> (prod.swap`edges)"
      assumes SP: "shortestPath s p t" and EDGES_SS: "edges \<subseteq> set p"
      assumes P': "Graph.isPath c' s p' t" "prod.swap`edges \<inter> set p' \<noteq> {}"
      shows "length p + 2 \<le> length p'"
    proof -
      interpret g'!: Graph c' .

      (* TODO: The proof still contains some redundancy: A first flipped edge
        is searched in both, the induction, and the initialization *)
      {
        fix u v p1 p2'
        assume "(u,v)\<in>edges"
           and "isPath s p1 v" and "g'.isPath u p2' t"
        hence "min_dist s t < length p1 + length p2'"   
        proof (induction p2' arbitrary: u v p1 rule: length_induct)
          case (1 p2')
          note IH = "1.IH"[rule_format]
          note P1 = \<open>isPath s p1 v\<close>
          note P2' = \<open>g'.isPath u p2' t\<close>

          have "length p1 > min_dist s u"
          proof -
            from P1 have "length p1 \<ge> min_dist s v"
              using min_dist_minD by (auto simp: dist_def)
            moreover from \<open>(u,v)\<in>edges\<close> EDGES_SS have "min_dist s v = Suc (min_dist s u)"
              using shortestPath_level_edge[OF SP] by auto
            ultimately show ?thesis by auto
          qed  

          from shortestPath_level_edge[OF SP] \<open>(u,v)\<in>edges\<close> EDGES_SS 
          have 
                "min_dist s t = min_dist s u + min_dist u t" 
            and "conn s u"
          by auto

          show ?case
          proof (cases "prod.swap`edges \<inter> set p2' = {}")
            -- \<open>We proceed by a case distinction whether the suffix path contains swapped edges\<close>
            case True 
            with g'.transfer_path[OF _ P2', of c] \<open>g'.E \<subseteq> E \<union> prod.swap ` edges\<close>
            have "isPath u p2' t" by auto
            hence "length p2' \<ge> min_dist u t" using min_dist_minD
              by (auto simp: dist_def)
            moreover note \<open>length p1 > min_dist s u\<close>
            moreover note \<open>min_dist s t = min_dist s u + min_dist u t\<close>
            ultimately show ?thesis by auto
          next
            case False
            -- \<open>Obtain first swapped edge on suffix path\<close>
            obtain p21' e' p22' where [simp]: "p2'=p21'@e'#p22'"
                and E_IN_EDGES: "e'\<in>prod.swap`edges" and P1_NO_EDGES: "prod.swap`edges \<inter> set p21' = {}"
              apply (rule split_list_first_propE[of p2' "\<lambda>e. e\<in>prod.swap`edges"])
              using \<open>prod.swap ` edges \<inter> set p2' \<noteq> {}\<close> apply auto []
              apply (rprems, assumption)
              apply auto
              done
            obtain u' v' where [simp]: "e'=(v',u')" by (cases e')      
      
            -- \<open>Split the suffix path accordingly\<close>
            from P2' have P21': "g'.isPath u p21' v'" and P22': "g'.isPath u' p22' t"
              by (auto simp: g'.isPath_append)
            -- \<open>As we chose the first edge, the prefix of the suffix path is also a path in the original graph\<close>  
            from g'.transfer_path[OF _ P21', of c] \<open>g'.E \<subseteq> E \<union> prod.swap ` edges\<close> P1_NO_EDGES
            have P21: "isPath u p21' v'" by auto
            from min_dist_is_dist[OF \<open>conn s u\<close>] 
            obtain psu where PSU: "isPath s psu u" and LEN_PSU: "length psu = min_dist s u" by (auto simp: dist_def)
            from PSU P21 have P1n: "isPath s (psu@p21') v'" by (auto simp: isPath_append)
            from IH[OF _ _ P1n P22'] E_IN_EDGES have "min_dist s t < length psu + length p21' + length p22'" by auto
            moreover note \<open>length p1 > min_dist s u\<close>
            ultimately show ?thesis by (auto simp: LEN_PSU)
          qed
        qed  
      } note aux=this

      (* TODO: This step is analogous to what we do in the False-case of the induction.
        Can we somehow remove the redundancy? *)
      -- \<open>Obtain first swapped edge on path\<close>
      obtain p1' e p2' where [simp]: "p'=p1'@e#p2'"
          and E_IN_EDGES: "e\<in>prod.swap`edges" and P1_NO_EDGES: "prod.swap`edges \<inter> set p1' = {}"
        apply (rule split_list_first_propE[of p' "\<lambda>e. e\<in>prod.swap`edges"])
        using \<open>prod.swap ` edges \<inter> set p' \<noteq> {}\<close> apply auto []
        apply (rprems, assumption)
        apply auto
        done
      obtain u v where [simp]: "e=(v,u)" by (cases e)      

      -- \<open>Split the new path accordingly\<close>
      from \<open>g'.isPath s p' t\<close> have P1': "g'.isPath s p1' v" and P2': "g'.isPath u p2' t"
        by (auto simp: g'.isPath_append)
      -- \<open>As we chose the first edge, the prefix of the path is also a path in the original graph\<close>  
      from g'.transfer_path[OF _ P1', of c] \<open>g'.E \<subseteq> E \<union> prod.swap ` edges\<close> P1_NO_EDGES
      have P1: "isPath s p1' v" by auto
      
      from aux[OF _ P1 P2'] E_IN_EDGES have "min_dist s t < length p1' + length p2'"
        by auto
      thus ?thesis using SP 
        by (auto simp: shortestPath_min_dist_def)
    qed    
  end    


  text \<open>We outsource the more specific lemmas to its own locale, 
    to prevent name space pollution\<close>
  locale ek_analysis_defs = Graph +
    fixes s t :: node

  locale ek_analysis = ek_analysis_defs + Finite_Graph
  begin
    definition (in ek_analysis_defs) "spEdges \<equiv> {e. \<exists>p. e\<in>set p \<and> shortestPath s p t}"

    lemma spEdges_ss_E: "spEdges \<subseteq> E"
      using isPath_edgeset unfolding spEdges_def shortestPath_def by auto

    lemma finite_spEdges[simp, intro]: "finite (spEdges)"  
      using finite_subset[OF spEdges_ss_E] 
      by blast

    definition (in ek_analysis_defs) "uE \<equiv> E \<union> E\<inverse>"

    lemma finite_uE[simp,intro]: "finite uE"
      by (auto simp: uE_def)

    lemma E_ss_uE: "E\<subseteq>uE"  
      by (auto simp: uE_def)

    lemma card_spEdges_le:
      shows "card spEdges \<le> card uE"
      apply (rule card_mono)
      apply (auto simp: order_trans[OF spEdges_ss_E E_ss_uE])
      done

    lemma card_spEdges_less:
      shows "card spEdges < card uE + 1"
      using card_spEdges_le[OF assms] 
      by auto
      
    
    definition (in ek_analysis_defs) "ekMeasure \<equiv> 
      if (conn s t) then
        (card V - min_dist s t) * (card uE + 1) + (card (spEdges))
      else 0"

    lemma measure_decr:
      assumes SV: "s\<in>V"
      assumes SP: "shortestPath s p t"
      assumes SP_EDGES: "edges\<subseteq>set p"
      assumes Ebounds: "Graph.E c' \<supseteq> E - edges \<union> prod.swap`edges" "Graph.E c' \<subseteq> E \<union> prod.swap`edges"
      shows "ek_analysis_defs.ekMeasure c' s t \<le> ekMeasure"
        and "edges - Graph.E c' \<noteq> {} \<Longrightarrow> ek_analysis_defs.ekMeasure c' s t < ekMeasure"
    proof -
      interpret g'!: ek_analysis_defs c' s t .

      interpret g'!: ek_analysis c' s t
        apply intro_locales
        apply (rule g'.Finite_Graph_EI)
        using finite_subset[OF Ebounds(2)] finite_subset[OF SP_EDGES]
        by auto
      
      from SP_EDGES SP have "edges \<subseteq> E" 
        by (auto simp: spEdges_def shortestPath_def dest: isPath_edgeset)
      with Ebounds have Veq[simp]: "Graph.V c' = V"
        by (force simp: Graph.V_def)

      from Ebounds \<open>edges \<subseteq> E\<close> have uE_eq[simp]: "g'.uE = uE"  
        by (force simp: ek_analysis_defs.uE_def)

      from SP have LENP: "length p = min_dist s t" by (auto simp: shortestPath_min_dist_def) 

      from SP have CONN: "conn s t" by (auto simp: shortestPath_def isReachable_def)

      {
        assume NCONN2: "\<not>g'.conn s t"
        hence "s\<noteq>t" by auto
        with CONN NCONN2 have "g'.ekMeasure < ekMeasure"
          unfolding g'.ekMeasure_def ekMeasure_def
          using min_dist_less_V[OF finite_V SV] (* TODO: Move this result to finite-graph! *)
          by auto
      } moreover {
        assume SHORTER: "g'.min_dist s t < min_dist s t"
        assume CONN2: "g'.conn s t"

        -- \<open>Obtain a shorter path in $g'$\<close>
        from g'.min_dist_is_dist[OF CONN2] obtain p' where
          P': "g'.isPath s p' t" and LENP': "length p' = g'.min_dist s t"
          by (auto simp: g'.dist_def)

        { -- \<open>Case: It does not use @{term "prod.swap`edges"}. 
            Then it is also a path in $g$, which is shorter than 
            the shortest path in $g$, yielding a contradiction.\<close>
          assume "prod.swap`edges \<inter> set p' = {}"
          with g'.transfer_path[OF _ P', of c] Ebounds have "dist s (length p') t"
            by (auto simp: dist_def)
          from LENP' SHORTER min_dist_minD[OF this] have False by auto 
        } moreover {
          -- \<open>So assume the path uses the edge @{term "prod.swap e"}.\<close>
          assume "prod.swap`edges \<inter> set p' \<noteq> {}"
          -- \<open>Due to auxiliary lemma, those path must be longer\<close>
          from shortestPath_flip_edges[OF _ _ SP SP_EDGES P' this] Ebounds
          have "length p' > length p" by auto
          with SHORTER LENP LENP' have False by auto
        } ultimately have False by auto
      } moreover {
        assume LONGER: "g'.min_dist s t > min_dist s t"
        assume CONN2: "g'.conn s t"
        have "g'.ekMeasure < ekMeasure"
          unfolding g'.ekMeasure_def ekMeasure_def
          apply (simp only: Veq uE_eq CONN CONN2 if_True)
          apply (rule mlex_fst_decrI)
          using card_spEdges_less g'.card_spEdges_less g'.min_dist_less_V[OF _ _ CONN2] SV
          using LONGER
          apply auto
          done
      } moreover {
        assume EQ: "g'.min_dist s t = min_dist s t"
        assume CONN2: "g'.conn s t"

        {
          fix p'
          assume P': "g'.shortestPath s p' t"
          have "prod.swap`edges \<inter> set p' = {}" 
          proof (rule ccontr) 
            assume EIP': "prod.swap`edges \<inter> set p' \<noteq> {}"
            from P' have P': "g'.isPath s p' t" and LENP': "length p' = g'.min_dist s t"
              by (auto simp: g'.shortestPath_min_dist_def)
            from shortestPath_flip_edges[OF _ _ SP SP_EDGES P' EIP'] Ebounds have "length p + 2 \<le> length p'" by auto
            with LENP LENP' EQ show False by auto
          qed  
          with g'.transfer_path[of p' c s t] P' Ebounds have "shortestPath s p' t"
            by (auto simp: Graph.shortestPath_min_dist_def EQ)
        } hence SS: "g'.spEdges \<subseteq> spEdges" by (auto simp: g'.spEdges_def spEdges_def)
            
        {
          assume "edges - Graph.E c' \<noteq> {}"
          with g'.spEdges_ss_E SS SP SP_EDGES have "g'.spEdges \<subset> spEdges"
            unfolding g'.spEdges_def spEdges_def by fastforce
          hence "g'.ekMeasure < ekMeasure"  
            unfolding g'.ekMeasure_def ekMeasure_def 
            apply (simp only: Veq uE_eq EQ CONN CONN2 if_True)
            apply (rule mlex_snd_decrI)
            apply (simp add: EQ)
            apply (rule psubset_card_mono)
            apply simp
            by simp
        } note G1 = this

        have G2: "g'.ekMeasure \<le> ekMeasure"
          unfolding g'.ekMeasure_def ekMeasure_def
          apply (simp only: Veq uE_eq CONN CONN2 if_True)
          apply (rule mlex_leI)
          apply (simp add: EQ)
          apply (rule card_mono)
          apply simp
          by fact
        note G1 G2  
      } ultimately show 
        "g'.ekMeasure \<le> ekMeasure" 
        "edges - Graph.E c' \<noteq> {} \<Longrightarrow> g'.ekMeasure < ekMeasure"
        using less_linear[of "g'.min_dist s t" "min_dist s t"]   
        apply -
        apply (fastforce)+
        done

    qed
  end  

  text \<open>As a first step to the analysis setup, we characterize
    the effect of augmentation on the residual graph
    \<close>
  context Graph
  begin
    definition "augment_cf edges cap \<equiv> \<lambda>e. 
      if e\<in>edges then c e - cap 
      else if prod.swap e\<in>edges then c e + cap
      else c e"
    
    lemma augment_cf_empty[simp]: "augment_cf {} cap = c" 
      by (auto simp: augment_cf_def)
  
    lemma augment_cf_ss_V: "\<lbrakk>edges \<subseteq> E\<rbrakk> \<Longrightarrow> Graph.V (augment_cf edges cap) \<subseteq> V"  
      by (auto simp add: augment_cf_def Graph.V_def Graph.E_def) []
      
    lemma augment_saturate:
      fixes edges e
      defines "c' \<equiv> augment_cf edges (c e)"
      assumes EIE: "e\<in>edges"
      shows "e\<notin>Graph.E c'"
      using EIE unfolding c'_def augment_cf_def
      by (auto simp: Graph.E_def)
      

    lemma augment_cf_split: 
      assumes "edges1 \<inter> edges2 = {}" "edges1\<inverse> \<inter> edges2 = {}"
      shows "Graph.augment_cf c (edges1 \<union> edges2) cap 
        = Graph.augment_cf (Graph.augment_cf c edges1 cap) edges2 cap"  
      using assms
      by (fastforce simp: Graph.augment_cf_def intro!: ext)
      
    (*lemma (in Graph) augment_singleton_bounds:
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
    *)  
  end

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
  
    theorem shortest_path_decr_ek_measure:
      fixes p
      assumes SP: "Graph.shortestPath cf s p t"
      defines "f' \<equiv> augment (augmentingFlow p)"
      defines "cf' \<equiv> residualGraph f'"
      shows "ek_analysis_defs.ekMeasure cf' s t < ek_analysis_defs.ekMeasure cf s t"
    proof -
      interpret cf!: ek_analysis cf 
        apply unfold_locales
        by (auto simp: resV_netV finite_V)

      interpret cf'!: ek_analysis_defs cf' .
  
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

  context Network begin
    lemma ekMeasure_upper_bound: 
      (* TODO: #edgesSp even bound by |E|, as either e or swap e lays on shortest path! *)
      "ek_analysis_defs.ekMeasure (residualGraph (\<lambda>_. 0)) s t < 2 * card V * card E + card V"
    proof -  
      interpret NFlow c s t "(\<lambda>_. 0)"
        unfolding NFlow_def Flow_def using Network_axioms by (auto simp: s_node t_node)

      interpret ek!: ek_analysis cf  
        apply unfold_locales
        apply (auto simp: resV_netV finite_V)
        done

      have cardV_positive: "card V > 0" and cardE_positive: "card E > 0"
        using card_0_eq finite_V apply blast
        using V_def card_0_eq finite_E by blast

      show ?thesis proof (cases "ek.conn s t")  
        case False hence "ek.ekMeasure = 0" by (auto simp: ek.ekMeasure_def)
        with cardV_positive cardE_positive show ?thesis
          by auto
      next
        case True 

        have "ek.min_dist s t > 0"
          apply (rule ccontr)
          apply (auto simp: Graph.min_dist_z_iff True s_not_t[symmetric])
          done

        have "cf = c"  
          unfolding residualGraph_def by (auto intro!: ext simp: E_def)
        hence "ek.uE = E\<union>E\<inverse>" unfolding ek.uE_def by simp

        from True have "ek.ekMeasure = (card ek.V - ek.min_dist s t) * (card ek.uE + 1) + (card (ek.spEdges))"
          unfolding ek.ekMeasure_def by simp
        also from mlex_bound[of "card ek.V - ek.min_dist s t" "card V", OF _ ek.card_spEdges_less]
        have "\<dots> < card V * (card ek.uE+1)" 
          using \<open>ek.min_dist s t > 0\<close> \<open>card V > 0\<close>
          by (auto simp: resV_netV)
        also have "card ek.uE \<le> 2*card E" unfolding \<open>ek.uE = E\<union>E\<inverse>\<close> 
          apply (rule order_trans)
          apply (rule card_Un_le)
          by auto
        finally show ?thesis by (auto simp: algebra_simps)
      qed  
    qed  

    definition "edkac_rel \<equiv> {((f,brk,itc), (f,brk)) | f brk itc.
      itc + ek_analysis_defs.ekMeasure (residualGraph f) s t < 2 * card V * card E + card V
    }"

    context begin interpretation Refine_Monadic_Syntax .
  
      text \<open>Finally, we present a version of the Edmonds-Karp algorithm 
        which is instrumented with a loop counter, and asserts that
        there are less than $2|V||E|+|V| = O(|V||E|)$ iterations.

        Note that we only count the non-breaking loop iterations.
        \<close>
      definition "edka_complexity \<equiv> do {
        let f = (\<lambda>_. 0);
  
        (f,_,itc) \<leftarrow> while\<^sub>T 
          (\<lambda>(f,brk,_). \<not>brk) 
          (\<lambda>(f,_,itc). do {
            p \<leftarrow> find_shortest_augmenting_spec f;
            case p of 
              None \<Rightarrow> return (f,True,itc)
            | Some p \<Rightarrow> do {
                let f' = NFlow.augmentingFlow c f p;
                let f = NFlow.augment c f f';
                return (f, False,itc + 1)
              }  
          })
          (f,False,0);
        assert (itc < 2 * card V * card E + card V);
        return f 
      }"
  
      lemma edka_complexity_refine: "edka_complexity \<le> \<Down>Id edka"
      proof -
        have [refine_dref_RELATES]: 
          "RELATES edkac_rel"
          by (auto simp: RELATES_def)
  
        show ?thesis  
          unfolding edka_complexity_def edka_def
          apply (refine_rcg)
          apply (refine_dref_type)
          apply (vc_solve simp: edkac_rel_def)
          using ekMeasure_upper_bound apply auto []
          apply auto []
          apply (drule (1) NFlow.shortest_path_decr_ek_measure; auto)
          done
      qed    

      text \<open>We show that this algorithm never fails, and computes a maximum flow.\<close>
      theorem "edka_complexity \<le> (spec f. isMaxFlow c s t f)"
      proof -  
        note edka_complexity_refine
        also note edka_refine
        also note fofu_total_correct
        finally show ?thesis .
      qed  
    end  

  end


end

