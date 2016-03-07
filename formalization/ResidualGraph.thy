theory ResidualGraph
imports Network
begin
  text \<open>
    In this theory, we define the residual graph, and the concepts of 
    augmenting path, residual capacity, and residual flow.
    \<close>

  (* Residual graph definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  definition residualGraph :: "_ graph \<Rightarrow> _ flow \<Rightarrow> _ graph"
  where "residualGraph c f \<equiv> \<lambda>(u, v).
    if (u, v) \<in> Graph.E c then
      c (u, v) - f (u, v)
    else if (v, u) \<in> Graph.E c then
      f (v, u)
    else
      0"


  notation (in Graph_Syntax) residualGraph ("\<langle>\<C>\<^sub>\<f>/ _,/ _\<rangle>" 1000)


  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Augmenting flow definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    abbreviation "cf \<equiv> residualGraph c f"
    sublocale cf!: Graph cf .
    lemmas cf_def = residualGraph_def[of c f]
    
    definition isAugmenting :: "path \<Rightarrow> bool"
    where "isAugmenting p \<equiv> cf.isSimplePath s p t"
      
    definition bottleNeck :: "path \<Rightarrow> 'capacity"  (* TODO: Rename to residualCapacity*)
    where "bottleNeck p \<equiv> Min {cf e | e. e \<in> set p}"

    lemma bottleNeck_alt: "bottleNeck p = Min (cf`set p)"  
      -- \<open>Useful characterization for finiteness arguments\<close>
      unfolding bottleNeck_def apply (rule arg_cong[where f=Min]) by auto

      
    definition augmentingFlow :: "path \<Rightarrow> 'capacity flow"
    where "augmentingFlow p \<equiv> \<lambda>(u, v).
      if (u, v) \<in> (set p) then
        bottleNeck p
      else
        0"
  end

  locale NFlow_Loc_Syntax = Graph_Loc_Syntax + NFlow begin
    notation isAugmenting ("\<langle>\<Rightarrow>\<^sup>A/ _\<rangle>" 1000)
    notation bottleNeck ("\<langle>\<nabla>/ _\<rangle>" 1000)
    notation augmentingFlow ("\<langle>\<F>\<^sub>\<p>/ _\<rangle>" 1000)
  end

  context Graph_Syntax begin  
    abbreviation NFlow_isAugmenting :: "_ graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> _ flow \<Rightarrow> path \<Rightarrow> bool"
      ("\<lbrace>_,/ _,/ _,/ _/ \<parallel>\<^sub>N\<^sub>F/ \<langle>\<Rightarrow>\<^sup>A/ _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c, s, t, f \<parallel>\<^sub>N\<^sub>F \<langle>\<Rightarrow>\<^sup>A p\<rangle>\<rbrace> \<equiv> NFlow.isAugmenting c s t f p"
    
    abbreviation NFlow_bottleNeck :: "_ graph \<Rightarrow> _ flow \<Rightarrow> path \<Rightarrow> _"
      ("\<lbrace>_,/ _/ \<parallel>\<^sub>N\<^sub>F/ \<langle>\<nabla>/ _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c, f \<parallel>\<^sub>N\<^sub>F \<langle>\<nabla> p\<rangle>\<rbrace> \<equiv> NFlow.bottleNeck c f p"
    
    abbreviation NFlow_augmentingFlow :: "_ graph \<Rightarrow> _ flow \<Rightarrow> path \<Rightarrow> _ flow"
      ("\<lbrace>_,/ _/ \<parallel>\<^sub>N\<^sub>F/ \<langle>\<F>\<^sub>\<p>/ _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c, f \<parallel>\<^sub>N\<^sub>F \<langle>\<F>\<^sub>\<p> p\<rangle>\<rbrace> \<equiv> NFlow.augmentingFlow c f p"
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)  
  
  
  
  
  (* Residual graph lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin

    lemma (in NFlow) cfE_ss_invE: "Graph.E cf \<subseteq> E \<union> E\<inverse>"
      unfolding residualGraph_def Graph.E_def
      by auto


    lemma resV_netV[simp] : "cf.V = V"
      -- \<open>The nodes of the residual graph are exactly the nodes of the network.\<close>
      proof
        show "V \<subseteq> Graph.V cf" unfolding Graph.V_def
          proof 
            fix u
            assume "u \<in> {u. \<exists>v. (u, v) \<in> E \<or> (v, u) \<in> E}"
            then obtain v where "(u, v) \<in> E \<or> (v, u) \<in> E" by auto
            then show "u \<in> {u. \<exists>v. (u, v) \<in> Graph.E cf \<or> (v, u) \<in> Graph.E cf}"
              proof
                assume "(u, v) \<in> E"
                then have "(u, v) \<in> Graph.E cf \<or> (v, u) \<in> Graph.E cf"
                  proof (cases "f (u, v) = 0")
                    case True
                      then have "cf (u, v) = c (u, v)"
                        unfolding residualGraph_def using `(u, v) \<in> E` by (auto simp:)
                      then have "cf (u, v) \<noteq> 0" using `(u, v) \<in> E` unfolding E_def by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  next
                    case False 
                      then have "cf (v, u) = f (u, v)" unfolding residualGraph_def
                        using `(u, v) \<in> E` no_parallel_edge by auto
                      then have "cf (v, u) \<noteq> 0" using False by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  qed
                thus ?thesis by auto
              next
                assume "(v, u) \<in> E"
                then have "(v, u) \<in> Graph.E cf \<or> (u, v) \<in> Graph.E cf"
                  proof (cases "f (v, u) = 0")
                    case True
                      then have "cf (v, u) = c (v, u)"
                        unfolding residualGraph_def using `(v, u) \<in> E` by (auto)
                      then have "cf (v, u) \<noteq> 0" using `(v, u) \<in> E` unfolding E_def by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  next
                    case False 
                      then have "cf (u, v) = f (v, u)" unfolding residualGraph_def
                        using `(v, u) \<in> E` no_parallel_edge by auto
                      then have "cf (u, v) \<noteq> 0" using False by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  qed
                thus ?thesis by auto
              qed
         qed     
      next
        show "Graph.V cf \<subseteq> V" unfolding Graph.V_def Graph.E_def residualGraph_def by auto
      qed
      
    lemma resE_nonNegative: "cf e \<ge> 0"
      -- \<open>The capacity matrix entries of the residual graph are non-negative\<close>
      proof -
        obtain u v where obt: "e = (u, v)" by (metis nat_gcd.cases)
        have "((u, v) \<in> E \<or> (v, u) \<in> E) \<or> ((u, v) \<notin> E \<and> (v, u) \<notin> E)" by blast
        thus ?thesis
          proof
            assume "(u, v) \<in> E \<or> (v, u) \<in> E"
              thus ?thesis
              proof
                assume "(u, v) \<in> E"
                then have "cf e = c e - f e" using cf_def obt by auto
                thus ?thesis using capacity_const cap_positive obt by (metis diff_0_right
                  diff_eq_diff_less_eq eq_iff eq_iff_diff_eq_0 linear)
              next
                assume "(v, u) \<in> E"
                then have "cf e = f (v, u)" using cf_def no_parallel_edge obt by auto
                thus ?thesis using obt capacity_const using le_less by fastforce 
              qed
          next
            assume "(u, v) \<notin> E \<and> (v, u) \<notin> E"
              thus ?thesis unfolding residualGraph_def using obt by simp
          qed
      qed
    
    lemma resE_positive: "e \<in> cf.E \<Longrightarrow> cf e > 0"
      -- \<open>Thus, all actual edges are labeled with positive values\<close>
      proof -
        assume asm: "e \<in> cf.E"
        have "cf e \<noteq> 0" using asm unfolding cf.E_def by auto
        thus ?thesis using resE_nonNegative by (meson eq_iff not_le)
      qed 
      
    (* TODO: Only one usage: Move or remove! *)  
    lemma reverse_flow: "Flow cf s t f' \<Longrightarrow> \<forall>(u, v) \<in> E. f' (v, u) \<le> f (u, v)"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix u v
          assume "(u, v) \<in> E"
          
          then have "cf (v, u) = f (u, v)"
            unfolding residualGraph_def using no_parallel_edge by auto
          moreover have "f' (v, u) \<le> cf (v, u)" using asm[unfolded Flow_def] by auto
          ultimately have "f' (v, u) \<le> f (u, v)" by metis
        }
        thus ?thesis by auto
      qed  


  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Augmenting flow lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    lemma bottleNeck_gzero': "cf.isPath s p t \<Longrightarrow> 0<bottleNeck p"
    proof -
      assume PATH: "cf.isPath s p t"
      hence "set p\<noteq>{}" using s_not_t by (auto)
      moreover have "\<forall>e\<in>set p. cf e > 0"
        using cf.isPath_edgeset[OF PATH] resE_positive by (auto)
      ultimately show ?thesis unfolding bottleNeck_alt by (auto)
    qed 

    lemma bottleNeck_gzero: "isAugmenting p \<Longrightarrow> 0<bottleNeck p"
      using bottleNeck_gzero'[of p] by (auto simp: isAugmenting_def cf.isSimplePath_def)

    lemma setsum_augmenting_alt:
      assumes "finite A"          
      shows "(\<Sum>e \<in> A. (augmentingFlow p) e) = bottleNeck p * of_nat (card (A\<inter>set p))"
    proof -
      have "(\<Sum>e \<in> A. (augmentingFlow p) e) = setsum (\<lambda>_. bottleNeck p) (A\<inter>set p)"
        apply (subst setsum.inter_restrict)
        apply (auto simp: augmentingFlow_def assms)
        done
      thus ?thesis by auto
    qed  

    (* TODO: Lemma to analyze how incoming and outgoing edges of a node look in a simple path.
      This can then be used to easily prove the next two lemmas!
    *)
    lemma (in Graph) adjacent_edges_not_on_path:
      assumes PATH: "isPath s p t"
      assumes VNV: "v\<notin>set (pathVertices_fwd s p)"
      shows "incoming v \<inter> set p = {}" "outgoing v \<inter> set p = {}"
    proof -
      from VNV have "\<forall>u. (u,v)\<notin>set p \<and> (v,u)\<notin>set p"
        by (auto dest: pathVertices_edge[OF PATH])
      thus "incoming v \<inter> set p = {}" "outgoing v \<inter> set p = {}"
        by (auto simp: incoming_def outgoing_def)
    qed    
      
    lemma (in Graph) adjacent_edges_on_simple_path:
      assumes SPATH: "isSimplePath s p t"
      assumes VNV: "v\<in>set (pathVertices_fwd s p)" "v\<noteq>s" "v\<noteq>t"
      obtains p1 u w p2 where 
        "p = p1@(u,v)#(v,w)#p2" "incoming v \<inter> set p = {(u,v)}" "outgoing v \<inter> set p = {(v,w)}"
    proof -
      from SPATH have PATH: "isPath s p t" and DIST: "distinct (pathVertices_fwd s p)" 
        by (auto simp: isSimplePath_def pathVertices_fwd)
      from split_path_at_vertex[OF VNV(1) PATH] obtain p1 p2 where 
        [simp]: "p=p1@p2" and P1: "isPath s p1 v" and P2: "isPath v p2 t" .
      from \<open>v\<noteq>s\<close> P1 obtain p1' u where 
        [simp]: "p1=p1'@[(u,v)]" and P1': "isPath s p1' u" and UV: "(u,v)\<in>E"
        by (cases p1 rule: rev_cases) (auto simp: split_path_simps)
      from \<open>v\<noteq>t\<close> P2 obtain w p2' where 
        [simp]: "p2=(v,w)#p2'" and VW: "(v,w)\<in>E" and P2': "isPath w p2' t"
        by (cases p2) (auto)
      show thesis
        apply (rule that[of p1' u w p2'])
        apply simp
        using isSPath_sg_outgoing[OF SPATH, of v w] isSPath_sg_incoming[OF SPATH, of u v]
          isPath_edgeset[OF PATH]
        apply (fastforce simp: incoming_def outgoing_def)+
        done
    qed

    (* TODO: Move. Interpret finite-graph for cf, and move lemmas in general form their *)
    lemma finite_cf_incoming[simp, intro!]: "finite (cf.incoming v)" 
      unfolding cf.incoming_def 
      apply (rule finite_subset[where B="V\<times>V"])
      using cf.E_ss_VxV by auto

    lemma finite_cf_outgoing[simp, intro!]: "finite (cf.outgoing v)" 
      unfolding cf.outgoing_def 
      apply (rule finite_subset[where B="V\<times>V"])
      using cf.E_ss_VxV by auto

    lemma augFlow_resFlow: "isAugmenting p \<Longrightarrow> Flow cf s t (augmentingFlow p)"
      proof -
        assume asm: "isAugmenting p"
        hence SPATH: "cf.isSimplePath s p t" by (simp add: isAugmenting_def)
        hence PATH: "cf.isPath s p t" by (simp add: cf.isSimplePath_def)

        {
          fix e
          have "0 \<le> (augmentingFlow p) e \<and> (augmentingFlow p) e \<le> cf e"
            proof (cases "e \<in> set p") 
              case True
                hence "bottleNeck p \<le> cf e" unfolding bottleNeck_alt by auto
                moreover  have "(augmentingFlow p) e = bottleNeck p" 
                  unfolding augmentingFlow_def using True by auto
                moreover have "0 < bottleNeck p" using bottleNeck_gzero[OF asm] by simp 
                ultimately show ?thesis by auto
            next
              case False
                hence "(augmentingFlow p) e = 0" unfolding augmentingFlow_def by auto
                thus ?thesis using resE_nonNegative by auto
            qed
        } moreover {
          fix v
          assume asm_s: "v \<in> Graph.V cf - {s, t}"

          have "card (Graph.incoming cf v \<inter> set p) = card (Graph.outgoing cf v \<inter> set p)"  
          proof (cases)  
            assume "v\<in>set (cf.pathVertices_fwd s p)"
            from cf.split_path_at_vertex[OF this PATH] obtain p1 p2 where
              P_FMT: "p=p1@p2" 
              and 1: "cf.isPath s p1 v"
              and 2: "cf.isPath v p2 t" 
              .
            from 1 obtain p1' u1 where [simp]: "p1=p1'@[(u1,v)]"    
              using asm_s by (cases p1 rule: rev_cases) (auto simp: split_path_simps)
            from 2 obtain p2' u2 where [simp]: "p2=(v,u2)#p2'"    
              using asm_s by (cases p2) (auto)
            from 
              cf.isSPath_sg_outgoing[OF SPATH, of v u2]  cf.isSPath_sg_incoming[OF SPATH, of u1 v]
              cf.isPath_edgeset[OF PATH] 
            have "cf.outgoing v \<inter> set p = {(v,u2)}" "cf.incoming v \<inter> set p = {(u1,v)}"
              by (fastforce simp: P_FMT cf.outgoing_def cf.incoming_def)+

            thus ?thesis by auto
          next
            assume "v\<notin>set (cf.pathVertices_fwd s p)"
            then have "\<forall>u. (u,v)\<notin>set p \<and> (v,u)\<notin>set p"
              by (auto dest: cf.pathVertices_edge[OF PATH])
            hence "cf.incoming v \<inter> set p = {}" "cf.outgoing v \<inter> set p = {}"
              by (auto simp: cf.incoming_def cf.outgoing_def)
            thus ?thesis by auto
          qed  
          hence "(\<Sum>e \<in> Graph.incoming cf v. (augmentingFlow p) e) =
            (\<Sum>e \<in> Graph.outgoing cf v. (augmentingFlow p) e)"
            by (auto simp: setsum_augmenting_alt)
        } ultimately show ?thesis unfolding Flow_def by auto
      qed
     

    lemma augFlow_val: "isAugmenting p \<Longrightarrow> Flow.val cf s (augmentingFlow p) = bottleNeck p"
      proof -
        assume asm: "isAugmenting p"
        with augFlow_resFlow interpret f!: Flow cf s t "augmentingFlow p" .

        from asm have SPATH: "cf.isSimplePath s p t" by (simp add: isAugmenting_def)
        hence PATH: "cf.isPath s p t" by (simp add: cf.isSimplePath_def)
        then obtain v p' where "p=(s,v)#p'" "(s,v)\<in>cf.E" 
          using s_not_t by (cases p) auto
        with cf.isSPath_sg_outgoing[OF SPATH, of s v] cf.isPath_edgeset[OF PATH] 
          have "cf.outgoing s \<inter> set p = {(s,v)}" by (fastforce simp: cf.outgoing_def)
        moreover have "cf.incoming s \<inter> set p = {}" using SPATH no_incoming_s
          by (auto 
            simp: cf.incoming_def \<open>p=(s,v)#p'\<close> in_set_conv_decomp[where xs=p']
            simp: cf.isSimplePath_append cf.isSimplePath_cons)  
        ultimately show ?thesis  
          unfolding f.val_def
          by (auto simp: setsum_augmenting_alt)
      qed    

  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
end
