theory ResidualGraph
imports Network
begin

  definition (in Graph) residualGraph :: "flow \<Rightarrow> graph" where 
    "residualGraph f \<equiv> \<lambda>(u, v).
      if (u, v) \<in> E then
        c (u, v) - f (u, v)
      else if (v, u) \<in> E then
        f (v, u)
      else
        0"

  context NFlow
  begin
    abbreviation "cf \<equiv> residualGraph f"
    
    lemma resV_netV : "Graph.V cf = V"
      unfolding Graph.V_def Graph.E_def residualGraph_def
      apply (auto simp: capacity_cons no_parallel_edge)
      by (metis neq0_conv)

    (* Original, manual proof *)  
    lemma "Graph.V cf = V"
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
                        unfolding residualGraph_def using `(u, v) \<in> E` by (auto simp: E_def)
                      then have "cf (u, v) \<noteq> 0" using `(u, v) \<in> E` E_def by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  next
                    case False 
                      then have "cf (v, u) = f (u, v)" unfolding residualGraph_def
                        using `(u, v) \<in> E` E_def no_parallel_edge by auto
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
                        unfolding residualGraph_def using `(v, u) \<in> E` by (auto simp: E_def)
                      then have "cf (v, u) \<noteq> 0" using `(v, u) \<in> E` E_def by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  next
                    case False 
                      then have "cf (u, v) = f (v, u)" unfolding residualGraph_def
                        using `(v, u) \<in> E` E_def no_parallel_edge by auto
                      then have "cf (u, v) \<noteq> 0" using False by auto
                      thus ?thesis unfolding Graph.E_def by auto
                  qed
                thus ?thesis by auto
              qed
         qed     
      next
        show "Graph.V cf \<subseteq> V" unfolding Graph.V_def Graph.E_def residualGraph_def by auto
      qed

    lemma finite_cfV[simp, intro!]: "finite (Graph.V cf)"  
      by (simp add: resV_netV)

    (* TODO: Simpler proof, using Vfin_imp_Efin, once this is in Graph *)
    lemma finite_cfE[simp, intro!]: "finite (Graph.E cf)"  
    proof -
      have "Graph.E cf \<subseteq> Graph.V cf \<times> Graph.V cf" by (auto simp: Graph.V_def)
      moreover have "finite \<dots>" by (simp add: resV_netV)
      ultimately show ?thesis by (rule finite_subset)
    qed  
    
    lemma st_nodes_cf[simp, intro!]: "s\<in>Graph.V cf" "t\<in>Graph.V cf"
      by (auto simp: resV_netV)

    lemma reverse_flow: "Flow cf s t f' \<Longrightarrow> \<forall>(u, v) \<in> E. f' (v, u) \<le> f (u, v)"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix u v
          assume "(u, v) \<in> E"
          then have "cf (v, u) = f (u, v)"
            unfolding residualGraph_def E_def using no_parallel_edge by auto
          moreover have "f' (v, u) \<le> cf (v, u)" using asm Flow_def by auto
          ultimately have "f' (v, u) \<le> f (u, v)" by metis
        }
        thus ?thesis by auto
      qed  
  end
  
  context NFlow
  begin
    definition "isAugmenting p \<equiv> Graph.isSimplePath cf s p t"
      
    definition bottleNeck :: "path \<Rightarrow> capacity" where
      "bottleNeck p \<equiv> Min {cf e | e. e \<in> set p}"
      
    lemma bottleNeck_gzero: "Graph.isPath cf s p t \<Longrightarrow> bottleNeck p > 0"
      proof -
        assume asm: "Graph.isPath cf s p t"
        {
          fix e
          assume "e \<in> set p"
          then obtain u v where "e = (u, v)" by (metis nat_gcd.cases)
          then have "e \<in> Graph.E cf" using Graph.isPath_edgeset[OF asm]
            by (metis (poly_guards_query) `e \<in> set p`)
          then have "cf e \<noteq> 0" using Graph.E_def by auto
        }
        moreover {
          have "finite (set p)" by auto
          then have f1: "finite {cf e |e. e \<in> set p }"
            proof -
              have "finite {R. R \<in> set p}" by auto
              thus "finite {cf e |e. e \<in> set p}" using finite_image_set by blast
            qed
          have "set p \<noteq> {}" using asm s_not_t by (metis Graph.isPath.simps(1) set_empty)
          then have f2: "{cf e |e. e \<in> set p} \<noteq> {}" 
            by (metis (mono_tags, lifting) Collect_empty_eq all_not_in_conv)
          
          note Min_in[OF f1 f2]
        }
        ultimately show ?thesis unfolding bottleNeck_def by auto
      qed
      
    definition augmentingFlow :: "path \<Rightarrow> flow" where
      "augmentingFlow p \<equiv> \<lambda>(u, v).
        if (u, v) \<in> (set p) then
          bottleNeck p
        else
          0"
    
    lemma augFlow_node_card: "isAugmenting p \<Longrightarrow> \<forall> v \<in> Graph.V cf - {s, t}.
      card {u |u. u \<in> Graph.V cf \<and> (u, v) \<in> set p} = card {u |u. u \<in> Graph.V cf \<and> (v, u) \<in> set p}"
      unfolding isAugmenting_def
      proof -
        assume asm: "Graph.isSimplePath cf s p t"
        {
          fix v
          assume asm_s: "v \<in> Graph.V cf - {s, t}"
          let ?S_OP = "{u | u. u \<in> Graph.V cf \<and> (v, u) \<in> set p}"
          let ?S_IP = "{u | u. u \<in> Graph.V cf \<and> (u, v) \<in> set p}"
          have "card ?S_IP = card ?S_OP"
            proof (cases "?S_IP = {}")
              case True
                have "?S_OP = {}"
                  proof (rule ccontr)
                    assume "\<not> ?S_OP = {}"
                    then obtain u where "(v, u) \<in> set p" by auto
                    moreover have "Graph.isPath cf s p t" using asm Graph.isSimplePath_def by auto
                    ultimately obtain x where "(x, v) \<in> set p"
                      using asm_s Graph.isPath_ex_edge1[of cf s p t v u] by auto
                    moreover have "(x, v) \<in> Graph.E cf" using `Graph.isPath cf s p t` 
                      Graph.isPath_edgeset[of cf s p t "(x,v)"] `(x, v) \<in> set p` by auto
                    ultimately have "x \<in> ?S_IP" using Graph.V_def by auto
                    thus "False" using True by auto
                  qed
                thus ?thesis using True by metis
            next
              case False
                then obtain u where "u \<in> ?S_IP" by auto
                then have "(u, v) \<in> set p" by blast
                {
                  have "\<forall> u'. u' \<noteq> u \<longrightarrow> u' \<notin> ?S_IP" using 
                    Graph.isSPath_sg_incoming[OF asm `(u, v) \<in> set p`] by auto
                  then have "?S_IP = {u}" using `u \<in> ?S_IP` by auto
                  then have "card ?S_IP = 1" by auto
                }
                moreover {
                  have f1: "Graph.isPath cf s p t" using asm Graph.isSimplePath_def by auto
                  obtain v' where "(v, v') \<in> set p" using asm_s 
                    Graph.isPath_ex_edge2[OF f1 `(u, v) \<in> set p`] by auto
                  then have "v' \<in> Graph.V cf" using Graph.isPath_edgeset[OF f1] Graph.V_def by auto
                  then have "v' \<in> ?S_OP" using `(v, v') \<in> set p` by auto
                  have "\<forall> v''. v'' \<noteq> v' \<longrightarrow> v'' \<notin> ?S_OP" using 
                    Graph.isSPath_sg_outgoing[OF asm `(v, v') \<in> set p`] by auto
                  then have "?S_OP = {v'}" using `v' \<in> ?S_OP` by auto
                  then have "card ?S_OP = 1" by auto
                }
                ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
      qed      
          
    lemma augFlow_resFlow: "isAugmenting p \<Longrightarrow> Flow cf s t (augmentingFlow p)"
      proof -
        assume "isAugmenting p"
        then have asm: "Graph.isPath cf s p t \<and> distinct (pathVertices s p)" 
          using isAugmenting_def Graph.isSimplePath_def by auto
        {
          fix e
          have "(augmentingFlow p) e \<le> cf e"
            proof (cases "e \<in> set p") 
              case True
                have "finite {cf e | e. e \<in> set p}"
                  proof -
                    have "finite {R. R \<in> set p}" by auto
                    thus "finite {cf e |e. e \<in> set p}" using finite_image_set by blast
                  qed
                then have "bottleNeck p \<le> cf e" unfolding bottleNeck_def Min_def 
                  by (metis (mono_tags, lifting) True Min_def Min_le mem_Collect_eq)
                moreover  have "(augmentingFlow p) e = bottleNeck p" 
                  unfolding augmentingFlow_def using True by auto
                ultimately show ?thesis by auto
            next
              case False
                thus ?thesis unfolding augmentingFlow_def by auto
            qed
        } note fct1 = this
        moreover {
          fix v
          assume asm_s: "v \<in> Graph.V cf - {s, t}"
          have "(\<Sum>e \<in> Graph.incoming cf v. (augmentingFlow p) e) =
            (\<Sum>e \<in> Graph.outgoing cf v. (augmentingFlow p) e)"
            proof -
              let ?S = "{u | u. u \<in> Graph.V cf}"
              let ?S_OP = "{u | u. u \<in> Graph.V cf \<and> (v, u) \<in> set p}"
              let ?S_ON = "{u | u. u \<in> Graph.V cf \<and> (v, u) \<notin> set p}"
              let ?S_IP = "{u | u. u \<in> Graph.V cf \<and> (u, v) \<in> set p}"
              let ?S_IN = "{u | u. u \<in> Graph.V cf \<and> (u, v) \<notin> set p}"
              let ?OG = "Graph.outgoing cf v"
              let ?IN = "Graph.incoming cf v"
              let ?F = "augmentingFlow p"
              let ?F_O = "\<lambda>x. ?F (v, x)"
              let ?F_I = "\<lambda>x. ?F (x, v)"
              let ?SUM = "\<lambda>s f. \<Sum>e \<in> s. f e"
              {
                have f1: "finite (Graph.V cf)" using resV_netV finite_V by auto
                have f2: "\<forall>e. (augmentingFlow p) e \<le> cf e" using fct1 by auto
                note Graph.sum_incoming_alt[OF f1 f2]
                
                then have "?SUM ?IN ?F = ?SUM ?S ?F_I" using asm_s by auto
              }
              moreover {
                {
                  have f1: "finite ?S_IP" using resV_netV finite_V by auto
                  have f2: "finite ?S_IN" using resV_netV finite_V by auto
                  have f3: "?S_IP \<inter> ?S_IN = {}" by auto
                  
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of ?F_I]
                moreover have "?S_IP \<union> ?S_IN = ?S" by auto
                ultimately have "?SUM ?S ?F_I = ?SUM ?S_IP ?F_I + ?SUM ?S_IN ?F_I" by auto
              }
              moreover {
                {
                  fix e
                  assume "e \<in> ?S_IN"
                  then have "(e, v) \<notin> set p" by auto
                  then have "?F_I e = 0" unfolding augmentingFlow_def by auto
                }
                then have "\<And>e. e \<in> ?S_IN \<Longrightarrow> ?F_I e = 0" by auto
                then have "?SUM ?S_IN ?F_I = 0" by auto
              }
              moreover {
                {
                  fix e
                  assume "e \<in> ?S_IP"
                  then have "(e, v) \<in> set p" by auto
                  then have "?F_I e = bottleNeck p" unfolding augmentingFlow_def by auto
                }
                then have f1: "\<forall>x \<in> ?S_IP. ?F_I x = bottleNeck p" by auto
                have f2: "finite ?S_IP" using resV_netV finite_V by auto
                note setsumExt.decomp_4[OF f2 f1]
              }
              moreover have "card ?S_IP = card ?S_OP" 
                using augFlow_node_card[OF `isAugmenting p`] asm_s by auto
              ultimately have "?SUM ?IN ?F = bottleNeck p * card ?S_OP" by auto
              moreover {
                {
                  fix e
                  assume "e \<in> ?S_OP"
                  then have "(v, e) \<in> set p" by auto
                  then have "?F_O e = bottleNeck p" unfolding augmentingFlow_def by auto
                }
                then have f1: "\<forall>x \<in> ?S_OP. ?F_O x = bottleNeck p" by auto
                have f2: "finite ?S_OP" using resV_netV finite_V by auto
                note setsumExt.decomp_4[OF f2 f1]
                then have "bottleNeck p * card ?S_OP = ?SUM ?S_OP ?F_O" by auto
              }
              moreover {
                {
                  fix e
                  assume "e \<in> ?S_ON"
                  then have "(v, e) \<notin> set p" by auto
                  then have "?F_O e = 0" unfolding augmentingFlow_def by auto
                }
                then have "\<And>e. e \<in> ?S_ON \<Longrightarrow> ?F_O e = 0" by auto
                then have "?SUM ?S_ON ?F_O = 0" by auto
                then have "?SUM ?S_OP ?F_O = ?SUM ?S_OP ?F_O + ?SUM ?S_ON ?F_O" by auto
              }
              moreover {
                {
                  have f1: "finite ?S_OP" using resV_netV finite_V by auto
                  have f2: "finite ?S_ON" using resV_netV finite_V by auto
                  have f3: "?S_OP \<inter> ?S_ON = {}" by auto
                  
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of ?F_O]
                moreover have "?S_OP \<union> ?S_ON = ?S" by auto
                ultimately have "?SUM ?S_OP ?F_O + ?SUM ?S_ON ?F_O = ?SUM ?S ?F_O" by auto
              }
              moreover {
                have f1: "finite (Graph.V cf)" using resV_netV finite_V by auto
                have f2: "\<forall>e. (augmentingFlow p) e \<le> cf e" using fct1 by auto
                note Graph.sum_outgoing_alt[OF f1 f2]
                
                then have "?SUM ?S ?F_O = ?SUM ?OG ?F" using asm_s by auto
              }
              ultimately show ?thesis by auto
            qed
        }
        ultimately show ?thesis unfolding Flow_def 
          by (auto)
      qed
      
    lemma augFlow_val: "isAugmenting p \<Longrightarrow> Flow.val cf s (augmentingFlow p) = bottleNeck p"
      proof -
        assume asm: "isAugmenting p"
        {
          then have "Graph.isPath cf s p t" using isAugmenting_def Graph.isSimplePath_def by auto
          then have "p \<noteq> []" using s_not_t by (metis Graph.isPath.simps(1))
          then obtain e es where "p = e # es" by (metis list.collapse)
          then obtain u v where "e = (u, v)" by (metis nat_gcd.cases)
          then have "u = s" using `p = e#es` `Graph.isPath cf s p t` by (metis Graph.isPath.simps(2))
          then have "\<exists> v. (s, v) \<in> set p" using `p = e # es` `e = (u, v)` by auto
        } note fct = this
        show ?thesis
          proof -
            let ?S = "{u | u. u \<in> Graph.V cf}"
            let ?S_OP = "{u | u. u \<in> Graph.V cf \<and> (s, u) \<in> set p}"
            let ?S_ON = "{u | u. u \<in> Graph.V cf \<and> (s, u) \<notin> set p}"
            let ?S_IP = "{u | u. u \<in> Graph.V cf \<and> (u, s) \<in> set p}"
            let ?S_IN = "{u | u. u \<in> Graph.V cf \<and> (u, s) \<notin> set p}"
            let ?OG = "Graph.outgoing cf s"
            let ?IN = "Graph.incoming cf s"
            let ?F = "augmentingFlow p"
            let ?F_O = "\<lambda>x. ?F (s, x)"
            let ?F_I = "\<lambda>x. ?F (x, s)"
            let ?SUM = "\<lambda>s f. \<Sum>e \<in> s. f e"
            have fct1: "Graph.Flow cf s t (augmentingFlow p)" using asm augFlow_resFlow by auto
            then have "Flow.val cf s (augmentingFlow p) = ?SUM ?OG ?F - ?SUM ?IN ?F"
              using Flow.val_def by auto
            moreover {
              have f1: "finite (Graph.V cf)" using resV_netV finite_V by auto
              have f2: "\<forall>e. (augmentingFlow p) e \<le> cf e" using fct1 Graph.Flow_def by auto
              note Graph.sum_outgoing_alt[OF f1 f2]
              
              then have "?SUM ?OG ?F = ?SUM ?S ?F_O" using s_node resV_netV by auto
            }
            moreover {
              {
                have f1: "finite ?S_OP" using resV_netV finite_V by auto
                have f2: "finite ?S_ON" using resV_netV finite_V by auto
                have f3: "?S_OP \<inter> ?S_ON = {}" by auto
                
                note setsum.union_disjoint[OF f1 f2 f3]
              }
              note this[of ?F_O]
              moreover have "?S_OP \<union> ?S_ON = ?S" by auto
              ultimately have "?SUM ?S ?F_O = ?SUM ?S_OP ?F_O + ?SUM ?S_ON ?F_O" by auto
            }
            moreover {
              {
                fix e
                assume "e \<in> ?S_ON"
                then have "(s, e) \<notin> set p" by auto
                then have "?F_O e = 0" unfolding augmentingFlow_def by auto
              }
              then have "\<And>e. e \<in> ?S_ON \<Longrightarrow> ?F_O e = 0" by auto
              then have "?SUM ?S_ON ?F_O = 0" by auto
            }
            moreover {
              {
                fix e
                assume "e \<in> ?S_OP"
                then have "(s, e) \<in> set p" by auto
                then have "?F_O e = bottleNeck p" unfolding augmentingFlow_def by auto
              }
              then have f1: "\<forall>x \<in> ?S_OP. ?F_O x = bottleNeck p" by auto
              have f2: "finite ?S_OP" using resV_netV finite_V by auto
              note setsumExt.decomp_4[OF f2 f1]
            }
            
            
            moreover {
              have f1: "finite (Graph.V cf)" using resV_netV finite_V by auto
              have f2: "\<forall>e. (augmentingFlow p) e \<le> cf e" using fct1 Graph.Flow_def by auto
              note Graph.sum_incoming_alt[OF f1 f2]
              
              then have "?SUM ?IN ?F = ?SUM ?S ?F_I" using s_node resV_netV by auto
            }
            moreover {
              {
                have f1: "finite ?S_IP" using resV_netV finite_V by auto
                have f2: "finite ?S_IN" using resV_netV finite_V by auto
                have f3: "?S_IP \<inter> ?S_IN = {}" by auto
                
                note setsum.union_disjoint[OF f1 f2 f3]
              }
              note this[of ?F_I]
              moreover have "?S_IP \<union> ?S_IN = ?S" by auto
              ultimately have "?SUM ?S ?F_I = ?SUM ?S_IP ?F_I + ?SUM ?S_IN ?F_I" by auto
            }
            moreover {
              {
                fix e
                assume "e \<in> ?S_IN"
                then have "(e, s) \<notin> set p" by auto
                then have "?F_I e = 0" unfolding augmentingFlow_def by auto
              }
              then have "\<And>e. e \<in> ?S_IN \<Longrightarrow> ?F_I e = 0" by auto
              then have "?SUM ?S_IN ?F_I = 0" by auto
            }
            moreover {
              {
                fix e
                assume "e \<in> ?S_IP"
                then have "(e, s) \<in> set p" by auto
                then have "?F_I e = bottleNeck p" unfolding augmentingFlow_def by auto
              }
              then have f1: "\<forall>x \<in> ?S_IP. ?F_I x = bottleNeck p" by auto
              have f2: "finite ?S_IP" using resV_netV finite_V by auto
              note setsumExt.decomp_4[OF f2 f1]
            }
            ultimately have "Flow.val cf s (augmentingFlow p) = 
              bottleNeck p * card ?S_OP - bottleNeck p * card ?S_IP" by auto
            also {
              have "Graph.isSimplePath cf s p t" using asm isAugmenting_def by auto
              moreover obtain v where "(s, v) \<in> set p" using fct by auto
              ultimately have "\<forall> u. u \<noteq> v \<longrightarrow> u \<notin> ?S_OP" using 
                Graph.isSPath_sg_outgoing by auto
              moreover {
                have "Graph.isPath cf s p t" 
                  using `Graph.isSimplePath cf s p t` Graph.isSimplePath_def by auto
                then have f2: "v \<in> Graph.V cf" using Graph.isPath_edgeset[of cf s p t "(s,v)"] 
                  Graph.V_def[of cf] `(s, v) \<in> set p` by auto
                then have "v \<in> ?S_OP" using `(s, v) \<in> set p` by auto
              }
              ultimately have "?S_OP = {v}" by auto
              then have "card ?S_OP = 1" by auto
            }
            also {
              {
                fix v'
                have fct1: "Graph.isSimplePath cf s p t" using asm isAugmenting_def by auto
                moreover obtain v where "(s, v) \<in> set p" using fct by auto
                ultimately have "\<exists>es1 es2. p = es1 @ (v', s) # (s, v) # es2 \<or> (v', s) \<notin> set p" 
                  using Graph.isSPath_no_returning by auto
                moreover {
                  have "\<not> (\<exists>es1 es2. p = es1 @ (v', s) # (s, v) # es2)"
                    proof (rule ccontr)
                      assume "\<not> \<not> (\<exists>es1 es2. p = es1 @ (v', s) # (s, v) # es2)"
                      then obtain es1 es2 where obt2: "p = es1 @ (v', s) # (s, v) # es2" by blast
                      then show "False"
                        proof (cases "es1 = []")
                          case True
                            have "fst (hd p) = s" using fct1 by (metis Graph.isPath.simps(1) 
                              Graph.isPath_head Graph.isSimplePath_def list.collapse s_not_t)
                            then have "v' = s" using True obt2 by auto
                            then have "(s, s) \<in> set p" using obt2 by auto
                            thus ?thesis using Graph.isSPath_no_selfloop[OF fct1] by auto
                        next
                          case False
                            then obtain e es1' where "es1 = e # es1'" by (metis list.collapse)
                            then have f1: "p = e # es1' @ (v', s) # (s, v) # es2" using obt2 by auto
                            then have "fst e = s" using fct1 
                              by (metis Graph.isPath_head Graph.isSimplePath_def)
                            then obtain v'' where "e = (s, v'')" by (metis prod.collapse)
                            then obtain es1'' where f2: "p = (s, v'') # es1'' @ 
                              (v', s) # (s, v) # es2" using f1 by auto
                            moreover note Graph.pathVertices_append[of s "(s, v'') # es1''"
                              "(v', s) # (s, v) # es2"]
                            moreover have "\<exists> vs1. butlast (pathVertices s ((s, v'') # es1'')) = 
                              s # vs1" by (metis Graph.pathVertices.simps(1) 
                              Graph.pathVertices.simps(2) Graph.pathVertices_alt `e = (s, v'')`
                              `fst e = s` append_is_Nil_conv butlast.simps(2) not_Cons_self2)
                            moreover have "\<exists> vs2.  pathVertices (last (pathVertices s ((s, v'') #
                              es1''))) ((v', s) # (s, v) # es2) = v' # s # vs2"
                              by (metis Graph.pathVertices.simps(2) fst_conv)
                            ultimately have "\<exists> vs1 vs2. pathVertices s p = s # vs1 @ v' # s # vs2"
                              by auto
                            then have "\<not> distinct (pathVertices s p)" by auto
                            then show "False" using fct1 Graph.isSimplePath_def by auto
                        qed
                    qed
                }
                ultimately have "(v', s) \<notin> set p" by auto
              }
              then have "\<forall> v'. (v', s) \<notin> set p" by auto
              then have "card ?S_IP = 0" by auto
            }
            finally show ?thesis by simp
          qed
      qed
  end

end