theory Augmenting
imports ResidualGraph
begin

  context NFlow
  begin
    definition augment :: "flow \<Rightarrow> flow" where
      "augment f' \<equiv> \<lambda>(u, v).
        if (u, v) \<in> E then
          f (u, v) + f' (u, v) - f' (v, u)
        else
          0"
  end
  
  context NFlow
  begin
    lemma augment_flow_presv_cap: "Flow cf s t f' \<Longrightarrow> \<forall>e. augment f' e \<le> c e"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix e
          have "augment f' e \<le> c e"
            proof -
              {
                fix u v
                assume "e = (u, v)"
                have "augment f' (u, v) \<le> c (u, v)" (is "?L \<le> _")
                  proof -
                    have "?L \<le> f (u, v)  + f' (u, v)" unfolding augment_def by auto
                    moreover have "f' (u, v) \<le> cf (u, v)" using asm Flow_def by auto
                    ultimately have fct: "?L \<le> f (u, v) + cf (u, v)" by simp
                    thus ?thesis
                      proof (cases "(u, v) \<in> E")
                        case True
                          then have "cf (u, v) = c (u, v) - f(u, v)"
                            unfolding residualGraph_def by (auto simp: E_def)
                          thus ?thesis using fct capacity_cons
                            by (metis (poly_guards_query) le_add_diff_inverse)
                      next
                        case False
                          thus ?thesis
                            proof (cases "(v, u) \<in> E")
                              case True
                                have "augment f' (u, v) = 0"
                                  unfolding augment_def using `(u, v) \<notin> E` by auto
                                thus ?thesis by auto
                            next
                              case False
                                then have "cf (u, v) = 0"
                                  unfolding residualGraph_def using `(u, v) \<notin> E` by (auto simp: E_def)
                                thus ?thesis using fct capacity_cons
                                  by (metis Nat.add_0_right le_trans)
                            qed  
                      qed        
                  qed    
              }        
              thus ?thesis by (metis (poly_guards_query) surj_pair)                    
            qed
        }
        thus ?thesis by auto
      qed
  end
  
  context NFlow
  begin
    lemma augment_outflow_split: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V. (\<Sum>e \<in> outgoing v. (augment f') e) =
      nat ((\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. int (f (v, e))) +
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. int (f' (v, e))) -
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. int (f' (e, v))))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e \<in> outgoing v. (augment f') e) = 
            nat ((\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. int (f (v, e))) +
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. int (f' (v, e))) -
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. int (f' (e, v))))"
            proof -
              let ?S = "{u | u. u \<in> V}"
              let ?S_OE = "{u |u. u \<in> V \<and> (v, u) \<in> E}"
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?FA = "\<lambda> x. (augment f') x"
              let ?FF = "\<lambda> (u, v). f' (u, v) - f' (v, u)"
              let ?FF_I = "\<lambda> (u, v). int (f' (u, v)) - int (f' (v, u))"
              let ?FE = "\<lambda> (u, v). f (u, v) + f' (u, v) - f' (v, u)"
              let ?FE_I = "\<lambda> (u, v). int (f (u, v)) + (int(f' (u, v)) - int (f' (v, u)))"
              let ?FO = "\<lambda> f x. f (v, x)"
              let ?FO_I = "\<lambda> f x. int (f (v, x))"
              let ?FI_I = "\<lambda> f x. int (f (x, v))"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SUS = "?SUM ?S"
              let ?SOE = "?SUM ?S_OE"
              let ?SON = "?SUM ?S_ON"
              {
                have "?SUM (outgoing v) ?FA = ?SUS (?FO (augment f'))" using 
                  sum_outgoing_alt[OF finite_V] augment_flow_presv_cap[OF asm] asm_s by auto
                then have "?SUM (outgoing v) ?FA = nat (int (?SUS (?FO ?FA)))" by auto
                then have "?SUM (outgoing v) ?FA = nat (?SUS (?FO_I ?FA))"
                  using Int.int_setsum by metis
              }
              moreover {
                {
                  have f1: "finite ?S_OE" using finite_V by auto
                  have f2: "finite ?S_ON" using finite_V by auto
                  have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FO_I ?FA"]
                moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                ultimately have "?SUS (?FO_I ?FA) = ?SOE (?FO_I ?FA) + ?SON (?FO_I ?FA)" by auto
                moreover {
                  have "\<And>u. u \<in> ?S_ON \<Longrightarrow> (?FO_I ?FA) u = 0" unfolding augment_def by auto
                  then have "?SON (?FO_I ?FA) = 0" by auto
                } 
                ultimately have "?SUS (?FO_I ?FA) = ?SOE (?FO_I ?FA)" by auto 
              }
              moreover {
                {
                  have "?SOE (?FO_I ?FA) = ?SOE (?FO_I ?FE)" unfolding augment_def by auto
                  moreover have "\<And>u. u \<in> ?S_OE \<Longrightarrow> ?FO_I ?FE u = ?FO ?FE_I u"
                    using reverse_flow[OF asm] by auto
                  ultimately have "?SOE (?FO_I ?FA) = ?SOE (?FO ?FE_I)" by auto
                }
                moreover {
                  note setsum.distrib[of "?FO_I f" "?FO ?FF_I" ?S_OE]
                  then have "?SOE (?FO ?FE_I) = ?SOE (?FO_I f) + ?SOE (?FO ?FF_I)" by auto
                }
                moreover {
                  note setsum_subtractf[of "?FO_I f'" "?FI_I f'" ?S_OE]
                  then have "?SOE (?FO ?FF_I) = ?SOE (?FO_I f') - ?SOE (?FI_I f')" by auto
                }
                ultimately have "?SOE (?FO_I ?FA) =
                  ?SOE (?FO_I f) + ?SOE (?FO_I f') - ?SOE (?FI_I f')" by auto 
              }
              ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
      qed
     
    lemma augment_inflow_split: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V. (\<Sum>e \<in> incoming v. (augment f') e) =
      nat ((\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f (e, v))) +
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (e, v))) -
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (v, e))))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e \<in> incoming v. (augment f') e) = 
            nat ((\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f (e, v))) +
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (e, v))) -
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (v, e))))"
            proof -
              let ?S = "{u | u. u \<in> V}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_IN = "{u |u. u \<in> V \<and> (u, v) \<notin> E}"
              let ?FA = "\<lambda> x. (augment f') x"
              let ?FF = "\<lambda> (u, v). f' (u, v) - f' (v, u)"
              let ?FF_I = "\<lambda> (u, v). int (f' (u, v)) - int (f' (v, u))"
              let ?FE = "\<lambda> (u, v). f (u, v) + f' (u, v) - f' (v, u)"
              let ?FE_I = "\<lambda> (u, v). int (f (u, v)) + (int(f' (u, v)) - int (f' (v, u)))"
              let ?FO_I = "\<lambda> f x. int (f (v, x))"
              let ?FI = "\<lambda> f x. f (x, v)"
              let ?FI_I = "\<lambda> f x. int (f (x, v))"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SUS = "?SUM ?S"
              let ?SIE = "?SUM ?S_IE"
              let ?SIN = "?SUM ?S_IN"
              {
                have "?SUM (incoming v) ?FA = ?SUS (?FI (augment f'))" using 
                  sum_incoming_alt[OF finite_V] augment_flow_presv_cap[OF asm] asm_s by auto
                then have "?SUM (incoming v) ?FA = nat (int (?SUS (?FI ?FA)))" by auto
                then have "?SUM (incoming v) ?FA = nat (?SUS (?FI_I ?FA))"
                  using Int.int_setsum by metis
              }
              moreover {
                {
                  have f1: "finite ?S_IE" using finite_V by auto
                  have f2: "finite ?S_IN" using finite_V by auto
                  have f3: "?S_IE \<inter> ?S_IN = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FI_I ?FA"]
                moreover have "?S_IE \<union> ?S_IN = ?S" by auto
                ultimately have "?SUS (?FI_I ?FA) = ?SIE (?FI_I ?FA) + ?SIN (?FI_I ?FA)" by auto
                moreover {
                  have "\<And>u. u \<in> ?S_IN \<Longrightarrow> (?FI_I ?FA) u = 0" unfolding augment_def by auto
                  then have "?SIN (?FI_I ?FA) = 0" by auto
                } 
                ultimately have "?SUS (?FI_I ?FA) = ?SIE (?FI_I ?FA)" by auto 
              }
              moreover {
                {
                  have "?SIE (?FI_I ?FA) = ?SIE (?FI_I ?FE)" unfolding augment_def by auto
                  moreover have "\<And>u. u \<in> ?S_IE \<Longrightarrow> ?FI_I ?FE u = ?FI ?FE_I u"
                    using reverse_flow[OF asm] by auto
                  ultimately have "?SIE (?FI_I ?FA) = ?SIE (?FI ?FE_I)" by auto
                }
                moreover {
                  note setsum.distrib[of "?FI_I f" "?FI ?FF_I" ?S_IE]
                  then have "?SIE (?FI ?FE_I) = ?SIE (?FI_I f) + ?SIE (?FI ?FF_I)" by auto
                }
                moreover {
                  note setsum_subtractf[of "?FI_I f'" "?FO_I f'" ?S_IE]
                  then have "?SIE (?FI ?FF_I) = ?SIE (?FI_I f') - ?SIE (?FO_I f')" by auto
                }
                ultimately have "?SIE (?FI_I ?FA) =
                  ?SIE (?FI_I f) + ?SIE (?FI_I f') - ?SIE (?FO_I f')" by auto 
              }
              ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
     qed
  end
  
  context NFlow
  begin
    lemma augment_res_inflow_alt: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V.
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (e, v))) =
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. int (f' (e, v)))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (e, v))) =
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. int (f' (e, v)))"
            proof -
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_NN = "{u |u. u \<in> V \<and> (u, v) \<notin> E \<and> (v, u) \<notin> E}"
              let ?FI_I = "\<lambda> f x. int (f (x, v))"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SON = "?SUM ?S_ON"
              let ?SIE = "?SUM ?S_IE"
              let ?SNN = "?SUM ?S_NN" 
              have "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FI_I f') u = 0"
                proof -
                  {
                    fix u
                    assume "u \<in> ?S_NN"
                    then have "(u, v) \<notin> E \<and> (v, u) \<notin> E" by auto
                    then have "cf (u, v) = 0 \<and> cf (v, u) = 0" unfolding residualGraph_def by (auto simp: E_def)
                    then have "f' (u, v) = 0 \<and> f' (v, u) = 0"
                      using asm Flow_def by (metis le0 le_antisym)
                    then have "(?FI_I f') u = 0" by auto
                  }
                  then show "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FI_I f') u = 0" by auto
                qed
              moreover {
                {
                  have f1: "finite ?S_IE" using finite_V by auto
                  have f2: "finite ?S_NN" using finite_V by auto
                  have f3: "?S_IE \<inter> ?S_NN = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FI_I f'"]
                moreover have "?S_IE \<union> ?S_NN = ?S_ON"
                  unfolding E_def using no_parallel_edge asm by auto
                ultimately have "?SON (?FI_I f') = ?SIE (?FI_I f') + ?SNN (?FI_I f')" by auto                  
              }
              ultimately show "?SIE (?FI_I f') = ?SON (?FI_I f')" by auto
            qed
        }
        thus ?thesis by auto
      qed 
     
    lemma augment_res_outflow_alt: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V.
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (v, e))) =
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. int (f' (v, e)))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. int (f' (v, e))) =
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. int (f' (v, e)))"
            proof -
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_NN = "{u |u. u \<in> V \<and> (u, v) \<notin> E \<and> (v, u) \<notin> E}"
              let ?FO_I = "\<lambda> f x. int (f (v, x))"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SON = "?SUM ?S_ON"
              let ?SIE = "?SUM ?S_IE"
              let ?SNN = "?SUM ?S_NN" 
              have "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FO_I f') u = 0"
                proof -
                  {
                    fix u
                    assume "u \<in> ?S_NN"
                    then have "(u, v) \<notin> E \<and> (v, u) \<notin> E" by auto
                    then have "cf (u, v) = 0 \<and> cf (v, u) = 0" unfolding residualGraph_def by (auto simp: E_def)
                    then have "f' (u, v) = 0 \<and> f' (v, u) = 0"
                      using asm Flow_def by (metis le0 le_antisym)
                    then have "(?FO_I f') u = 0" by auto
                  }
                  then show "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FO_I f') u = 0" by auto
                qed
              moreover {
                {
                  have f1: "finite ?S_IE" using finite_V by auto
                  have f2: "finite ?S_NN" using finite_V by auto
                  have f3: "?S_IE \<inter> ?S_NN = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FO_I f'"]
                moreover have "?S_IE \<union> ?S_NN = ?S_ON"
                  unfolding E_def using no_parallel_edge asm by auto
                ultimately have "?SON (?FO_I f') = ?SIE (?FO_I f') + ?SNN (?FO_I f')" by auto                  
              }
              ultimately show "?SIE (?FO_I f') = ?SON (?FO_I f')" by auto
            qed
        }
        thus ?thesis by auto
      qed
  end
  
  context NFlow
  begin
    lemma augment_flow_presv_con: "Flow cf s t f' \<Longrightarrow> 
      \<forall>v \<in> V - {s, t}. (\<Sum>e \<in> outgoing v. (augment f') e) = (\<Sum>e \<in> incoming v. (augment f') e)"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V - {s, t}"
          have "(\<Sum>e \<in> outgoing v. (augment f') e) = (\<Sum>e \<in> incoming v. (augment f') e)" 
            proof -
              let ?S = "{u | u. u \<in> V}"
              let ?S' = "{u | u. u \<in> Graph.V cf}"
              let ?S_OE = "{u |u. u \<in> V \<and> (v, u) \<in> E}"
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_IN = "{u |u. u \<in> V \<and> (u, v) \<notin> E}"
              let ?S_NN = "{u |u. u \<in> V \<and> (u, v) \<notin> E \<and> (v, u) \<notin> E}"
              let ?FA = "\<lambda> x. (augment f') x"
              let ?FF = "\<lambda> (u, v). f' (u, v) - f' (v, u)"
              let ?FF_I = "\<lambda> (u, v). int (f' (u, v)) - int (f' (v, u))"
              let ?FE = "\<lambda> (u, v). f (u, v) + f' (u, v) - f' (v, u)"
              let ?FE_I = "\<lambda> (u, v). int (f (u, v)) + (int(f' (u, v)) - int (f' (v, u)))"
              let ?FO = "\<lambda> f x. f (v, x)"
              let ?FO_I = "\<lambda> f x. int (f (v, x))"
              let ?FI = "\<lambda> f x. f (x, v)"
              let ?FI_I = "\<lambda> f x. int (f (x, v))"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SUS = "?SUM ?S"
              let ?SOE = "?SUM ?S_OE"
              let ?SON = "?SUM ?S_ON"
              let ?SIE = "?SUM ?S_IE"
              let ?SIN = "?SUM ?S_IN"
              let ?SNN = "?SUM ?S_NN"
              have "?SUM (outgoing v) ?FA = nat (?SOE (?FO_I f) + ?SOE (?FO_I f') -
                ?SOE (?FI_I f'))" using augment_outflow_split[OF asm] asm_s by auto
              moreover {
                have "?SOE (?FO_I f) = ?SOE (?FO_I f) + ?SON (?FO_I f) - ?SON (?FO_I f)" by auto
                moreover {
                  {
                    have f1: "finite ?S_OE" using finite_V by auto
                    have f2: "finite ?S_ON" using finite_V by auto
                    have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  } 
                  note this[of "?FO_I f"]
                  moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                  ultimately have "?SOE (?FO_I f) + ?SON (?FO_I f) = ?SUS (?FO_I f)" by auto
                }
                moreover {
                  have "?SUS (?FO_I f) = int (?SUS (?FO f))" using Int.int_setsum by metis
                  moreover {
                    have "?SUS (?FO f) = ?SUM (outgoing v) f"
                      using sum_outgoing_alt[OF finite_V] capacity_cons asm_s by auto
                    moreover have "?SUM (outgoing v) f = ?SUM (incoming v) f" 
                      using asm_s conservation_const by auto  
                    moreover have "?SUM (incoming v) f = ?SUS (?FI f)"
                      using sum_incoming_alt[OF finite_V] capacity_cons asm_s by auto
                    ultimately have "?SUS (?FO f) = ?SUS (?FI f)" by auto
                  }
                  moreover have "int (?SUS (?FI f)) = ?SUS (?FI_I f)" using Int.int_setsum by metis
                  ultimately have "?SUS (?FO_I f) = ?SUS (?FI_I f)" by auto
                }
                moreover {
                  {
                    have f1: "finite ?S_IE" using finite_V by auto
                    have f2: "finite ?S_IN" using finite_V by auto
                    have f3: "?S_IE \<inter> ?S_IN = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  }
                  note this[of "?FI_I f"]
                  moreover have "?S_IE \<union> ?S_IN = ?S" by auto
                  ultimately have "?SUS (?FI_I f) = ?SIE (?FI_I f) + ?SIN (?FI_I f)" by auto
                }
                moreover {
                  have "\<And>u. u \<in> ?S_ON \<Longrightarrow> (?FO_I f) u = 0" unfolding E_def using capacity_cons
                    by (metis (mono_tags, lifting) le_0_eq mem_Collect_eq of_nat_eq_0_iff splitI)
                  then have "?SON (?FO_I f) = 0" by auto
                }
                moreover {
                  have "\<And>u. u \<in> ?S_IN \<Longrightarrow> (?FI_I f) u = 0"
                    unfolding E_def using capacity_cons  no_parallel_edge 
                    proof -
                      fix u :: nat
                      assume "u \<in> {u |u. u \<in> V \<and> (u, v) \<notin> {(u, v). c (u, v) \<noteq> 0}}"
                      hence "\<not> c (u, v) \<noteq> 0" by force
                      thus "int (f (u, v)) = 0" by (metis capacity_cons le_0_eq of_nat_eq_0_iff)
                    qed
                  then have "?SIN (?FI_I f) = 0" by auto
                }
                ultimately have "?SOE (?FO_I f) = ?SIE(?FI_I f)" by auto
              }
              moreover {
                have "?SOE (?FO_I f') = ?SOE (?FO_I f') + ?SON (?FO_I f') - ?SON (?FO_I f')" by auto
                moreover {
                  {
                    have f1: "finite ?S_OE" using finite_V by auto
                    have f2: "finite ?S_ON" using finite_V by auto
                    have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  }
                  note this[of "?FO_I f'"]
                  moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                  ultimately have "?SOE (?FO_I f') + ?SON (?FO_I f') = ?SUS (?FO_I f')" by auto
                }
                moreover {
                  have "?SUS (?FO_I f') = int (?SUS (?FO f'))" using Int.int_setsum by metis
                  moreover {
                    have f1: "finite (Graph.V cf)" using resV_netV finite_V by auto
                    have f2: "\<forall>e. f' e \<le> cf e" using asm Flow_def by auto
                    {  
                      note Graph.sum_incoming_alt[OF f1 f2]
                      then have "?SUM (Graph.incoming cf v) f' = ?SUS (?FI f')" 
                        using asm_s resV_netV by auto
                    }
                    moreover { 
                      note Graph.sum_outgoing_alt[OF f1 f2]
                      then have "?SUM (Graph.outgoing cf v) f' = ?SUS (?FO f')" 
                        using asm_s resV_netV by auto
                    }
                    moreover have "?SUM (Graph.incoming cf v) f' = ?SUM (Graph.outgoing cf v) f'"
                      using resV_netV asm_s asm Flow_def by auto
                    ultimately have "?SUS (?FO f') = ?SUS (?FI f')" by auto
                  } 
                  moreover have "int (?SUS (?FI f')) = ?SUS (?FI_I f')"
                    using Int.int_setsum by metis
                  ultimately have "?SUS (?FO_I f') = ?SUS (?FI_I f')" by auto
                }
                ultimately have "?SOE (?FO_I f') = ?SUS (?FI_I f') - ?SON (?FO_I f')" by auto
              }
              moreover {
                have "?SOE (?FI_I f') = ?SOE (?FI_I f') + ?SON (?FI_I f') - ?SON (?FI_I f')" by auto
                moreover {
                  {
                    have f1: "finite ?S_OE" using finite_V by auto
                    have f2: "finite ?S_ON" using finite_V by auto
                    have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  }
                  note this[of "?FI_I f'"]
                  moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                  ultimately have "?SOE (?FI_I f') + ?SON (?FI_I f') = ?SUS (?FI_I f')" by auto
                }
                ultimately have "?SOE (?FI_I f') = ?SUS (?FI_I f') - ?SON (?FI_I f')" by auto
              }
              ultimately have "?SUM (outgoing v) ?FA = 
                nat (?SIE (?FI_I f) + ?SON (?FI_I f') - ?SON (?FO_I f'))" by auto
              moreover have "?SON (?FI_I f') = ?SIE (?FI_I f')"
                using augment_res_inflow_alt[OF asm] asm_s by auto
              moreover have "?SON (?FO_I f') = ?SIE (?FO_I f')"
                using augment_res_outflow_alt[OF asm] asm_s by auto
              moreover have " nat (?SIE (?FI_I f) + ?SIE (?FI_I f') - ?SIE (?FO_I f')) =
                ?SUM (incoming v) ?FA"  using augment_inflow_split[OF asm] asm_s by auto
              ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
      qed 
  end
    
  context NFlow
  begin
    lemma augment_flow_presv: "Flow cf s t f' \<Longrightarrow> Flow c s t (augment f')"
      using augment_flow_presv_cap augment_flow_presv_con Flow_def by auto
       
    lemma augment_flow_value: "Flow cf s t f' \<Longrightarrow>  Flow.val cf s f' > 0 \<Longrightarrow>
      Flow.val c s (augment f') = val + Flow.val cf s f'"
      proof -
        assume asm1: "Flow cf s t f'"
        assume asm2: " Flow.val cf s f' > 0"
        let ?S = "{u | u. u \<in> V}"
        let ?S_OE = "{u |u. u \<in> V \<and> (s, u) \<in> E}"
        let ?S_ON = "{u |u. u \<in> V \<and> (s, u) \<notin> E}"
        let ?S_IE = "{u |u. u \<in> V \<and> (u, s) \<in> E}"
        let ?FZ = "\<lambda>u. 0"
        let ?FA = "\<lambda> x. (augment f') x"
        let ?FO = "\<lambda> f x. f (s, x)"
        let ?FO_I = "\<lambda> f x. int (f (s, x))"
        let ?FI = "\<lambda> f x. f (x, s)"
        let ?FI_I = "\<lambda> f x. int (f (x, s))"
        let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
        let ?SUS = "?SUM ?S"
        let ?SOE = "?SUM ?S_OE"
        let ?SON = "?SUM ?S_ON"
        let ?SIE = "?SUM ?S_IE"       
        have "Flow.val c s (augment f') = (?SUM (outgoing s) ?FA) - (?SUM (incoming s) ?FA)"
            using Flow.val_def[OF augment_flow_presv[OF asm1]] by auto
        moreover {
          moreover have "?SUM (outgoing s) ?FA = nat (?SOE (?FO_I f) + ?SOE (?FO_I f') -
            ?SOE (?FI_I f'))" using augment_outflow_split[OF asm1] s_node by auto
          moreover {
            have "NFlow c s t (augment f')" unfolding NFlow_def
              using augment_flow_presv[OF asm1] Network_axioms by auto
            then have "?SUM (incoming s) ?FA = 0"
              using NFlow.no_inflow_s[of c s t "augment f'"] by auto 
          }
          ultimately have "(?SUM (outgoing s) ?FA) - (?SUM (incoming s) ?FA) =
            nat (?SOE (?FO_I f) + ?SOE (?FO_I f') - ?SOE (?FI_I f') - int (?SUM (incoming s) ?FA))"
            by auto
        }
        moreover {
          have "?SUM (incoming s) ?FA = nat (?SIE (?FI_I f) + ?SIE (?FI_I f') -
          ?SIE (?FO_I f'))" using augment_inflow_split[OF asm1] s_node by auto
          moreover {
            have "\<And>u. u \<in> ?S_IE \<Longrightarrow> int (f'(s, u)) \<le> int (f(u, s))" 
              using reverse_flow[OF asm1] by auto
            then have "?SIE (?FO_I f') \<le> ?SIE (?FI_I f)" 
              using setsum_mono[of ?S_IE "?FO_I f'" "?FI_I f"] by auto
            moreover have "0 \<le> ?SIE (?FI_I f)" using setsum_mono[of ?S_IE ?FZ "?FI_I f"] by auto
            moreover have "0 \<le> ?SIE (?FI_I f')" using setsum_mono[of ?S_IE ?FZ "?FI_I f'"] by auto
            moreover have "0 \<le> ?SIE (?FO_I f')" using setsum_mono[of ?S_IE ?FZ "?FO_I f'"] by auto
            ultimately have "?SIE (?FI_I f) + ?SIE (?FI_I f') - ?SIE (?FO_I f') \<ge> 0" 
              (is "?L \<ge> 0") by auto
            then have "int (nat ?L) = ?L" by auto
          }
          ultimately have "int (?SUM (incoming s) ?FA) = ?SIE (?FI_I f) + ?SIE (?FI_I f') -
            ?SIE (?FO_I f')" by auto
        }
        ultimately have "Flow.val c s (augment f') = nat ((?SOE (?FO_I f) - ?SIE (?FI_I f)) + 
          (?SOE (?FO_I f') + ?SIE (?FO_I f')) - (?SOE (?FI_I f') + ?SIE (?FI_I f')))" by auto  
        moreover {
          {
            have "\<And>u. u \<in> ?S_IE \<Longrightarrow> (?FI_I f) u = 0" 
              unfolding E_def using capacity_cons no_parallel_edge
              by (metis no_incoming_s of_nat_0 of_nat_le_0_iff of_nat_le_iff)   
            then have "?SIE (?FI_I f) = 0" by auto
          }
          moreover {
            have "?SOE (?FO_I f) = ?SOE (?FO_I f) + ?SON (?FO_I f) - ?SON (?FO_I f)" by auto
            moreover {
              {
                have f1: "finite ?S_OE" using finite_V by auto
                have f2: "finite ?S_ON" using finite_V by auto
                have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                note setsum.union_disjoint[OF f1 f2 f3]
              } 
              note this[of "?FO_I f"]
              moreover have "?S_OE \<union> ?S_ON = ?S" by auto
              ultimately have "?SOE (?FO_I f) + ?SON (?FO_I f) = ?SUS (?FO_I f)" by auto
            }
            moreover {
              have "\<And>u. u \<in> ?S_ON \<Longrightarrow> (?FO_I f) u = 0" unfolding E_def using capacity_cons
                by (metis (mono_tags, lifting) le_0_eq mem_Collect_eq of_nat_eq_0_iff splitI)
              then have "?SON (?FO_I f) = 0" by auto
            }
            ultimately have "?SOE (?FO_I f) = ?SUS (?FO_I f)" by auto
          }
          ultimately have "?SOE (?FO_I f) - ?SIE (?FI_I f) = ?SUS (?FO_I f)" by auto
          moreover have "?SUS (?FO_I f) = int (?SUS (?FO f))" using Int.int_setsum by metis
          ultimately have "?SOE (?FO_I f) - ?SIE (?FI_I f) = int (?SUS (?FO f))" by auto
        }
        moreover { 
          {
            have f1: "finite ?S_OE" using finite_V by auto
            have f2: "finite ?S_ON" using finite_V by auto
            have f3: "?S_OE \<inter> ?S_ON = {}" by auto
            note setsum.union_disjoint[OF f1 f2 f3]
          }
          note this[of "?FO_I f'"]
          moreover have "?SIE (?FO_I f') = ?SON (?FO_I f')" 
            using augment_res_outflow_alt[OF asm1] s_node by auto
          moreover have "?S_OE \<union> ?S_ON = ?S" by auto
          moreover have "?SUS (?FO_I f') = int (?SUS (?FO f'))" using Int.int_setsum by metis
          ultimately have "?SOE (?FO_I f') + ?SIE (?FO_I f') = int (?SUS (?FO f'))" by auto
        }
        moreover { 
          {
            have f1: "finite ?S_OE" using finite_V by auto
            have f2: "finite ?S_ON" using finite_V by auto
            have f3: "?S_OE \<inter> ?S_ON = {}" by auto
            note setsum.union_disjoint[OF f1 f2 f3]
          }
          note this[of "?FI_I f'"]
          moreover have "?SIE (?FI_I f') = ?SON (?FI_I f')" 
            using augment_res_inflow_alt[OF asm1] s_node by auto
          moreover have "?S_OE \<union> ?S_ON = ?S" by auto
          moreover have "?SUS (?FI_I f') = int (?SUS (?FI f'))" using Int.int_setsum by metis
          ultimately have "?SOE (?FI_I f') + ?SIE (?FI_I f') = int (?SUS (?FI f'))" by auto
        }
        ultimately have "Flow.val c s (augment f') = nat (int (?SUS (?FO f)) + 
          int (?SUS (?FO f')) - int (?SUS (?FI f')))" by auto   
        moreover {
          have "int (?SUS (?FO f)) = int val" using finite_V sum_outgoing_alt[of f] capacity_cons
            val_alt s_node by auto
          moreover {
            {
              have f1: "finite (Graph.V cf)" using finite_V resV_netV by auto
              have f2: "\<forall>e. f' e \<le> cf e" using asm1 Flow_def by auto
              note Graph.sum_outgoing_alt[OF f1 f2]
              then have "?SUM (Graph.outgoing cf s) f' = ?SUS (?FO f')" 
                using asm1 Flow_def s_node resV_netV by auto
            }
            moreover {
              have f1: "finite (Graph.V cf)" using finite_V resV_netV by auto
              have f2: "\<forall>e. f' e \<le> cf e" using asm1 Flow_def by auto
              note Graph.sum_incoming_alt[OF f1 f2]
              then have "?SUM (Graph.incoming cf s) f' = ?SUS (?FI f')" 
                using asm1 Flow_def s_node resV_netV by auto
            }
            moreover note Flow.val_def[OF asm1]
            ultimately have "int (?SUS (?FO f')) - int (?SUS (?FI f')) = 
              int (Flow.val cf s f')" using asm2 by auto
          }
          ultimately have
            "int (?SUS (?FO f)) + int (?SUS (?FO f')) - int (?SUS (?FI f')) = 
              int (val + Flow.val cf s f')" by auto
        }
        ultimately show ?thesis by auto
      qed      
  end
  
end