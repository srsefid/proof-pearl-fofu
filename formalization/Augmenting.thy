theory Augmenting
imports ResidualGraph Refine_Util
begin
  text \<open>
    In this theory, we define the concept of an augmenting flow,
    augmentation with a flow, and show that augmentation of a flow 
    with an augmenting flow yields a valid flow again.
    \<close>



  (* Augment definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    (* TODO: Define in network locale, with \<up> syntax. *)
    definition augment :: "'capacity flow \<Rightarrow> 'capacity flow"
    where "augment f' \<equiv> \<lambda>(u, v).
      if (u, v) \<in> E then
        f (u, v) + f' (u, v) - f' (v, u)
      else
        0"
  end

  notation (in NFlow_Loc_Syntax) augment ("\<langle>\<up>/ _\<rangle>" 1000)
    

  abbreviation (in Graph_Syntax) NFlow_augment :: "_ graph \<Rightarrow> _ flow \<Rightarrow> _ flow \<Rightarrow> _ flow"
    ("\<lbrace>_/ \<parallel>\<^sub>N\<^sub>F/ \<langle>_/ \<up>/ _\<rangle>\<rbrace>" 1000)
  where "\<lbrace>c \<parallel>\<^sub>N\<^sub>F \<langle>f \<up> f'\<rangle>\<rbrace> \<equiv> NFlow.augment c f f'"
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Augment flow-capacity lemma *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin

    context 
      -- \<open>Let $f'$ be a flow in $cf$\<close>
      fixes f'
      assumes f'_flow: "Flow cf s t f'"
    begin  
      interpretation f'!: Flow cf s t f' by (rule f'_flow)

      (* TODO: Define augment in Network, with two flows as arguments *)
      abbreviation (input) augment_syntax (infix "\<up>" 55) where "augment_syntax \<equiv> NFlow.augment c"

(* FIXME: Indentation unfortunate, but required to extract snippet for latex presentation *)    
text_raw \<open>\DefineSnippet{augment_flow_presv_cap}{\<close>  
lemma augment_flow_presv_cap: 
  shows "0 \<le> (f\<up>f')(u,v) \<and> (f\<up>f')(u,v) \<le> c(u,v)"
proof (cases "(u,v)\<in>E"; rule conjI) 
  assume [simp]: "(u,v)\<in>E"
  hence "f(u,v) = cf(v,u)" 
    using no_parallel_edge by (auto simp: residualGraph_def)
  also have "cf(v,u) \<ge> f'(v,u)" using f'.capacity_const by auto
  finally(*<*)(xtrans)(*>*) have "f'(v,u) \<le> f(u,v)" .

(*<*){
    note [trans] = xtrans
  (*>*)text_raw \<open>\isanewline\<close>

  text_raw \<open>\ \ \<close>have "(f\<up>f')(u,v) = f(u,v) + f'(u,v) - f'(v,u)"
    by (auto simp: augment_def)
  also have "\<dots> \<ge> f(u,v) + f'(u,v) - f(u,v)"
  (*<*)(is "_ \<ge> \<dots>")(*>*)  using \<open>f'(v,u) \<le> f(u,v)\<close> by auto
  also have "\<dots> = f'(u,v)" by auto
  also have "\<dots> \<ge> 0" using f'.capacity_const by auto
  finally show "(f\<up>f')(u,v) \<ge> 0" .
  (*<*)}(*>*)
    
  have "(f\<up>f')(u,v) = f(u,v) + f'(u,v) - f'(v,u)" 
    by (auto simp: augment_def)
  also have "\<dots> \<le> f(u,v) + f'(u,v)" using f'.capacity_const by auto
  also have "\<dots> \<le> f(u,v) + cf(u,v)" using f'.capacity_const by auto
  also have "\<dots> = f(u,v) + c(u,v) - f(u,v)" 
    by (auto simp: residualGraph_def)
  also have "\<dots> = c(u,v)" by auto
  finally show "(f\<up>f')(u, v) \<le> c(u, v)" .
qed (auto simp: augment_def cap_positive)
text_raw \<open>}%EndSnippet\<close>

    end  
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Augment auxiliary lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    (* TODO: Clean up! *)
    lemma augment_outflow_split: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V. (\<Sum>e \<in> outgoing v. augment f' e) =
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. f (v, e)) + 
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. f' (v, e))-
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. f' (e, v))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e \<in> outgoing v. augment f' e) = 
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. f (v, e)) +
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. f' (v, e))-
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<in> E}. f' (e, v))"
            proof -
              let ?S = "{u | u. u \<in> V}"
              let ?S_OE = "{u |u. u \<in> V \<and> (v, u) \<in> E}"
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?FA = "\<lambda> x. (augment f') x"
              let ?FF = "\<lambda> (u, v). f' (u, v) - f' (v, u)"
              let ?FE = "\<lambda> (u, v). f (u, v) + (f' (u, v) - f' (v, u))"
              let ?FO = "\<lambda> f x. f (v, x)"
              let ?FI = "\<lambda> f x. f (x, v)"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SUS = "?SUM ?S"
              let ?SOE = "?SUM ?S_OE"
              let ?SON = "?SUM ?S_ON"
              {
                have "?SUM (outgoing v) ?FA = ?SUS (?FO (augment f'))" using 
                  sum_outgoing_alt[OF finite_V] augment_flow_presv_cap[OF asm] asm_s by auto
              }
              moreover {
                {
                  have f1: "finite ?S_OE" using finite_V by auto
                  have f2: "finite ?S_ON" using finite_V by auto
                  have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FO ?FA"]
                moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                ultimately have "?SUS (?FO ?FA) = ?SOE (?FO ?FA) + ?SON (?FO ?FA)" by auto
                moreover {
                  have "\<And>u. u \<in> ?S_ON \<Longrightarrow> (?FO ?FA) u = 0" unfolding augment_def by auto
                  then have "?SON (?FO ?FA) = 0" by auto
                } 
                ultimately have "?SUS (?FO ?FA) = ?SOE (?FO ?FA)" by auto 
              }
              moreover {
                {
                  have "?SOE (?FO ?FA) = ?SOE (?FO ?FE)" unfolding augment_def
                    by (rule setsum.cong[OF refl]) auto
                  moreover have "\<And>u. u \<in> ?S_OE \<Longrightarrow> ?FO ?FE u = ?FO ?FE u" by auto
                  ultimately have "?SOE (?FO ?FA) = ?SOE (?FO ?FE)" by auto
                }
                moreover {
                  note setsum.distrib[of "?FO f" "?FO ?FF" ?S_OE]
                  then have "?SOE (?FO ?FE) = ?SOE (?FO f) + ?SOE (?FO ?FF)" by auto
                }
                moreover {
                  note setsum_subtractf[of "?FO f'" "?FI f'" ?S_OE]
                  then have "?SOE (?FO ?FF) = ?SOE (?FO f') - ?SOE (?FI f')" by auto
                }
                ultimately have "?SOE (?FO ?FA) =
                  ?SOE (?FO f) + ?SOE (?FO f') - ?SOE (?FI f')" by auto 
              }
              ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
      qed
     
    lemma augment_inflow_split: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V. (\<Sum>e \<in> incoming v. augment f' e) =
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f (e, v)) +
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (e, v))-
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (v, e))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e \<in> incoming v. augment f' e) = 
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f (e, v)) +
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (e, v))-
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (v, e))"
            proof -
              let ?S = "{u | u. u \<in> V}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_IN = "{u |u. u \<in> V \<and> (u, v) \<notin> E}"
              let ?FA = "\<lambda> x. (augment f') x"
              let ?FF = "\<lambda> (u, v). f' (u, v) - f' (v, u)"
              let ?FE = "\<lambda> (u, v). f (u, v) + (f' (u, v) - f' (v, u))"
              let ?FO = "\<lambda> f x. f (v, x)"
              let ?FI = "\<lambda> f x. f (x, v)"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SUS = "?SUM ?S"
              let ?SIE = "?SUM ?S_IE"
              let ?SIN = "?SUM ?S_IN"
              {
                have "?SUM (incoming v) ?FA = ?SUS (?FI (augment f'))" using 
                  sum_incoming_alt[OF finite_V] augment_flow_presv_cap[OF asm] asm_s by auto
              }
              moreover {
                {
                  have f1: "finite ?S_IE" using finite_V by auto
                  have f2: "finite ?S_IN" using finite_V by auto
                  have f3: "?S_IE \<inter> ?S_IN = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FI ?FA"]
                moreover have "?S_IE \<union> ?S_IN = ?S" by auto
                ultimately have "?SUS (?FI ?FA) = ?SIE (?FI ?FA) + ?SIN (?FI ?FA)" by auto
                moreover {
                  have "\<And>u. u \<in> ?S_IN \<Longrightarrow> (?FI ?FA) u = 0" unfolding augment_def by auto
                  then have "?SIN (?FI ?FA) = 0" by auto
                } 
                ultimately have "?SUS (?FI ?FA) = ?SIE (?FI ?FA)" by auto 
              }
              moreover {
                {
                  have "?SIE (?FI ?FA) = ?SIE (?FI ?FE)" unfolding augment_def
                    by (rule setsum.cong[OF refl]) auto
                  moreover have "\<And>u. u \<in> ?S_IE \<Longrightarrow> ?FI ?FE u = ?FI ?FE u"
                    using reverse_flow[OF asm] by auto
                  ultimately have "?SIE (?FI ?FA) = ?SIE (?FI ?FE)" by auto
                }
                moreover {
                  note setsum.distrib[of "?FI f" "?FI ?FF" ?S_IE]
                  then have "?SIE (?FI ?FE) = ?SIE (?FI f) + ?SIE (?FI ?FF)" by auto
                }
                moreover {
                  note setsum_subtractf[of "?FI f'" "?FO f'" ?S_IE]
                  then have "?SIE (?FI ?FF) = ?SIE (?FI f') - ?SIE (?FO f')" by auto
                }
                ultimately have "?SIE (?FI ?FA) =
                  ?SIE (?FI f) + ?SIE (?FI f') - ?SIE (?FO f')" by auto 
              }
              ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
      qed
  
    lemma augment_res_inflow_alt: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V.
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (e, v)) =
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. f' (e, v))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (e, v)) =
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. f' (e, v))"
            proof -
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_NN = "{u |u. u \<in> V \<and> (u, v) \<notin> E \<and> (v, u) \<notin> E}"
              let ?FI = "\<lambda> f x. f (x, v)"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SON = "?SUM ?S_ON"
              let ?SIE = "?SUM ?S_IE"
              let ?SNN = "?SUM ?S_NN" 
              have "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FI f') u = 0"
                proof -
                  {
                    fix u
                    assume "u \<in> ?S_NN"
                    then have "(u, v) \<notin> E \<and> (v, u) \<notin> E" by auto
                    then have f1: "cf (u, v) = 0" and f2: "cf (v, u) = 0"
                      unfolding residualGraph_def by (auto simp: )
                    have "f' (u, v) = 0" using f1
                      Flow.capacity_const[OF asm] by (metis (no_types) antisym)
                    moreover have "f' (v, u) = 0" using f2
                      Flow.capacity_const[OF asm] by (metis (no_types) antisym)
                    ultimately have "f' (u, v) = 0 \<and> f' (v, u) = 0" by simp 
                    then have "(?FI f') u = 0" by auto
                  }
                  then show "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FI f') u = 0" by auto
                qed
              moreover {
                {
                  have f1: "finite ?S_IE" using finite_V by auto
                  have f2: "finite ?S_NN" using finite_V by auto
                  have f3: "?S_IE \<inter> ?S_NN = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FI f'"]
                moreover have "?S_IE \<union> ?S_NN = ?S_ON" using no_parallel_edge asm by auto
                ultimately have "?SON (?FI f') = ?SIE (?FI f') + ?SNN (?FI f')" by auto                  
              }
              ultimately show "?SIE (?FI f') = ?SON (?FI f')" by auto
            qed
        }
        thus ?thesis by auto
      qed 
     
    lemma augment_res_outflow_alt: "Flow cf s t f' \<Longrightarrow> \<forall>v \<in> V.
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (v, e)) =
      (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. f' (v, e))"
      proof -
        assume asm: "Flow cf s t f'"
        {
          fix v
          assume asm_s: "v \<in> V"
          have "(\<Sum>e\<in>{u |u. u \<in> V \<and> (u, v) \<in> E}. f' (v, e)) =
            (\<Sum>e\<in>{u |u. u \<in> V \<and> (v, u) \<notin> E}. f' (v, e))"
            proof -
              let ?S_ON = "{u |u. u \<in> V \<and> (v, u) \<notin> E}"
              let ?S_IE = "{u |u. u \<in> V \<and> (u, v) \<in> E}"
              let ?S_NN = "{u |u. u \<in> V \<and> (u, v) \<notin> E \<and> (v, u) \<notin> E}"
              let ?FO = "\<lambda> f x. f (v, x)"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SON = "?SUM ?S_ON"
              let ?SIE = "?SUM ?S_IE"
              let ?SNN = "?SUM ?S_NN" 
              have "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FO f') u = 0"
                proof -
                  {
                    fix u
                    assume "u \<in> ?S_NN"
                    then have "(u, v) \<notin> E \<and> (v, u) \<notin> E" by auto
                    then have f1: "cf (u, v) = 0" and f2: "cf (v, u) = 0"
                      unfolding residualGraph_def by auto
                    have "f' (u, v) = 0" using f1
                      Flow.capacity_const[OF asm] by (metis (no_types) antisym)
                    moreover have "f' (v, u) = 0" using f2
                      Flow.capacity_const[OF asm] by (metis (no_types) antisym)
                    ultimately have "f' (u, v) = 0 \<and> f' (v, u) = 0" by simp 
                    then have "(?FO f') u = 0" by auto
                  }
                  then show "\<And>u. u \<in> ?S_NN \<Longrightarrow> (?FO f') u = 0" by auto
                qed
              moreover {
                {
                  have f1: "finite ?S_IE" using finite_V by auto
                  have f2: "finite ?S_NN" using finite_V by auto
                  have f3: "?S_IE \<inter> ?S_NN = {}" by auto
                  note setsum.union_disjoint[OF f1 f2 f3]
                }
                note this[of "?FO f'"]
                moreover have "?S_IE \<union> ?S_NN = ?S_ON" using no_parallel_edge asm by auto
                ultimately have "?SON (?FO f') = ?SIE (?FO f') + ?SNN (?FO f')" by auto                  
              }
              ultimately show "?SIE (?FO f') = ?SON (?FO f')" by auto
            qed
        }
        thus ?thesis by auto
      qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  (* Augment flow-conservation lemma *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    lemma augment_flow_presv_con: "Flow cf s t f' \<Longrightarrow> 
      \<forall>v \<in> V - {s, t}. (\<Sum>e \<in> outgoing v. augment f' e) = (\<Sum>e \<in> incoming v. augment f' e)"
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
              let ?FE = "\<lambda> (u, v). f (u, v) + f' (u, v) - f' (v, u)"
              let ?FO = "\<lambda> f x. f (v, x)"
              let ?FI = "\<lambda> f x. f (x, v)"
              let ?SUM = "\<lambda> S f. (\<Sum>e \<in> S. f e)"
              let ?SUS = "?SUM ?S"
              let ?SOE = "?SUM ?S_OE"
              let ?SON = "?SUM ?S_ON"
              let ?SIE = "?SUM ?S_IE"
              let ?SIN = "?SUM ?S_IN"
              let ?SNN = "?SUM ?S_NN"
              have "?SUM (outgoing v) ?FA = ?SOE (?FO f) + ?SOE (?FO f') -
                ?SOE (?FI f')" using augment_outflow_split[OF asm] asm_s by auto
              moreover {
                have "?SOE (?FO f) = ?SOE (?FO f) + ?SON (?FO f) - ?SON (?FO f)" by auto
                moreover {
                  {
                    have f1: "finite ?S_OE" using finite_V by auto
                    have f2: "finite ?S_ON" using finite_V by auto
                    have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  } 
                  note this[of "?FO f"]
                  moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                  ultimately have "?SOE (?FO f) + ?SON (?FO f) = ?SUS (?FO f)" by auto
                }
                moreover {
                  have "?SUS (?FO f) = ?SUM (outgoing v) f"
                    using sum_outgoing_alt[OF finite_V] capacity_const asm_s by auto
                  moreover have "?SUM (outgoing v) f = ?SUM (incoming v) f" 
                    using asm_s conservation_const by auto  
                  moreover have "?SUM (incoming v) f = ?SUS (?FI f)"
                    using sum_incoming_alt[OF finite_V] capacity_const asm_s by auto
                  ultimately have "?SUS (?FO f) = ?SUS (?FI f)" by auto
                }
                moreover {
                  {
                    have f1: "finite ?S_IE" using finite_V by auto
                    have f2: "finite ?S_IN" using finite_V by auto
                    have f3: "?S_IE \<inter> ?S_IN = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  }
                  note this[of "?FI f"]
                  moreover have "?S_IE \<union> ?S_IN = ?S" by auto
                  ultimately have "?SUS (?FI f) = ?SIE (?FI f) + ?SIN (?FI f)" by auto
                }
                moreover {
                  have "\<And>u. u \<in> ?S_ON \<Longrightarrow> (?FO f) u = 0" unfolding E_def using capacity_const
                    by (metis (mono_tags, lifting) antisym case_prodI2 mem_Collect_eq)
                  then have "?SON (?FO f) = 0" by auto
                }
                moreover {
                  have "\<And>u. u \<in> ?S_IN \<Longrightarrow> (?FI f) u = 0"
                    unfolding E_def using capacity_const  no_parallel_edge 
                    proof -
                      fix u :: nat
                      assume "u \<in> {u |u. u \<in> V \<and> (u, v) \<notin> {(u, v). c (u, v) \<noteq> 0}}"
                      hence "c (u, v) = 0" by force
                      thus "f (u, v) = 0" using capacity_const leD less_linear by fastforce
                    qed
                  then have "?SIN (?FI f) = 0" by auto
                }
                ultimately have "?SOE (?FO f) = ?SIE(?FI f)" by auto
              }
              moreover {
                have "?SOE (?FO f') = ?SOE (?FO f') + ?SON (?FO f') - ?SON (?FO f')" by auto
                moreover {
                  {
                    have f1: "finite ?S_OE" using finite_V by auto
                    have f2: "finite ?S_ON" using finite_V by auto
                    have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  }
                  note this[of "?FO f'"]
                  moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                  ultimately have "?SOE (?FO f') + ?SON (?FO f') = ?SUS (?FO f')" by auto
                }
                moreover {
                  have f1: "finite (Graph.V cf)" using resV_netV finite_V by auto
                  have f2: "\<forall>e. 0 \<le> f' e \<and> f' e \<le> cf e" using asm[unfolded Flow_def] by auto
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
                    using resV_netV asm_s asm[unfolded Flow_def] by auto
                  ultimately have "?SUS (?FO f') = ?SUS (?FI f')" by auto
                }
                ultimately have "?SOE (?FO f') = ?SUS (?FI f') - ?SON (?FO f')" by auto
              }
              moreover {
                have "?SOE (?FI f') = ?SOE (?FI f') + ?SON (?FI f') - ?SON (?FI f')" by auto
                moreover {
                  {
                    have f1: "finite ?S_OE" using finite_V by auto
                    have f2: "finite ?S_ON" using finite_V by auto
                    have f3: "?S_OE \<inter> ?S_ON = {}" by auto
                    note setsum.union_disjoint[OF f1 f2 f3]
                  }
                  note this[of "?FI f'"]
                  moreover have "?S_OE \<union> ?S_ON = ?S" by auto
                  ultimately have "?SOE (?FI f') + ?SON (?FI f') = ?SUS (?FI f')" by auto
                }
                ultimately have "?SOE (?FI f') = ?SUS (?FI f') - ?SON (?FI f')" by auto
              }
              ultimately have "?SUM (outgoing v) ?FA = 
                ?SIE (?FI f) + ?SON (?FI f') - ?SON (?FO f')" by auto
              moreover have "?SON (?FI f') = ?SIE (?FI f')"
                using augment_res_inflow_alt[OF asm] asm_s by auto
              moreover have "?SON (?FO f') = ?SIE (?FO f')"
                using augment_res_outflow_alt[OF asm] asm_s by auto
              moreover have " ?SIE (?FI f) + ?SIE (?FI f') - ?SIE (?FO f') =
                ?SUM (incoming v) ?FA"  using augment_inflow_split[OF asm] asm_s by auto
              ultimately show ?thesis by auto
            qed
        }
        thus ?thesis by auto
      qed 
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Augment flow preservation and value lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    corollary augment_flow_presv: "Flow cf s t f' \<Longrightarrow> Flow c s t (augment f')"
      using augment_flow_presv_cap augment_flow_presv_con unfolding Flow_def by auto

    lemma zero_rev_flow_simp[simp]: "(u,v)\<in>E \<Longrightarrow> f(v,u) = 0"
      using no_parallel_edge by auto

    lemma augment_flow_value:
      assumes "Flow cf s t f'"
      shows "Flow.val c s (augment f') = val + Flow.val cf s f'"
      -- \<open>The value of the augmented flow matches the original flow value plus
        the value of the augmenting flow.\<close>
    proof -
      interpret f'!: Flow cf s t f' by fact
      interpret f''!: Flow c s t "augment f'" using augment_flow_presv[OF assms] . 

      txt \<open>For this proof, we set up Isabelle's rewriting engine for rewriting of sums.
        In particular, we add lemmas to convert sums over incoming or outgoing 
        edges to sums over all vertices.\<close>
      (*<*)
      note setsum_simp_setup[simp] = 
        sum_outgoing_alt[OF finite_V capacity_const] s_node
        sum_incoming_alt[OF finite_V capacity_const]
        cf.sum_outgoing_alt[OF _ f'.capacity_const]
        cf.sum_incoming_alt[OF _ f'.capacity_const]
        sum_outgoing_alt[OF finite_V f''.capacity_const]
        sum_incoming_alt[OF finite_V f''.capacity_const]
        setsum_subtractf setsum.distrib
      (*>*)  
      
      txt \<open>Note that, if neither an edge nor its reverse is in the graph,
        there is also no edge in the residual graph, and thus the flow value
        is zero.\<close>  
      {
        fix u v
        assume "(u,v)\<notin>E" "(v,u)\<notin>E"
        with cfE_ss_invE have "(u,v)\<notin>cf.E" by auto
        hence "f'(u,v) = 0" by auto
      } note aux1 = this  

      txt \<open>Now, the proposition follows by straightforward rewriting of 
        the summations:\<close>
      have "f''.val = (\<Sum>u\<in>V. augment f' (s, u) - augment f' (u, s))" 
        unfolding f''.val_def by simp
      also have "\<dots> = (\<Sum>u\<in>V. f (s, u) - f (u, s) + (f' (s, u) - f' (u, s)))"
        by (rule setsum.cong) (auto simp: augment_def no_parallel_edge aux1)
      also have "\<dots> = val + Flow.val cf s f'"  
        unfolding val_def f'.val_def by simp
      finally show ?thesis .  

      txt \<open>Note, there is also an automatic proof. When creating the above 
          explicit proof, this automatic one has been used to extract meaningful
          subgoals, abusing Isabelle as a term rewriter.\<close>
      have ?thesis
        unfolding val_def f'.val_def f''.val_def
        apply (simp del: setsum_simp_setup
          add: 
          sum_outgoing_alt[OF finite_V capacity_const] s_node
          sum_incoming_alt[OF finite_V capacity_const]
          sum_outgoing_alt[OF finite_V f''.capacity_const]
          sum_incoming_alt[OF finite_V f''.capacity_const]
          cf.sum_outgoing_alt[OF _ f'.capacity_const]
          cf.sum_incoming_alt[OF _ f'.capacity_const]
          setsum_subtractf[symmetric] setsum.distrib[symmetric]
          )
        apply (fo_rule arg_cong fun_cong)+
        apply (rule ext)
        apply (auto simp: augment_def no_parallel_edge aux1)
        done
    qed    

  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
end
