theory Network
imports Graph
begin



  (* Network definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  locale Network = Graph c for c :: "'capacity::linordered_idom graph" +
    fixes s t :: node
    assumes s_node: "s \<in> V"
    assumes t_node: "t \<in> V"
    assumes s_not_t: "s \<noteq> t"
    assumes cap_positive: "\<forall>u v. c (u, v) \<ge> 0"
    assumes no_self_loop: "\<forall>u. (u, u) \<notin> E"      (* TODO: Implied by no_parallel_edge! *)
    assumes no_incoming_s: "\<forall>u. (u, s) \<notin> E"
    assumes no_outgoing_t: "\<forall>u. (t, u) \<notin> E"
    assumes no_parallel_edge: "\<forall>u v. (u, v) \<in> E \<longrightarrow> (v, u) \<notin> E"
    assumes nodes_on_st_path: "\<forall>v \<in> V. connected s v \<and> connected v t"
    assumes finite_reachable: "finite (reachableNodes s)"
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Flow definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  locale NFlow = Network c s t + Flow c s t f for c :: "'capacity::linordered_idom graph" and s t f
    
  definition (in Network) isMaxFlow :: "_ flow \<Rightarrow> bool" 
  where "isMaxFlow f \<equiv> NFlow c s t f \<and> 
    (\<forall>f'. NFlow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* s-t Cut definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  locale NCut = Network c s t + Cut c k for c :: "'capacity::linordered_idom graph" and s t k +
    assumes s_in_cut: "s \<in> k"
    assumes t_ni_cut: "t \<notin> k"
  begin
    definition cap :: "'capacity"
    where "cap \<equiv> (\<Sum>e \<in> outgoing' k. c e)"
  end
 
  abbreviation (in Graph_Syntax) NCut_cap :: "'capacity::linordered_idom graph \<Rightarrow> node set \<Rightarrow> 'capacity"
    ("\<lbrace>_/ \<parallel>\<^sub>N\<^sub>C/ Cap/ (_)\<rbrace>" 1000) 
  where "\<lbrace>c \<parallel>\<^sub>N\<^sub>C Cap k\<rbrace> \<equiv> NCut.cap c k"
  
  definition isMinCut :: "_ graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cut \<Rightarrow> bool" 
  where "isMinCut c s t k \<equiv> NCut c s t k \<and>
    (\<forall>k'. NCut c s t k' \<longrightarrow> NCut.cap c k \<le> NCut.cap c k')"
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* FoFu definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  locale FoFu = NCut c s t k + NFlow c s t f for c :: "'capacity::linordered_idom graph" and s t k f 
  begin  
    definition netFlow :: "'capacity"
    where "netFlow \<equiv> (\<Sum>e \<in> outgoing' k. f e) - (\<Sum>e \<in> incoming' k. f e)"
  end
  
  abbreviation (in Graph_Syntax) FoFu_netFlow :: "_ graph \<Rightarrow> cut \<Rightarrow> _ flow \<Rightarrow> _"
    ("\<lbrace>_/ \<parallel>\<^sub>F\<^sub>F/ _/ \<Join>/ _\<rbrace>" 1000)
  where "\<lbrace>c \<parallel>\<^sub>F\<^sub>F k \<Join> f\<rbrace> \<equiv> FoFu.netFlow c k f"
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Network lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Network
  begin
    lemma V_ss_reachable : "V \<subseteq> reachableNodes s"
      proof
        fix x
        assume "x \<in> V"
        thus "x \<in> reachableNodes s"
          unfolding reachableNodes_def by (simp add: s_node nodes_on_st_path)
      qed
    
    lemma reachable_is_V[simp]: "reachableNodes s = V"
      using s_node reachable_ss_V V_ss_reachable by blast
      
    lemma finite_V[simp, intro!]: "finite V"
      using reachable_is_V finite_reachable by auto
      
    lemma finite_E[simp]: "finite E"
      proof -
        have "finite (V \<times> V)" using finite_V by auto
        moreover have "E \<subseteq> V \<times> V" using V_def by auto
        ultimately show ?thesis by (metis finite_subset)
      qed
      
    lemma edges_positive: "e \<in> E \<Longrightarrow> c e > 0"
      unfolding E_def using cap_positive le_neq_trans by fastforce 

  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)  
  
  
  
  
  (* s-t Flow lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow 
  begin      
    lemma no_inflow_s: "\<forall>e \<in> incoming s. f e = 0" (is ?thesis)
      proof (rule ccontr)
        assume "\<not>(\<forall>e \<in> incoming s. f e = 0)"
        then obtain e where obt1: "e \<in> incoming s \<and> f e \<noteq> 0" by blast
        then have "e \<in> E" using incoming_def by auto
        thus "False" using obt1 no_incoming_s incoming_def by auto
      qed
      
    lemma no_outflow_t: "\<forall>e \<in> outgoing t. f e = 0"
      proof (rule ccontr)
        assume "\<not>(\<forall>e \<in> outgoing t. f e = 0)"
        then obtain e where obt1: "e \<in> outgoing t \<and> f e \<noteq> 0" by blast
        then have "e \<in> E" using outgoing_def by auto
        thus "False" using obt1 no_outgoing_t outgoing_def by auto
      qed
      
    lemma val_alt: "val = (\<Sum>e \<in> outgoing s. f e)"
      unfolding val_def by (auto simp: no_inflow_s)
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
    
  (* FoFu lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context FoFu
  begin      
    lemma flow_value: "netFlow = val"
      proof -
        let ?LCL = "{(u, v) | u v. u \<in> k \<and> v \<in> k \<and> (u, v) \<in> E}"
        let ?AOG = "{(u, v) | u v. u \<in> k \<and> (u, v) \<in> E}"
        let ?AIN = "{(v, u) | u v. u \<in> k \<and> (v, u) \<in> E}"
        let ?SOG = "\<lambda>u. (\<Sum>e \<in> outgoing u. f e)"
        let ?SIN = "\<lambda>u. (\<Sum>e \<in> incoming u. f e)"
        let ?SOG' = "(\<Sum>e \<in> outgoing' k. f e)"
        let ?SIN' = "(\<Sum>e \<in> incoming' k. f e)"

        have fct1: "netFlow =  ?SOG' + (\<Sum>e \<in> ?LCL. f e) - (?SIN' + (\<Sum>e \<in> ?LCL. f e))" 
          (is "_  = ?SAOG - (?SAIN)") using netFlow_def by auto
        {
          {
            note f = setsum.union_disjoint[of ?LCL "(outgoing' k)" f]
            have "?LCL \<subseteq> E" by auto
            then have f1: "finite ?LCL" using finite_subset[of ?LCL E] finite_E by auto
            have "(outgoing' k) \<subseteq> E" unfolding outgoing'_def by auto
            then have f2: "finite (outgoing' k)"
              using finite_subset[of "(outgoing' k)" E] finite_E by auto
            then have f3: "?LCL \<inter> outgoing' k = {}" unfolding outgoing'_def by auto
            have "?SAOG = (\<Sum>e \<in> ?LCL \<union> (outgoing' k). f e)" 
              using f[OF f1 f2 f3] by auto
            moreover have "?LCL \<union> (outgoing' k) = ?AOG" unfolding outgoing'_def by auto
            ultimately have "?SAOG = (\<Sum>e \<in> ?AOG. f e)" by simp
          } note fct1 = this 
          {
            note f = setsumExt.decomp_2[of k Pair "\<lambda>y a. (y, a) \<in> E" f]
            have f1: "finite k" using cut_ss_V finite_V finite_subset[of k V] by blast
            have "{(y, a) |y a. (y, a) \<in> E} \<subseteq> E" by force
            then have f2: "finite {(y, a) |y a. (y, a) \<in> E}" (is "finite ?TMP")
              using finite_subset[of ?TMP E] finite_E by blast
            have f3: "\<forall>x y a b. x \<noteq> y \<longrightarrow> (x, a) \<noteq> (y, b)" by simp
            have "(\<Sum>e \<in> ?AOG. f e) = (\<Sum>y \<in> k. (\<Sum>x \<in> outgoing y. f x))"
              using f[OF f1 f2 f3] outgoing_def by auto
          } note fct2 = this
          {
            note f = setsumExt.decomp_1[of "k - {s}" s ?SOG]
            have f1: "finite (k - {s})"
              using cut_ss_V finite_V finite_subset[of "k - {s}" V] by blast
            have f2: "s \<notin> k - {s}" by blast
            have "(\<Sum>y \<in> k - {s} \<union> {s}. ?SOG y) = (\<Sum>y \<in> k - {s}. ?SOG y) + (\<Sum>y \<in> {s}. ?SOG y)"
              using f[OF f1 f2] by auto
            moreover have "k - {s} \<union> {s} = k" using s_in_cut by force
            ultimately have "(\<Sum>y \<in> k. ?SOG y) = (\<Sum>y \<in> k - {s}. ?SOG y) + ?SOG s" by auto
          } note fct3 = this
          have "?SAOG = (\<Sum>y \<in> k - {s}. ?SOG y) + ?SOG s" using fct1 fct2 fct3 by simp
        } note fct2 = this
        {
          {
            note f = setsum.union_disjoint[of ?LCL "(incoming' k)" f]
            have "?LCL \<subseteq> E" by auto
            then have f1: "finite ?LCL" using finite_subset[of ?LCL E] finite_E by auto
            have "(incoming' k) \<subseteq> E" unfolding incoming'_def by auto
            then have f2: "finite (incoming' k)"
              using finite_subset[of "(incoming' k)" E] finite_E by auto
            then have f3: "?LCL \<inter> incoming' k = {}" unfolding incoming'_def by auto
            have "?SAIN = (\<Sum>e \<in> ?LCL \<union> (incoming' k). f e)" 
              using f[OF f1 f2 f3] by auto
            moreover have "?LCL \<union> (incoming' k) = ?AIN" unfolding incoming'_def by auto
            ultimately have "?SAIN = (\<Sum>e \<in> ?AIN. f e)" by simp
          } note fct1 = this 
          {
            note f = setsumExt.decomp_2[of k "\<lambda>y a. Pair a y" "\<lambda>y a. (a, y) \<in> E" f]
            have f1: "finite k" using cut_ss_V finite_V finite_subset[of k V] by blast
            have "{(a, y) |y a. (a, y) \<in> E} \<subseteq> E" by force
            then have f2: "finite {(a, y) |y a. (a, y) \<in> E}" (is "finite ?TMP")
              using finite_subset[of ?TMP E] finite_E by blast
            have f3: "\<forall>x y a b. x \<noteq> y \<longrightarrow> (a, x) \<noteq> (b, y)" by simp
            have "(\<Sum>e \<in> ?AIN. f e) = (\<Sum>y \<in> k. (\<Sum>x \<in> incoming y. f x))"
              using f[OF f1 f2 f3] incoming_def by auto
          } note fct2 = this
          {
            note f = setsumExt.decomp_1[of "k - {s}" s ?SIN]
            have f1: "finite (k - {s})" 
              using cut_ss_V finite_V finite_subset[of "k - {s}" V] by blast
            have f2: "s \<notin> k - {s}" by blast
            have "(\<Sum>y \<in> k - {s} \<union> {s}. ?SIN y) = (\<Sum>y \<in> k - {s}. ?SIN y) + (\<Sum>y \<in> {s}. ?SIN y)"
              using f[OF f1 f2] by auto
            moreover have "k - {s} \<union> {s} = k" using s_in_cut by force
            ultimately have "(\<Sum>y \<in> k. ?SIN y) = (\<Sum>y \<in> k - {s}. ?SIN y) + ?SIN s" by auto
          } note fct3 = this
          have "?SAIN = (\<Sum>y \<in> k - {s}. ?SIN y) + ?SIN s" using fct1 fct2 fct3 by simp
        } note fct3 = this 
        have "netFlow =  ((\<Sum>y \<in> k - {s}. ?SOG y) + ?SOG s) - ((\<Sum>y \<in> k - {s}. ?SIN y) + ?SIN s)"
           (is "_ = ?R") using fct1 fct2 fct3 by auto
        moreover have "?R = ?SOG s - ?SIN s"
          proof -
            note f = setsum.cong[of "k - {s}" "k - {s}" ?SOG ?SIN]
            have f1: "k - {s} = k - {s}" by blast
            have f2: "(\<And>u. u \<in> k - {s} \<Longrightarrow> ?SOG u = ?SIN u)" 
              using conservation_const cut_ss_V t_ni_cut by force
            have "(\<Sum>y \<in> k - {s}. ?SOG y) = (\<Sum>y \<in> k - {s}. ?SIN y)" using f[OF f1 f2] by blast
            thus ?thesis by auto
          qed
        ultimately show ?thesis unfolding val_def by simp
      qed
      
    lemma weak_duality: "val \<le> cap"
      proof -
        have "(\<Sum>e \<in> outgoing' k. f e) \<le> (\<Sum>e \<in> outgoing' k. c e)" (is "?L \<le> ?R") 
          using capacity_const by (metis setsum_mono)
        then have "(\<Sum>e \<in> outgoing' k. f e) \<le> cap" unfolding cap_def  by simp
        moreover have "val \<le> (\<Sum>e \<in> outgoing' k. f e)" using netFlow_def
          by (simp add: capacity_const flow_value setsum_nonneg)
        ultimately show ?thesis by simp
      qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* s-t Flow extra lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context NFlow
  begin
    lemma inflow_t_outflow_s: "(\<Sum>e \<in> incoming t. f e) = (\<Sum>e \<in> outgoing s. f e)"
      proof -
        let ?K = "V - {t}"
        have "Network c s t" using NFlow_def NFlow_axioms by auto
        then have "NCut c s t ?K"
          unfolding NCut_def Cut_def NCut_axioms_def using s_node t_node s_not_t by auto
        then have fct: "FoFu c s t ?K f" unfolding FoFu_def using NFlow_axioms by auto
        {
          have "FoFu.netFlow c ?K f = (\<Sum>e \<in> outgoing' ?K. f e) - (\<Sum>e \<in> incoming' ?K. f e)"
            using FoFu.netFlow_def[OF fct] by blast 
          moreover have "FoFu.netFlow c ?K f = val" using FoFu.flow_value[OF fct] by blast
          moreover have "outgoing' ?K = incoming t"
            unfolding outgoing'_def incoming_def V_def using no_self_loop by auto
          moreover have "incoming' ?K = outgoing t"
            unfolding incoming'_def outgoing_def V_def using no_self_loop by auto
          ultimately have "val = (\<Sum>e \<in> incoming t. f e) - (\<Sum>e \<in> outgoing t. f e)" by auto
        }
        thus ?thesis unfolding val_def using no_inflow_s no_outflow_t by auto 
      qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
end