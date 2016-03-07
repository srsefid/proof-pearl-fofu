theory Graph
imports Fofu_Abs_Base
begin


  (* Graph definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  type_synonym node = nat 
  type_synonym edge = "node \<times> node"
  (*type_synonym capacity = int*)

  (*
  typedecl capacity 
  instance capacity :: linordered_idom sorry
  *)


  type_synonym 'capacity graph = "edge \<Rightarrow> 'capacity"
  
locale Graph = fixes c :: "'capacity::linordered_idom graph"
  begin
    definition E :: "edge set" -- \<open>Edges of the graph\<close>
    where "E \<equiv> {(u, v). c (u, v) \<noteq> 0}"
    
    definition V :: "node set" -- \<open>Nodes of the graph. Exactly the nodes that have adjacent edges.\<close>
    where "V \<equiv> {u. \<exists>v. (u, v) \<in> E \<or> (v, u) \<in> E}"
    
    definition incoming :: "node \<Rightarrow> edge set" -- \<open>Incoming edges into a node\<close>
    where "incoming v \<equiv> {(u, v) | u. (u, v) \<in> E}"
    
    definition outgoing :: "node \<Rightarrow> edge set" -- \<open>Outgoing edges from a node\<close>
    where "outgoing v \<equiv> {(v, u) | u. (v, u) \<in> E}"
      
    definition adjacent :: "node \<Rightarrow> edge set" -- \<open>Adjacent edges of a node\<close>
    where "adjacent v \<equiv> incoming v \<union> outgoing v"
    
    definition incoming' :: "node set \<Rightarrow> edge set" -- \<open>Incoming edges into a set of nodes\<close>
    where "incoming' k \<equiv> {(u, v) | u v. u \<notin> k \<and> v \<in> k \<and> (u, v) \<in> E}"
      
    definition outgoing' :: "node set \<Rightarrow> edge set" -- \<open>Outgoing edges from a set of nodes\<close>
    where "outgoing' k \<equiv> {(v, u) | u v. u \<notin> k \<and> v \<in> k \<and> (v, u) \<in> E}"
      
    definition adjacent' :: "node set \<Rightarrow> edge set" -- \<open>Edges adjacent to a set of nodes\<close>
    where "adjacent' k \<equiv> incoming' k \<union> outgoing' k"
  end

  (* TODO: Rename to is_adjacency_map, and move to Graph locale! *)
  definition is_pred_succ :: "(node \<Rightarrow> node list) \<Rightarrow> _ graph \<Rightarrow> bool" 
    -- \<open>Predicate to characterize function that returns adjacent nodes\<close>
    where
    "is_pred_succ ps c \<equiv> (\<forall>u. distinct (ps u) \<and> set (ps u) = (Graph.E c)``{u} \<union> (Graph.E c)\<inverse>``{u})"


  locale Graph_Loc_Syntax = Graph
  begin
    notation incoming ("\<delta>\<^sup>+(_)" 1000) 
    notation outgoing ("\<delta>\<^sup>-(_)" 1000)
    notation adjacent ("\<delta>(_)" 1000) 
    notation incoming' ("\<Delta>\<^sup>+(_)" 1000) 
    notation outgoing' ("\<Delta>\<^sup>-(_)" 1000)
    notation adjacent' ("\<Delta>(_)" 1000) 
  end

  locale Graph_Syntax begin
    abbreviation Graph_E :: "'c::linordered_idom graph \<Rightarrow> edge set"
      ("\<lbrace>_/ \<parallel>\<^sub>G/ E\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G E\<rbrace> \<equiv> Graph.E c"
      
    abbreviation Graph_V :: "'c::linordered_idom graph \<Rightarrow> node set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ V\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G V\<rbrace> \<equiv> Graph.V c"
      
    abbreviation Graph_incoming :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<delta>\<^sup>+(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<delta>\<^sup>+ u\<rbrace> \<equiv> Graph.incoming c u"
      
    abbreviation Graph_outgoing :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<delta>\<^sup>-(_)\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<delta>\<^sup>- u\<rbrace> \<equiv> Graph.outgoing c u"
      
    abbreviation Graph_delta :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> edge set"
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<delta>(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<delta> u\<rbrace> \<equiv> Graph.adjacent c u"
      
    abbreviation Graph_incoming' :: "'c::linordered_idom graph \<Rightarrow> node set \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<Delta>\<^sup>+(_)\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<Delta>\<^sup>+ u\<rbrace> \<equiv> Graph.incoming' c u"  
    
    abbreviation Graph_outgoing' :: "'c::linordered_idom graph \<Rightarrow> node set \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<Delta>\<^sup>-(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<Delta>\<^sup>- u\<rbrace> \<equiv> Graph.outgoing' c u"
      
    abbreviation Graph_delta' :: "'c::linordered_idom graph \<Rightarrow> node set \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<Delta>(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<Delta> u\<rbrace> \<equiv> Graph.adjacent' c u"
    (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
    (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
    (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  end  
  
  locale Finite_Graph = Graph +
    assumes finite_V[simp, intro!]: "finite V"

  
  (* Path definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  type_synonym path = "edge list"
  
  context Graph
  begin
    fun isPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where
      "isPath u [] v \<longleftrightarrow> u = v"
    | "isPath u ((x,y)#p) v \<longleftrightarrow> u = x \<and> (x, y) \<in> E \<and> isPath y p v"
  
    fun pathVertices :: "node \<Rightarrow> path \<Rightarrow> node list"
    where
      "pathVertices u [] = [u]"
    | "pathVertices u (e # es) = fst e # (pathVertices (snd e) es)"
    
    (* TODO: This characterization is probably nicer to work with! Exchange! *)
    definition (in Graph) pathVertices_fwd :: "node \<Rightarrow> edge list \<Rightarrow> node list" 
      where "pathVertices_fwd u p = u#map snd p"

    lemma (in Graph) pathVertices_fwd: 
      assumes "isPath u p v"
      shows "pathVertices u p = pathVertices_fwd u p"
      unfolding pathVertices_fwd_def
      using assms apply (induction p arbitrary: u)
      by auto


    definition connected :: "node \<Rightarrow> node \<Rightarrow> bool" 
    where "connected u v \<equiv> \<exists>p. isPath u p v" 
    
    abbreviation (input) "isReachable \<equiv> connected" (* Deprecated *)

    definition reachableNodes :: "node \<Rightarrow> node set"  
    where "reachableNodes u \<equiv> {v. connected u v}"
    
    definition isShortestPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where "isShortestPath u p v \<equiv> isPath u p v \<and> (\<forall>p'. isPath u p' v \<longrightarrow> length p \<le> length p')"
        
    definition isSimplePath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where "isSimplePath u p v \<equiv> isPath u p v \<and> distinct (pathVertices u p)"

    definition dist :: "node \<Rightarrow> nat \<Rightarrow> node \<Rightarrow> bool" 
      -- \<open>There is a path of given length between the nodes\<close>
      where "dist v d v' \<equiv> \<exists>p. isPath v p v' \<and> length p = d"

    definition min_dist :: "node \<Rightarrow> node \<Rightarrow> nat"
      -- \<open>Minimum distance between two connected nodes\<close>
      where "min_dist v v' = (LEAST d. dist v d v')"

  end  

  context Graph_Loc_Syntax begin
    notation isPath ("\<langle>\<leadsto>/ _,/ _,/ _\<rangle>"  1000)
    notation connected ("\<langle>_/ \<leadsto>/ _\<rangle>" 1000)
    notation reachableNodes ("\<langle>\<star>/ _\<rangle>" 1000)
    notation isShortestPath ("\<langle>\<rightarrow>/ _,/ _,/ _\<rangle>" 1000) 
    notation isSimplePath ("\<langle>\<Rightarrow>/ _,/ _,/ _\<rangle>" 1000)
  end

  context Graph_Syntax begin  
    abbreviation Graph_isPath :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<leadsto> _, _, _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<leadsto> u, p, v\<rangle>\<rbrace> \<equiv> Graph.isPath c u p v"
      
    abbreviation Graph_connected :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>_/ \<leadsto>/ _\<rangle>\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>u \<leadsto> v\<rangle>\<rbrace> \<equiv> Graph.connected c u v"
      
    abbreviation Graph_reachableNodes :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> node set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<star>/ _\<rangle>\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<star> u\<rangle>\<rbrace> \<equiv> Graph.reachableNodes c u"
      
    abbreviation Graph_isShortestPath :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<rightarrow> _, _, _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<rightarrow> u, p, v\<rangle>\<rbrace> \<equiv> Graph.isShortestPath c u p v"
      
    abbreviation Graph_isSimplePath :: "'c::linordered_idom graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool"
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<Rightarrow> _, _, _\<rangle>\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<Rightarrow> u, p, v\<rangle>\<rbrace> \<equiv> Graph.isSimplePath c u p v"
  end  
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
    
  
  
  
  (* Flow definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  type_synonym 'capacity flow = "edge \<Rightarrow> 'capacity"
  
  locale Flow = Graph c for c :: "'capacity::linordered_idom graph" +
    fixes s t :: node
    fixes f :: "'capacity::linordered_idom flow"
    (* TODO: Move \<forall>-quantifiers to meta-level! *)
    assumes capacity_const: "\<forall>e. 0 \<le> f e \<and> f e \<le> c e"
    assumes conservation_const: "\<forall>v \<in> V - {s, t}. (\<Sum>e \<in> incoming v. f e) = (\<Sum>e \<in> outgoing v. f e)"
  begin
    definition val :: "'capacity"
    where "val \<equiv> (\<Sum>e \<in> outgoing s. f e) - (\<Sum>e \<in> incoming s. f e)"
  end

  context Graph_Syntax begin    
    abbreviation Flow_val :: "'capacity::linordered_idom graph \<Rightarrow> node \<Rightarrow> 'capacity flow \<Rightarrow> 'capacity"
      ("\<lbrace>_,/ _/ \<parallel>\<^sub>F/ |_|\<rbrace>" 1000) 
    where "\<lbrace>c, s \<parallel>\<^sub>F |f|\<rbrace> \<equiv> Flow.val c s f"
  end  
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
    
    
    
  
  (* Cut definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  type_synonym cut = "node set"
  
  locale Cut = Graph +
    fixes k :: cut
    assumes cut_ss_V: "k \<subseteq> V"
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Graph lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin
    lemma V_alt: "V = fst`E \<union> snd`E" unfolding V_def by force
    
    lemma E_ss_VxV: "E \<subseteq> V\<times>V" by (auto simp: V_def)

    lemma Vfin_imp_Efin[simp, intro]: assumes "finite V" shows "finite E"
      using E_ss_VxV assms by (auto intro: finite_subset)

    lemma Efin_imp_Vfin: "finite E \<Longrightarrow> finite V"
      unfolding V_alt by auto

    lemma zero_cap_simp[simp]: "(u,v)\<notin>E \<Longrightarrow> c (u,v) = 0"  
      by (auto simp: E_def)

    lemma sum_outgoing_alt: "\<lbrakk>finite V; \<forall>e. 0 \<le> g e \<and> g e \<le> c e\<rbrakk> \<Longrightarrow>
      \<forall>v \<in> V. (\<Sum>e \<in> outgoing v. g e) = (\<Sum>u \<in> V. g (v, u))"
      proof -
        assume asm1: "finite V"
        assume asm2: "\<forall>e. 0 \<le> g e \<and> g e \<le> c e"
        {
          fix v
          assume "v \<in> V"
          {
            then have "{(v, u) | u. u \<in> V} \<subseteq> V \<times> V" by blast
            then have tmp1: "finite {(v, u) | u. u \<in> V}" using asm1 finite_subset by simp
            have "{(v, u) | u. u \<in> V \<and> (v, u) \<in> E} \<subseteq> {(v, u) | u. u \<in> V}" by blast
            then have f1:"finite {(v, u) | u. u \<in> V \<and> (v, u) \<in> E}" using tmp1 finite_subset by auto
            have "{(v, u) | u. u \<in> V \<and> (v, u) \<notin> E} \<subseteq> {(v, u) | u. u \<in> V}" by blast
            then have f2:"finite {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E}" using tmp1 finite_subset by auto
            have f3: "{(v, u) | u. u \<in> V \<and> (v, u) \<in> E} \<inter> {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E} = {}"
              (is "?S1 \<inter> ?S2 = _") by blast          
            note f = setsum.union_disjoint[of ?S1 ?S2 g]
            have "(\<Sum>e \<in> ?S1 \<union> ?S2. g e) = (\<Sum>e \<in> ?S1. g e) + (\<Sum>e \<in> ?S2. g e)"
              using f[OF f1 f2 f3] by simp
            moreover have "?S1 \<union> ?S2 = {(v, u) | u. u \<in> V}" by force
            ultimately have "(\<Sum>e \<in> {(v, u) | u. u \<in> V}. g e) =
              (\<Sum>e \<in> ?S1. g e) + (\<Sum>e \<in> ?S2. g e)" by simp
          } note fct1 = this
          {
            have "\<And>e. (e \<in> {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E} \<Longrightarrow> g e = 0)"
              proof -
                {
                  fix e
                  assume asm: "e \<in> {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E}"
                  have "g e = 0"
                    proof (rule ccontr)
                      assume "\<not> g e = 0"
                      then have "e \<in> E" using asm2 E_def
                        by (metis (mono_tags, lifting) antisym case_prodI2 mem_Collect_eq) 
                      then have "e \<notin> {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E}" unfolding E_def by auto
                      thus "False" using asm by blast
                    qed
                }
                then show "\<And>e. (e \<in> {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E} \<Longrightarrow> g e = 0)" by simp
              qed
            then have "(\<Sum>e \<in> {(v, u) | u. u \<in> V \<and> (v, u) \<notin> E}. g e) = 0" by auto
          } note fct2 = this
          {
            have "{(v, u) | u. u \<in> V \<and> (v, u) \<in> E} = {(v, u) | u. (v, u) \<in> E}" (is "?L = ?R")
              unfolding V_def E_def by auto
            then have "(\<Sum>e \<in> ?L. g e) = (\<Sum>e \<in> ?R. g e)" by simp
          } note fct3 = this
          have "(\<Sum>e \<in> {(v, u) | u. (v, u) \<in> E}. g e) = (\<Sum>e \<in> {(v, u) | u. u \<in> V}. g e) "
            using fct1 fct2 fct3 by auto
          moreover have "(\<Sum>e \<in> {(v, u) | u. u \<in> V}. g e) = (\<Sum>u \<in> {u | u. u \<in> V}. g (v, u))"
            using setsumExt.decomp_3[of V Pair g v] asm1 by auto
          ultimately have "(\<Sum>e \<in> {(v, u) | u. (v, u) \<in> E}. g e) = 
            (\<Sum>u \<in> {u | u. u \<in> V}. g (v, u))" by auto
        }
        thus ?thesis unfolding outgoing_def by auto
      qed
      
    lemma sum_incoming_alt: "\<lbrakk>finite V; \<forall>e. 0 \<le> g e \<and> g e \<le> c e\<rbrakk> \<Longrightarrow>
      \<forall>v \<in> V. (\<Sum>e \<in> incoming v. g e) = (\<Sum>u \<in> V. g (u, v))"
      proof -
        assume asm1: "finite V"
        assume asm2: "\<forall>e. 0 \<le> g e \<and> g e \<le> c e"
        {
          fix v
          assume "v \<in> V"
          {
            then have "{(u, v) | u. u \<in> V} \<subseteq> V \<times> V" by blast
            then have tmp1: "finite {(u, v) | u. u \<in> V}" using asm1 finite_subset by simp
            have "{(u, v) | u. u \<in> V \<and> (u, v) \<in> E} \<subseteq> {(u, v) | u. u \<in> V}" by blast
            then have f1:"finite {(u, v) | u. u \<in> V \<and> (u, v) \<in> E}" using tmp1 finite_subset by auto
            have "{(u, v) | u. u \<in> V \<and> (u, v) \<notin> E} \<subseteq> {(u, v) | u. u \<in> V}" by blast
            then have f2:"finite {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E}" using tmp1 finite_subset by auto
            have f3: "{(u, v) | u. u \<in> V \<and> (u, v) \<in> E} \<inter> {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E} = {}"
              (is "?S1 \<inter> ?S2 = _") by blast 
            note f = setsum.union_disjoint[of ?S1 ?S2 g]
            have "(\<Sum>e \<in> ?S1 \<union> ?S2. g e) = (\<Sum>e \<in> ?S1. g e) + (\<Sum>e \<in> ?S2. g e)"
              using f[OF f1 f2 f3] by simp
            moreover have "?S1 \<union> ?S2 = {(u, v) | u. u \<in> V}" by force
            ultimately have "(\<Sum>e \<in> {(u, v) | u. u \<in> V}. g e) =
              (\<Sum>e \<in> ?S1. g e) + (\<Sum>e \<in> ?S2. g e)" by simp
          } note fct1 = this
          {
            have "\<And>e. (e \<in> {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E} \<Longrightarrow> g e = 0)"
              proof -
                {
                  fix e
                  assume asm: "e \<in> {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E}"
                  have "g e = 0"
                    proof (rule ccontr)
                      assume "\<not> g e = 0"
                      then have "e \<in> E" using asm2 E_def 
                         by (metis (mono_tags, lifting) antisym case_prodI2 mem_Collect_eq)
                      then have "e \<notin> {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E}" unfolding E_def by auto
                      thus "False" using asm by blast
                    qed
                }
                then show "\<And>e. (e \<in> {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E} \<Longrightarrow> g e = 0)" by simp
              qed
            then have "(\<Sum>e \<in> {(u, v) | u. u \<in> V \<and> (u, v) \<notin> E}. g e) = 0" by auto
          } note fct2 = this
          {
            have "{(u, v) | u. u \<in> V \<and> (u, v) \<in> E} = {(u, v) | u. (u, v) \<in> E}" (is "?L = ?R")
              unfolding V_def E_def by auto
            then have "(\<Sum>e \<in> ?L. g e) = (\<Sum>e \<in> ?R. g e)" by simp
          } note fct3 = this
          have "(\<Sum>e \<in> {(u, v) | u. (u, v) \<in> E}. g e) = (\<Sum>e \<in> {(u, v) | u. u \<in> V}. g e) "
            using fct1 fct2 fct3 by auto
          moreover have "(\<Sum>e \<in> {(u, v) | u. u \<in> V}. g e) = (\<Sum>u \<in> {u | u. u \<in> V}. g (u, v))"
            using setsumExt.decomp_3[of V "\<lambda>x y. (y, x)" g v] asm1 by auto
          ultimately have "(\<Sum>e \<in> {(u, v) | u. (u, v) \<in> E}. g e) = 
            (\<Sum>u \<in> {u | u. u \<in> V}. g (u, v))" by auto
        }
        thus ?thesis unfolding incoming_def by auto
      qed
  end


  lemma (in Finite_Graph) finite_E[simp,intro!]: "finite E" by simp


  lemma (in Graph) Finite_Graph_EI: "finite E \<Longrightarrow> Finite_Graph c"
    apply unfold_locales
    by (rule Efin_imp_Vfin)
  


  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Path lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin 
    named_theorems split_path_simps \<open>Simplification lemmas to split paths\<close>

    lemma transfer_path:
      -- \<open>Transfer path to another graph\<close>
      assumes "set p\<inter>E \<subseteq> Graph.E c'"
      assumes "isPath u p v"
      shows "Graph.isPath c' u p v"
      using assms
      apply (induction u p v rule: isPath.induct)
      apply (auto simp: Graph.isPath.simps)
      done

    lemma isPath_append[split_path_simps]: "isPath u (p1 @ p2) v \<longleftrightarrow> (\<exists>w. isPath u p1 w \<and> isPath w p2 v)"  
      by (induction p1 arbitrary: u) auto 
      
    lemma isPath_head[split_path_simps]: "isPath u (e#p) v \<longleftrightarrow> fst e = u \<and> e \<in> E \<and> isPath (snd e) p v"
      by (cases e) auto

    lemma isPath_head2: "isPath u (e#p) v \<Longrightarrow> (p = [] \<or> (p \<noteq> [] \<and> fst (hd p) = snd e))"
      by (metis Graph.isPath_head list.collapse)
      
    lemma isPath_tail: "isPath u (p@[e]) v \<longleftrightarrow> isPath u p (fst e) \<and> e \<in> E \<and> snd e = v"
      by (induction p) (auto simp: isPath_append isPath_head)
    
    lemma isPath_tail2: "isPath u (p@[e]) v \<Longrightarrow> (p = [] \<or> (p \<noteq> [] \<and> snd (last p) = fst e))"
      by (metis Graph.isPath_tail append_butlast_last_id)
      
    (* TODO: Really needed? *)  
    lemma isPath_append_edge: "isPath v p v' \<Longrightarrow> (v',v'')\<in>E \<Longrightarrow> isPath v (p@[(v',v'')]) v''"  
      by (auto simp: isPath_append)

    lemma isPath_edgeset: "\<lbrakk>isPath u p v; e \<in> set p\<rbrakk> \<Longrightarrow> e \<in> E"
      using E_def 
      by (metis (mono_tags, lifting) isPath_head isPath_append in_set_conv_decomp_first)
      
    lemma isPath_rtc: "isPath u p v \<Longrightarrow> (u, v) \<in> E\<^sup>*"
      proof (induction p arbitrary: u)
        case Nil
          thus ?case by auto
      next
        case (Cons e es)
          obtain u1 u2 where "e = (u1, u2)" apply (cases e) by auto
          then have "u = u1 \<and> isPath u2 es v \<and> (u1, u2) \<in> E"
            using isPath.simps(2) Cons.prems by auto
          then have "(u, u2) \<in> E" and "(u2, v) \<in> E\<^sup>*" using Cons.IH by auto
          thus ?case by auto 
      qed
      
    lemma rtc_isPath: "(u, v) \<in> E\<^sup>* \<Longrightarrow> (\<exists>p. isPath u p v)"
      proof (induction rule: rtrancl.induct)
        case (rtrancl_refl a)
          have "isPath a [] a" by simp
          thus ?case by blast
      next
        case (rtrancl_into_rtrancl u u' v)
          then obtain p1 where "isPath u p1 u'" by blast
          moreover have "(u', v) \<in> E" using rtrancl_into_rtrancl.hyps(2) by simp
          ultimately have "isPath u (p1 @ [(u', v)]) v" using isPath_tail by simp
          thus ?case by blast
      qed
    
    lemma rtci_isPath: "(v, u) \<in> (E\<inverse>)\<^sup>* \<Longrightarrow> (\<exists>p. isPath u p v)"
    proof -
      assume "(v,u)\<in>(E\<inverse>)\<^sup>*" 
      hence "(u,v)\<in>E\<^sup>*" by (rule rtrancl_converseD)
      thus ?thesis by (rule rtc_isPath)
    qed      
      
    lemma isPath_ex_edge1: "\<lbrakk>isPath u p v; (u1, v1) \<in> set p; u1 \<noteq> u\<rbrakk> \<Longrightarrow> \<exists>u2. (u2, u1) \<in> set p"
      proof -
        assume asm1: "isPath u p v"
        assume asm2: "(u1, v1) \<in> set p"
        assume asm3: "u1 \<noteq> u"
        obtain w1 w2 where obt1: "p = w1 @ [(u1, v1)] @ w2" using asm2
          by (metis append_Cons append_Nil in_set_conv_decomp_first)
        then have "isPath u w1 u1" using asm1 isPath_append by auto
        have "w1 \<noteq> []"
          proof (rule ccontr)
            assume "\<not> w1 \<noteq> []"
            then have "u = u1" using `isPath u w1 u1` by (metis isPath.simps(1))
            thus "False" using asm3 by blast
          qed
        then obtain e w1' where obt2:"w1 = w1' @ [e]" by (metis append_butlast_last_id)
        then obtain u2 where "e = (u2, u1)" 
          using `isPath u w1 u1` isPath_tail by (metis prod.collapse)
        then have "p = w1' @ (u2, u1) # (u1, v1) # w2" using obt1 obt2 by auto 
        thus ?thesis by auto
      qed
    
    lemma isPath_ex_edge2: "\<lbrakk>isPath u p v; (u1, v1) \<in> set p; v1 \<noteq> v\<rbrakk> \<Longrightarrow> \<exists>v2. (v1, v2) \<in> set p"
      proof -
        assume asm1: "isPath u p v"
        assume asm2: "(u1, v1) \<in> set p"
        assume asm3: "v1 \<noteq> v"
        obtain w1 w2 where obt1: "p = w1 @ [(u1, v1)] @ w2" using asm2
          by (metis append_Cons append_Nil in_set_conv_decomp_first)
        then have "isPath v1 w2 v" using asm1 isPath_append by auto
        have "w2 \<noteq> []"
          proof (rule ccontr)
            assume "\<not> w2 \<noteq> []"
            then have "v = v1" using `isPath v1 w2 v` by (metis isPath.simps(1))
            thus "False" using asm3 by blast
          qed
        then obtain e w2' where obt2:"w2 =  e # w2'" by (metis neq_Nil_conv)
        then obtain v2 where "e = (v1, v2)" 
          using `isPath v1 w2 v` isPath_head by (metis prod.collapse)
        then have "p = w1 @ (u1, v1) # (v1, v2) # w2'" using obt1 obt2 by auto
        thus ?thesis by auto
       qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Path Vertices lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin   

    lemma (in Graph) pathVertices_fwd_simps[simp]: 
      "pathVertices_fwd s ([]) = [s]"  
      "pathVertices_fwd s (e#p) = s#pathVertices_fwd (snd e) p"  
      "pathVertices_fwd s (p@[e]) = pathVertices_fwd s p@[snd e]"
      "pathVertices_fwd s (p1@e#p2) = pathVertices_fwd s p1 @ pathVertices_fwd (snd e) p2"
      "s\<in>set (pathVertices_fwd s p)"
      by (auto simp: pathVertices_fwd_def)



    lemma pathVertices_alt: "p \<noteq> [] \<Longrightarrow> pathVertices u p = map fst p @ [snd (last p)]"
      by (induction p arbitrary: u) auto
    
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

    lemma pathVertices_append: "pathVertices u (p1 @ p2) = 
      butlast (pathVertices u p1) @ pathVertices (last (pathVertices u p1)) p2"
      proof (induction p1 arbitrary: u)
        case Nil
          thus ?case by auto
      next
        case (Cons e es)
          have "pathVertices u ((e # es) @ p2) =  fst e # pathVertices (snd e) (es @ p2)"
            by (metis Graph.pathVertices.simps(2) append_Cons)
          moreover have "pathVertices (snd e) (es @ p2) =  butlast (pathVertices (snd e) es) @
            pathVertices (last (pathVertices (snd e) es)) p2" using Cons.IH by auto
          moreover have "fst e # butlast (pathVertices (snd e) es) = 
            butlast (fst e # pathVertices (snd e) es)" by (metis Graph.pathVertices.simps(1)
            Graph.pathVertices_alt Nil_is_append_conv butlast.simps(2) list.distinct(1))
          moreover have "fst e # pathVertices (snd e) es = pathVertices u (e # es)"
            by (metis Graph.pathVertices.simps(2))
          moreover have "last (pathVertices (snd e) es) = last (pathVertices u (e # es))"
            by (metis Graph.pathVertices.simps(1) Graph.pathVertices_alt 
            last.simps last_snoc list.distinct(1))
          ultimately show ?case by (metis append_Cons)
      qed
    
    lemma (in Graph) split_path_at_vertex: 
      assumes "u\<in>set (pathVertices_fwd s p)"
      assumes "isPath s p t"
      obtains p1 p2 where "p=p1@p2" "isPath s p1 u" "isPath u p2 t"
      using assms
      apply -
      (*unfolding pathVertices_fwd*)
      unfolding pathVertices_fwd_def
      apply (auto simp: in_set_conv_decomp isPath_append) 
      apply force
      by (metis Graph.isPath_append_edge append_Cons append_Nil append_assoc)


    lemma split_path_at_vertex_complete: 
      assumes "isPath s p t" "pathVertices_fwd s p = pv1@u#pv2" 
      obtains p1 p2 where 
        "p=p1@p2" 
        "isPath s p1 u" "pathVertices_fwd s p1 = pv1@[u]" 
        "isPath u p2 t" "pathVertices_fwd u p2 = u#pv2" 
    proof -
      from assms have PV: "pathVertices s p = pv1@u#pv2" by (simp add: pathVertices_fwd)
      then obtain p1 p2 where 
        "p=p1@p2" 
        "isPath s p1 u" "pathVertices s p1 = pv1@[u]" 
        "isPath u p2 t" "pathVertices u p2 = u#pv2"
      proof -
        show thesis
        using assms(1) PV
        apply (cases p rule: rev_cases; clarsimp simp: pathVertices_alt)
          apply (rule that[of "[]" "[]"]; simp)

          apply (cases pv2; clarsimp)
          apply (rule that[of p "[]"]; 
            auto simp add: isPath_append pathVertices_alt
          )  

          apply (clarsimp simp: append_eq_append_conv2; 
            auto elim!: map_eq_concE map_eq_consE list_append_eq_Cons_cases
                simp: isPath_append)

            apply (rename_tac l)
            apply (erule that) 
            apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)

            apply (rename_tac l)
            apply (erule that) 
            apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)

            apply (rename_tac l u1 u2 u3)
            apply (erule that)  
            apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)
            apply (auto simp: isPath_append) []
            apply (auto simp: pathVertices_alt) []
            
            apply (rename_tac l)
            apply (erule that) apply auto [4]
            apply (case_tac l rule: rev_cases; auto simp add: pathVertices_alt isPath_append)
        done
      qed
      thus ?thesis apply - unfolding pathVertices_fwd using that .
    qed

    lemma isPath_fwd_cases: 
      assumes "isPath s p t"
      obtains "p=[]" "t=s"
        | p' u where "p=(s,u)#p'" "(s,u)\<in>E" "isPath u p' t"
        using assms by (cases p) (auto)

    lemma isPath_bwd_cases: 
      assumes "isPath s p t"
      obtains "p=[]" "t=s"
        | p' u where "p=p'@[(u,t)]" "isPath s p' u" "(u,t)\<in>E"
        using assms by (cases p rule: rev_cases) (auto simp: split_path_simps)


    lemma pathVertices_edge: "isPath s p t \<Longrightarrow> e \<in> set p \<Longrightarrow> 
      \<exists>vs1 vs2. pathVertices_fwd s p = vs1 @ fst e # snd e # vs2"
      apply (cases e)
      apply (auto simp: in_set_conv_decomp split_path_simps)
      apply (erule isPath_bwd_cases[where s=s]; auto)
      apply (erule isPath_fwd_cases[where t=t]; auto)
      apply (erule isPath_fwd_cases[where t=t]; auto)
      done  


    (* TODO: Really needed? *)
    lemma pathVertices_edge_old: "isPath u p v \<Longrightarrow> e \<in> set p \<Longrightarrow> 
      \<exists>vs1 vs2. pathVertices u p = vs1 @ fst e # snd e # vs2"
      proof (induction p arbitrary: u)
        case Nil
          thus ?case by auto
      next
        case (Cons x xs)
          then have "e = x \<or> e \<in> set xs" by auto
          thus ?case
            proof
              assume "e = x"
              thus ?thesis
                proof (cases "set xs = {}")
                  case (True)
                    then have "pathVertices u (x # xs) = [] @ fst e # snd e # []" 
                      using `e = x` by auto
                    thus ?thesis by auto
                next
                  case (False)
                    then obtain x' xs' where obt: "xs = x' # xs'"
                      by (metis list.exhaust empty_set)
                    moreover have "isPath (snd x) xs v" using Cons.prems(1) isPath_head by auto
                    ultimately have "snd e = fst x'" using `e = x` isPath_head by auto
                    then have "pathVertices u (x # (xs)) = 
                      [] @ fst e # snd e # pathVertices (snd x') xs'" using `e = x` obt by auto
                    thus ?thesis by auto
                qed
            next
              assume "e \<in> set xs"
              moreover have "isPath (snd x) xs v" using Cons.prems(1) isPath_head by auto
              ultimately have "\<exists>vs1 vs2. pathVertices (snd x) xs =
                vs1 @ fst e # snd e # vs2" using Cons.IH by auto
              then obtain vs1 vs2 where 
                obt: "pathVertices (snd x) xs = vs1 @ fst e # snd e # vs2" by blast
              then have "pathVertices u (x # xs) = (fst x # vs1) @ fst e # snd e # vs2" by auto
              thus ?thesis by metis
            qed
      qed
  end 
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  (* Reachability lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)  
  context Graph
  begin
    lemma reachable_ss_V: "s \<in> V \<Longrightarrow> reachableNodes s \<subseteq> V"
      proof
        assume asm: "s \<in> V"
        fix x
        assume "x \<in> reachableNodes s"
        then obtain p where "x \<in> {v. isPath s p v}"
          unfolding reachableNodes_def connected_def by blast
        thus "x \<in> V" using asm
          by (induction p arbitrary: s) (auto simp: isPath_head V_alt) 
      qed

    lemma connected_refl[simp, intro!]: "connected v v" 
      unfolding connected_def by (force intro: exI[where x="[]"])

    lemma connected_inV_iff: "\<lbrakk>connected u v\<rbrakk> \<Longrightarrow> v\<in>V \<longleftrightarrow> u\<in>V"
      apply (auto simp: connected_def)
      apply (case_tac p; auto simp: V_def) []
      apply (case_tac p rule: rev_cases; auto simp: isPath_append V_def) []
      done

    lemma connected_edgeRtc: "connected u v \<longleftrightarrow> (u, v) \<in> E\<^sup>*"  
    proof
      assume "connected u v"
      then obtain p where "isPath u p v" by (auto simp add: connected_def)
      thus "(u,v)\<in>E\<^sup>*"
        apply (induction p arbitrary: u)
        apply (auto simp: intro: converse_rtrancl_into_rtrancl)
        done
    next
      assume "(u,v)\<in>E\<^sup>*"
      thus "connected u v"
        proof (induction rule: converse_rtrancl_induct)
          case (step y z)
            from step.IH obtain p where "isPath z p v" by (auto simp add: connected_def)
            moreover from step.hyps have "(y,z) \<in> E" by (simp add: )
            ultimately have "isPath y ((y,z)#p) v" by (auto simp: isPath_head)
            thus ?case unfolding connected_def by blast
        qed simp
    qed    
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Simple path lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin          

    lemma isSimplePath_fwd: "isSimplePath s p t \<longleftrightarrow> isPath s p t \<and> distinct (pathVertices_fwd s p)"  
      by (auto simp: isSimplePath_def pathVertices_fwd)

    lemma isSimplePath_singelton[split_path_simps]: "isSimplePath u [e] v \<longleftrightarrow> (e=(u,v) \<and> u\<noteq>v \<and> (u,v)\<in>E)"
      by (auto simp: isSimplePath_def isPath_head)

    lemma (in Graph) isSimplePath_append[split_path_simps]: 
      "isSimplePath s (p1@p2) t 
        \<longleftrightarrow> (\<exists>u. isSimplePath s p1 u \<and> isSimplePath u p2 t \<and> set (pathVertices_fwd s p1) \<inter> set (pathVertices_fwd u p2) = {u})"  
      (is "_ \<longleftrightarrow> ?R")
      unfolding isSimplePath_fwd
      apply (cases p1 rule: rev_cases; simp; cases p2; simp)
      by (auto simp: split_path_simps)
      
    lemma (in Graph) isSimplePath_cons[split_path_simps]: 
      "isSimplePath s (e#p) t \<longleftrightarrow> (\<exists>u. e=(s,u) \<and> s\<noteq>u \<and> (s,u)\<in>E \<and> isSimplePath u p t \<and> s\<notin>set (pathVertices_fwd u p))"
      using isSimplePath_append[of s "[e]" p t, simplified]
      by (auto simp: split_path_simps)

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

    lemma isSPath_pathLE: "isPath u p v \<Longrightarrow> \<exists>p'. isSimplePath u p' v"
      proof (induction p arbitrary: u)
        case Nil
          then have "isSimplePath u [] v" unfolding isSimplePath_def by auto
          thus ?case by auto
      next
        case (Cons e es)
          then have "isPath (snd e) es v" by (metis Graph.isPath_head)
          then obtain es' where obt1: "isSimplePath (snd e) es' v" using Cons.IH by auto
          have fct0: "fst e = u \<and> e \<in> E" using Cons.prems by (metis Graph.isPath_head)
          have fct1: "isPath (snd e) es' v" using obt1 isSimplePath_def by auto
          have fct2: "distinct (pathVertices (snd e) es')" using obt1 isSimplePath_def by auto
          have "distinct (pathVertices u (e # es')) \<or> \<not> distinct (pathVertices u (e # es'))" by auto
          thus ?case
            proof 
              assume "distinct (pathVertices u (e # es'))"
              moreover have "isPath u (e # es') v" using fct0 fct1 by (metis isPath_head)
              ultimately have "isSimplePath u (e # es') v" unfolding isSimplePath_def by auto
              thus ?thesis by blast
            next
              assume "\<not> distinct (pathVertices u (e # es'))"
              then have "fst e \<in> set (pathVertices (snd e) es')" using fct2 by auto
              thus ?thesis
                proof (cases "es' = []")
                  case True
                    then have "e = (u, v)" using fct1 fct0 by (metis isPath.simps(1) prod.collapse)
                    thus ?thesis
                      proof (cases "u \<noteq> v")
                        case True
                          then have "distinct (pathVertices u [(u, v)])" by auto
                          moreover have "isPath u [(u, v)] v" using `e = (u, v)` fct0 by auto
                          ultimately have "isSimplePath u [(u, v)] v" 
                            unfolding isSimplePath_def by auto
                          thus ?thesis by auto
                      next
                        case False
                          then have "isPath u [] v" by auto
                          moreover have "distinct (pathVertices u [])" by auto
                          ultimately have "isSimplePath u [] v" unfolding isSimplePath_def by auto
                          thus ?thesis by auto
                      qed
                next
                  case False
                    then obtain x where "fst e = x \<and> x \<in> set ( map fst es' @ [snd (last es')])" 
                      using `fst e \<in> set (pathVertices (snd e) es')` pathVertices_alt by auto
                    then have "(\<exists>e' \<in> set es'. u = fst e') \<or> u = snd (last es')" using fct0 by auto
                    thus ?thesis
                      proof
                        assume "\<exists>e' \<in> set es'. u = fst e'"
                        then obtain e' where "e' \<in> set es' \<and> u = fst e'" by auto
                        then obtain w1 w2 where "es' = w1 @ (e' # w2)" 
                          by (metis in_set_conv_decomp_first)
                        then obtain y  where "isPath y (e' # w2) v" 
                          using fct1 isPath_append by auto
                        then have "y = u" using `e' \<in> set es' \<and> u = fst e'` isPath_head by auto
                        then have "isPath u (e' # w2) v" using `isPath y (e' # w2) v` by auto
                        moreover {
                          note pathVertices_append[of "snd e" w1 "e' # w2"]
                          then have "pathVertices (snd e) es' = butlast (pathVertices (snd e) w1) @ 
                            pathVertices (last (pathVertices (snd e) w1)) (e' # w2)"
                            using `es' = w1 @ (e' # w2)` by auto
                          then have "distinct ( pathVertices (last (pathVertices (snd e) w1))
                            (e' # w2))" using fct2 by auto
                          moreover have "pathVertices (last (pathVertices (snd e) w1))
                            (e' # w2) = pathVertices u (e' # w2)" by auto
                          ultimately have "distinct (pathVertices u (e' # w2))" by auto
                        }
                        ultimately have "isSimplePath u (e' # w2) v" 
                          unfolding isSimplePath_def by auto 
                        thus ?thesis by auto
                      next
                        assume "u = snd (last es')"
                        then have "u = v" using False fct1 
                          by (metis Graph.isPath_tail snoc_eq_iff_butlast)
                        then have "isPath u [] v" by auto
                        moreover have "distinct (pathVertices u [])" by auto
                        ultimately have "isSimplePath u [] v" unfolding isSimplePath_def by auto
                        thus ?thesis by auto
                      qed
                qed
            qed
      qed  

    lemma isSPath_no_selfloop: "isSimplePath u p v \<Longrightarrow> (u1, u1) \<notin> set p"
      proof (rule ccontr)
        assume asm: "isSimplePath u p v"
        assume "\<not> (u1, u1) \<notin> set p"
        then have "(u1, u1) \<in> set p" by blast
        moreover have "isPath u p v" using asm isSimplePath_def by auto
        ultimately have "\<exists>vs1 vs2. pathVertices_fwd u p = vs1 @ u1 # u1 # vs2" 
          using pathVertices_edge by auto
        then obtain vs1 vs2 where "pathVertices_fwd u p = vs1 @ u1 # u1 # vs2" by blast
        then have "\<not> distinct (pathVertices_fwd u p)" 
          by (metis distinct_append distinct_length_2_or_more)
        thus "False" using asm isSimplePath_fwd by auto
      qed
      
    (* TODO: There should be a much simpler proof! *)  
    lemma isSPath_sg_outgoing: "\<lbrakk>isSimplePath u p v; (u1, v1) \<in> set p; v1 \<noteq> v2\<rbrakk> \<Longrightarrow> (u1, v2) \<notin> set p"
      proof -
        assume asm1: "isSimplePath u p v"
        assume asm2: "(u1, v1) \<in> set p"
        assume asm3: "v1 \<noteq> v2"
        show ?thesis
          proof (rule ccontr)
            assume asm_s: "\<not> (u1, v2) \<notin> set p"
            obtain w1 w2 where obt1: "p = w1 @ (u1, v1) # w2" 
              using asm2 by (metis in_set_conv_decomp)
            then have "(u1, v2) = (u1, v1) \<or> ((u1, v2) \<in> (set w1) \<or> (u1, v2) \<in> (set w2))" 
              using asm_s by (metis Un_iff set_ConsD set_append)
            then have "(u1, v2) \<in> (set w1) \<or> (u1, v2) \<in> (set w2)" using asm3 by auto
            then show "False"
              proof
                assume "(u1, v2) \<in> (set w1)"
                note pathVertices_append[of u w1 "(u1, v1) # w2"]
                moreover {
                  have "isPath u p v" using asm1 isSimplePath_def by auto
                  then obtain x where obt2: "isPath u w1 x" 
                    using obt1 isPath_append[of u w1 "(u1, v1) # w2"] by auto
                  then obtain vs1 vs2 where "pathVertices u w1 = vs1 @ u1 # v2 # vs2" 
                    using pathVertices_edge_old[OF obt2 `(u1, v2) \<in> (set w1)`] by auto
                  then have "\<exists>vs1 vs2. butlast (pathVertices u w1) = vs1 @ u1 # vs2"
                    by (metis butlast.simps(2) butlast_append list.distinct(1))
                }
                moreover {
                  have "pathVertices (last (pathVertices u w1)) ((u1, v1) # w2) = 
                    u1 # pathVertices v1 w2" (is "?L = _") by auto
                  then have "\<exists> vs1. ?L = u1 # vs1" by auto
                }
                ultimately obtain vs1 vs2 vs3 where "pathVertices u p = vs1 @ u1 # vs2 @ u1 # vs3"
                  using obt1 by auto
                then have "\<not> distinct (pathVertices u p)"
                  by (metis distinct.simps(2) distinct_append in_set_conv_decomp)
                thus ?thesis using asm1 isSimplePath_def by auto 
              next
                assume "(u1, v2) \<in> (set w2)"
                note pathVertices_append[of u "w1 @ [(u1, v1)]" w2]
                moreover {
                 have "p = (w1 @ [(u1, v1)]) @ w2" using obt1 by auto
                 then have "isPath u ((w1 @ [(u1, v1)]) @ w2) v" using asm1 isSimplePath_def by auto
                 then obtain x where obt2: "isPath u (w1 @ [(u1, v1)]) x \<and> isPath x w2 v" 
                    using isPath_append[of u "w1 @ [(u1, v1)]" w2 v] by auto
                 then have "x = v1" using isPath_tail by auto
                 moreover have "last (pathVertices u (w1 @ [(u1, v1)])) = v1" (is "?L = _")
                  using pathVertices_alt by auto
                 ultimately have "isPath ?L w2 v" using obt2 by auto
                 note pathVertices_edge_old[OF this `(u1, v2) \<in> (set w2)`] 
                 then have "\<exists> vs1 vs2. pathVertices (last (pathVertices u 
                  (w1 @ [(u1, v1)]))) w2 = vs1 @ u1 # v2 # vs2" by auto 
                }
                moreover {
                  have "w1 @ [(u1, v1)] \<noteq> []" by auto
                  then have "pathVertices u (w1 @ [(u1, v1)]) = map fst (w1 @ [(u1, v1)]) @ 
                    [snd (last (w1 @ [(u1, v1)]))]" using pathVertices_alt by auto
                  moreover have "map fst (w1 @ [(u1, v1)]) @ [snd (last (w1 @ [(u1, v1)]))] =
                    map fst w1 @ u1 # [v1]" by auto
                  ultimately have "\<exists>vs1. butlast (pathVertices u (w1 @ [(u1, v1)])) = 
                    vs1 @ [u1]" by (metis append_Cons append_Nil append_assoc snoc_eq_iff_butlast)
                }
                moreover have "p = (w1 @ [(u1, v1)]) @ w2" using obt1 by auto
                ultimately obtain vs1 vs2 vs3 where "pathVertices u p = vs1 @ [u1] @ vs2 @ 
                  u1 # v2 # vs3" by auto
                then have "\<not> distinct (pathVertices u p)" by (metis append_Cons append_Nil
                  distinct.simps(2) distinct_append in_set_conv_decomp)
                thus ?thesis using asm1 isSimplePath_def by auto 
              qed
          qed
      qed
      
    (* TODO: There should be a much simpler proof! *)  
    lemma isSPath_sg_incoming: "\<lbrakk>isSimplePath u p v; (u1, v1) \<in> set p; u1 \<noteq> u2\<rbrakk> \<Longrightarrow> (u2, v1) \<notin> set p"
      proof -
        assume asm1: "isSimplePath u p v"
        assume asm2: "(u1, v1) \<in> set p"
        assume asm3: "u1 \<noteq> u2"
        show ?thesis
          proof (rule ccontr)
            assume asm_s: "\<not> (u2, v1) \<notin> set p"
            obtain w1 w2 where obt1: "p = w1 @ (u1, v1) # w2" 
              using asm2 by (metis in_set_conv_decomp)
            then have "(u2, v1) = (u1, v1) \<or> ((u2, v1) \<in> (set w1) \<or> (u2, v1) \<in> (set w2))" 
              using asm_s by (metis Un_iff set_ConsD set_append)
            then have "(u2, v1) \<in> (set w1) \<or> (u2, v1) \<in> (set w2)" using asm3 by auto
            then show "False"
              proof
                assume "(u2, v1) \<in> (set w1)"
                note pathVertices_append[of u w1 "(u1, v1) # w2"]
                moreover {
                  have "isPath u p v" using asm1 isSimplePath_def by auto
                  then have "isPath u w1 u1" 
                    using obt1 isPath_append[of u w1 "(u1, v1) # w2"] by auto
                  then obtain vs1 vs2 where obt2: "pathVertices u w1 = vs1 @ u2 # v1 # vs2" 
                    using pathVertices_edge_old[OF _ `(u2, v1) \<in> (set w1)`] by (metis fst_conv snd_conv)
                  moreover {
                    have "snd (last w1) = u1" using `isPath u w1 u1` `(u2, v1) \<in> set w1` 
                      by (metis isPath_tail append_butlast_last_id empty_iff list.set(1))
                    have "vs2 \<noteq> []"
                      proof (rule ccontr)
                        assume "\<not> vs2 \<noteq> []"
                        then have "pathVertices u w1 = vs1 @ u2 # v1 # []" using obt2 by auto
                        moreover have "pathVertices u w1 = map fst w1 @ [snd (last w1)]" 
                          using `(u2, v1) \<in> (set w1)` pathVertices_alt[of w1 u] 
                          by (metis empty_iff list.set(1)) 
                        ultimately have "snd (last w1) = v1" 
                          by (metis last.simps last_appendR list.distinct(2))
                        then have "u1 = v1" using `snd (last w1) = u1` by auto
                        thus "False" using isSPath_no_selfloop[OF asm1] asm2 by auto 
                      qed
                  }
                  ultimately have "\<exists>vs1 vs2. butlast (pathVertices u w1) = vs1 @ u2 # v1 # vs2"
                    by (metis butlast.simps(2) butlast_append list.distinct(1))
                }
                moreover {
                  have "pathVertices (last (pathVertices u w1)) ((u1, v1) # w2) = 
                    pathVertices u1 ((u1, v1) # w2)" (is "?L = _") by auto
                  moreover {
                    have "isPath u p v" using asm1 isSimplePath_def by auto
                    then have "isPath u1 ((u1, v1) # w2) v" 
                      using obt1 isPath_append[of u w1 "(u1, v1) # w2"] by auto
                    note pathVertices_edge_old[OF this]
                  }
                  then have "\<exists> vs1 vs2. ?L = vs1 @ u1 # v1 # vs2" by auto
                }
                ultimately obtain vs1 vs2 vs3 vs4 where 
                  "pathVertices u p = vs1 @ u2 # v1 # vs2 @ vs3 @ u1 # v1 # vs4" using obt1 by auto
                then have "\<not> distinct (pathVertices u p)" by auto
                thus ?thesis using asm1 isSimplePath_def by auto 
              next
                assume "(u2, v1) \<in> (set w2)"
                note pathVertices_append[of u "w1 @ [(u1, v1)]" w2]
                moreover {
                  have "isPath u p v" using asm1 isSimplePath_def by auto
                  then have "isPath v1 w2 v" 
                    using obt1 isPath_append[of u w1 "(u1, v1) # w2"] by auto
                  {
                    obtain x w2' where obt2: "w2 = x # w2'" using `(u2, v1) \<in> (set w2)`
                      by (metis empty_iff list.collapse list.set(1))
                    then have "fst x = v1" by (metis Graph.isPath_head `isPath v1 w2 v`)
                    then have "x \<noteq> (u2, v1)" using isSPath_no_selfloop[OF asm1] obt1 obt2
                      by (metis asm_s fst_conv)
                    then have "(u2, v1) \<in> set w2'" using obt2 `(u2, v1) \<in> (set w2)`
                      by (metis set_ConsD)
                    then have "\<exists>x w2'. w2 = (v1, x) # w2' \<and> (u2, v1) \<in> (set w2')"
                      using obt2 `fst x = v1` by (metis PairE fst_conv)
                  } 
                  from this obtain x w2' where obt2: 
                    "w2 = (v1, x) # w2' \<and> (u2, v1) \<in> set w2'" by auto
                  then have "isPath x w2' v \<and> (u2, v1) \<in> set w2'" using `isPath v1 w2 v` by auto 
                  then have "\<exists>vs1 vs2. pathVertices x w2' = vs1 @ u2 # v1 # vs2"
                    using pathVertices_edge_old by auto
                  moreover have "pathVertices (last (pathVertices u (w1 @ [(u1, v1)]))) w2 = 
                    v1 # pathVertices x w2'" (is "?L= _") using obt2 by auto
                  ultimately have "\<exists>vs1 vs2. ?L = v1 # vs1 @ u2 # v1 # vs2" by auto
                }
                moreover have "p = (w1 @ [(u1, v1)]) @ w2" using obt1 by auto
                ultimately obtain vs1 vs2 vs3 where 
                  "pathVertices u p = vs1 @ v1 # vs2 @ u2 # v1 # vs3" by auto
                then have "\<not> distinct (pathVertices u p)" by auto
                thus ?thesis using asm1 isSimplePath_def by auto 
              qed
          qed
      qed  
      
    (* TODO: There should be a much simpler proof! *)  
    lemma isSPath_no_returning: "\<lbrakk>isSimplePath u p v; (u1, v1) \<in> set p\<rbrakk> \<Longrightarrow>
      (\<exists>es1 es2. p = es1 @ (v2, u1) # (u1, v1) # es2 \<or> (v2, u1) \<notin> set p)"
      proof -
        assume asm1: "isSimplePath u p v"
        assume asm2: "(u1, v1) \<in> set p"
        show ?thesis
          proof (rule ccontr)
            assume asm_s: "\<not> (\<exists>es1 es2. p = es1 @ (v2, u1) # (u1, v1) # es2 \<or> (v2, u1) \<notin> set p)"
            have asm_s1: "\<forall> es1 es2. p \<noteq> es1 @ (v2, u1) # (u1, v1) # es2" using asm_s by auto
            have asm_s2: "(v2, u1) \<in> set p" using asm_s by auto 
            obtain w1 w2 where obt1: "p = w1 @ (u1, v1) # w2" 
              using asm2 by (metis in_set_conv_decomp)
            then have "(v2, u1) = (u1, v1) \<or> ((v2, u1) \<in> (set w1) \<or> (v2, u1) \<in> (set w2))" 
              using asm_s2 by (metis Un_iff set_ConsD set_append)
            then show "False"
              proof 
                assume "(v2, u1) = (u1, v1)"
                then have "(u1, u1) \<in> set p" using asm2 by auto 
                thus ?thesis using asm1 isSPath_no_selfloop by auto
              next
                assume "(v2, u1) \<in> (set w1) \<or> (v2, u1) \<in> (set w2)"
                thus ?thesis
                  proof
                    assume "(v2, u1) \<in> (set w1)"
                    have "pathVertices u p = butlast (pathVertices u w1) @  pathVertices (last 
                      (pathVertices u w1)) ((u1, v1) # w2)" using obt1 pathVertices_append by auto
                    moreover {
                      have "set w1 \<noteq> {}" using `(v2, u1) \<in> (set w1)` by auto
                      {
                        obtain x where "isPath u w1 x" 
                          using obt1 asm1 isSimplePath_def isPath_append by auto
                        note pathVertices_edge_old[OF this `(v2, u1) \<in> (set w1)`]
                      }
                      then obtain vs1 vs2 where 
                        obt2: "pathVertices u w1 = vs1 @ fst (v2, u1) # snd (v2, u1) # vs2" by auto
                      moreover have "vs2 \<noteq> []"
                        proof (rule ccontr)
                          assume "\<not> vs2 \<noteq> []"
                          then have fct1: "pathVertices u w1 = vs1 @ [v2, u1]" using obt2 by auto
                          {
                            have "pathVertices u w1 = map fst w1 @ [snd (last w1)]" 
                              using pathVertices_alt `set w1 \<noteq> {}` by auto
                            moreover have "map fst w1 = map fst (butlast w1) @ [fst (last w1)]" 
                              using `set w1 \<noteq> {}` by (metis last_map empty_set map_butlast
                              snoc_eq_iff_butlast zip_Nil zip_map_fst_snd)
                            ultimately have "pathVertices u w1 = 
                              map fst (butlast w1) @ fst (last w1) # snd (last w1) # []" by auto
                          }  note fct2 = this
                          have "map fst (butlast w1) @ [fst (last w1)] = vs1 @ [v2]" using fct1
                            fct2 by (metis butlast.simps(2) butlast_append list.distinct(1)) 
                          then have "fst (last w1) = v2" by (metis last_snoc)
                          moreover have "snd (last w1) = u1" using fct1 fct2  
                            by (metis append_Cons append_Nil last_appendR last_snoc)
                          ultimately have "last w1 = (v2, u1)" by auto
                          moreover have "(v2, u1) \<noteq> last w1"
                            proof (rule ccontr)
                              assume "\<not> (v2, u1) \<noteq> last w1"
                              moreover have "butlast w1 @ [last w1] = w1" using `set w1 \<noteq> {}` 
                                by (metis append_butlast_last_id list.set(1))
                              ultimately have "p = butlast w1 @ (v2, u1) # (u1, v1) # w2" 
                                using obt1 by auto
                              thus "False" using asm_s1 by auto
                            qed
                          ultimately show "False" by metis
                        qed
                      ultimately have "\<exists> vs1' vs2'. butlast (pathVertices u w1) = 
                        vs1' @ v2 # u1 # vs2'" by (metis butlast.simps(2)
                        butlast_append fst_conv list.distinct(1) snd_conv)
                    }
                    moreover have "\<exists>vs3'. pathVertices (last (pathVertices u w1)) ((u1, v1) # w2) = 
                      u1 # vs3'" by (metis Graph.pathVertices.simps(2) fst_conv)
                    ultimately obtain vs1 vs2 vs3 where "pathVertices u p = 
                      (vs1 @ v2 # u1 # vs2) @ (u1 # vs3)" by auto
                    then have "\<not> distinct (pathVertices u p)" by (metis append_Cons append_assoc
                      distinct.simps(2) distinct_append in_set_conv_decomp)
                    thus ?thesis using asm1 isSimplePath_def by auto
                  next
                    assume "(v2, u1) \<in> (set w2)"
                    have "pathVertices u p = butlast (pathVertices u w1) @  pathVertices (last 
                      (pathVertices u w1)) ((u1, v1) # w2)" using obt1 pathVertices_append by auto
                    moreover have "pathVertices (last (pathVertices u w1)) ((u1, v1) # w2) = u1 # 
                      (pathVertices v1 w2)" by (metis Graph.pathVertices.simps(2) fst_conv snd_conv)
                    moreover {
                      have "isPath v1 w2 v" using asm1 isSimplePath_def
                        by (metis Graph.isPath.simps(2) Graph.isPath_append obt1)
                      note pathVertices_edge_old[OF this `(v2, u1) \<in> (set w2)`]
                      then have " \<exists>vs1 vs2. pathVertices v1 w2 = vs1 @ v2 # u1 # vs2" by auto
                    }
                    ultimately obtain vs1 vs2 vs3 where 
                      "pathVertices u p = vs1 @ (u1 # vs2 @ v2 # u1 # vs3 )" by auto
                    then have "\<not> distinct (pathVertices u p)" by auto
                    thus ?thesis using asm1 isSimplePath_def by auto
                  qed
              qed
          qed
      qed
      
    (* TODO: There should be a much simpler proof! *)  
    lemma isSPath_nt_parallel: "isSimplePath u p v \<Longrightarrow> (\<forall>(u, v) \<in> set p. (v, u) \<notin> set p)"
      proof -
        assume asm: "isSimplePath u p v"
        {
          fix x y
          assume asm_s: "(x, y) \<in> set p"
          have "\<exists>es1 es2. p = es1 @ (y, x) # (x, y) # es2 \<or> (y, x) \<notin> set p"
            using isSPath_no_returning[OF asm asm_s] by auto
          moreover have "\<not> (\<exists>es1 es2. p = es1 @ (y, x) # (x, y) # es2)"
            proof (rule ccontr)
              assume "\<not> \<not>(\<exists>es1 es2. p = es1 @ (y, x) # (x, y) # es2)"
              then obtain es1 es2 where obt: "p = es1 @ (y, x) # (x, y) # es2" by blast
              moreover have "isPath u p v" using asm isSimplePath_def[of u p v] by metis
              ultimately obtain w where "isPath w ((y, x) # (x, y) # es2) v"
                using isPath_append by auto
              then have "es2 = [] \<or> (es2 \<noteq> [] \<and> fst (hd es2) = y)"
                using isPath_head2[of x "(x, y)" es2] by auto
              then show "False"
                proof
                  assume "es2 = []"
                  have "pathVertices (last (pathVertices u es1)) [(y, x), (x, y)] = [y, x, y]"
                    by (metis pathVertices.simps(1) pathVertices.simps(2) fst_conv snd_conv)
                  moreover note pathVertices_append[of u es1 "(y, x) # (x, y) # []"]
                  ultimately have "pathVertices u p = butlast (pathVertices u es1) @ [y, x, y]"
                    using obt `es2 = []` by auto
                  then have "\<not> distinct (pathVertices u p)" by (metis distinct.simps(2)
                    distinct_append last.simps last_in_set list.distinct(1))
                  thus ?thesis using asm isSimplePath_def by auto
                next
                  assume "es2 \<noteq> [] \<and> fst (hd es2) = y"
                  {
                    have "pathVertices (last (pathVertices u es1)) ((y, x) # (x, y) # es2) =
                      y # x # pathVertices y es2" (is "?L = _") by auto
                    moreover have "pathVertices y es2 = fst (hd es2) # pathVertices 
                      (snd (hd es2)) (tl es2)" using `es2 \<noteq> [] \<and> fst (hd es2) = y` 
                      by (metis pathVertices.simps(2) list.collapse)
                    ultimately have "?L = y # x # y # pathVertices (snd (hd es2)) (tl es2)"
                      using `es2 \<noteq> [] \<and> fst (hd es2) = y` by auto
                  }
                  moreover note pathVertices_append[of u es1 "(y, x) # (x, y) # es2"]
                  ultimately have "pathVertices u p = butlast (pathVertices u es1) @ (y # x # y # 
                    pathVertices (snd (hd es2)) (tl es2))" using obt by auto
                  then have "\<not> distinct (pathVertices u p)"
                    by (metis (mono_tags) distinct_append distinct_length_2_or_more)
                  thus ?thesis using asm isSimplePath_def by auto
                qed
            qed
          ultimately have "(y, x) \<notin> set p" by blast
        }
        thus ?thesis by auto
      qed
      
    lemma isSPath_distinct: "isSimplePath u p v \<Longrightarrow> distinct p"
      proof (rule ccontr)
        assume asm: "isSimplePath u p v"
        assume "\<not> distinct (p)"
        then obtain us vs ws x where obt1: "p = us @ (x # vs @ [x]) @  ws"
          by (metis (mono_tags, hide_lams) append_Cons append_assoc not_distinct_decomp)
        then have "p \<noteq> []" by auto
        then have "pathVertices u p = map fst p @ [snd (last p)]" using pathVertices_alt by auto
        moreover have "map fst p = map fst us @ fst x # map fst vs @ [fst x] @ map fst ws"
          using obt1 by (metis append_Cons append_Nil append_assoc list.simps(9) map_append)
        ultimately have "pathVertices u p = map fst us @ fst x # map fst vs @ [fst x] @ 
          map fst ws @ [snd (last p)]" by (metis append_Cons append_assoc)
        then obtain vs1 vs2 vs3 where "pathVertices u p = vs1 @ fst x # vs2 @ fst x # vs3" by auto
        then have "\<not> distinct (pathVertices u p)" by auto
        thus "False" using asm isSimplePath_def by auto
      qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  (* Distance lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin
    lemma connected_by_dist: "connected v v' = (\<exists>d. dist v d v')"
      by (auto simp: dist_def connected_def)

    lemma isPath_distD: "isPath u p v \<Longrightarrow> dist u (length p) v"
      by (auto simp: dist_def)

    lemma
      shows connectedI[intro]: "dist v d v' \<Longrightarrow> connected v v'"
        and connectedI_id[intro!, simp]: "connected v v"
        and connectedI_succ: "connected v v' \<Longrightarrow> (v',v'') \<in> E \<Longrightarrow> connected v v''"
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
          by (auto simp: connectedI)
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


  end
  
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)


  (* Shortest Path Lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin
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

    lemma shortestPath_is_simple:
      assumes "isShortestPath s p t"
      shows "isSimplePath s p t"
    proof (rule ccontr)
      from assms have PATH: "isPath s p t" 
        and SHORTEST: "\<forall>p'. isPath s p' t \<longrightarrow> length p \<le> length p'"
        by (auto simp: isShortestPath_def)

      assume "\<not>isSimplePath s p t"  
      with PATH have "\<not>distinct (pathVertices_fwd s p)" by (auto simp: isSimplePath_fwd)

      then obtain pv1 u pv2 pv3 where PV: "pathVertices_fwd s p = pv1@u#pv2@u#pv3" 
        by (auto dest: not_distinct_decomp)

      from split_path_at_vertex_complete[OF PATH PV] obtain p1 p23 where
        [simp]: "p=p1@p23" and 
          P1: "isPath s p1 u" "pathVertices_fwd s p1 = pv1@[u]" and
          P23: "isPath u p23 t" "pathVertices_fwd u p23 = (u#pv2)@u#pv3"
          by auto
          
      from split_path_at_vertex_complete[OF P23] obtain p2 p3 where
        [simp]: "p23 = p2@p3" and
        P2: "isPath u p2 u" "pathVertices_fwd u p2 = u#pv2@[u]" and
        P3: "isPath u p3 t" "pathVertices_fwd u p3 = u#pv3"
        by auto

      from P1(1) P3(1) have SHORTER_PATH: "isPath s (p1@p3) t" by (auto simp: isPath_append)
      
      from P2 have "p2\<noteq>[]" by auto
      hence LESS: "length (p1@p3) < length p" by auto
      with SHORTER_PATH SHORTEST show False by auto
    qed    

    text \<open>We provide yet another characterization of shortest paths:\<close>
    lemma isShortestPath_alt: "isShortestPath u p v \<longleftrightarrow> isSimplePath u p v \<and> length p = min_dist u v"
      using shortestPath_is_simple isShortestPath_min_dist_def
      unfolding isSimplePath_def by auto

      
    text \<open>In a finite graph, the length of a shortest path is less 
      than the number of nodes\<close>  
    lemma isShortestPath_length_less_V:   
      assumes FIN: "finite V" and SV: "s\<in>V"
      assumes PATH: "isShortestPath s p t"
      shows "length p < card V"
      using simplePath_length_less_V[OF FIN SV]
      using shortestPath_is_simple[OF PATH] .

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


  lemma (in Flow) zero_flow_simp[simp]:
    "(u,v)\<notin>E \<Longrightarrow> f(u,v) = 0"
    by (metis capacity_const eq_iff zero_cap_simp)


end
