theory Graph
imports Fofu_Abs_Base
begin


  (* Graph definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  type_synonym node = nat 
  type_synonym edge = "node \<times> node"
  type_synonym capacity = int

  (*
  typedecl capacity 
  instance capacity :: linordered_idom sorry
  *)


  type_synonym graph = "edge \<Rightarrow> capacity"
  
  locale Graph = 
    fixes c :: graph
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
    abbreviation Graph_E :: "graph \<Rightarrow> edge set"
      ("\<lbrace>_/ \<parallel>\<^sub>G/ E\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G E\<rbrace> \<equiv> Graph.E c"
      
    abbreviation Graph_V :: "graph \<Rightarrow> node set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ V\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G V\<rbrace> \<equiv> Graph.V c"
      
    abbreviation Graph_incoming :: "graph \<Rightarrow> node \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<delta>\<^sup>+(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<delta>\<^sup>+ u\<rbrace> \<equiv> Graph.incoming c u"
      
    abbreviation Graph_outgoing :: "graph \<Rightarrow> node \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<delta>\<^sup>-(_)\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<delta>\<^sup>- u\<rbrace> \<equiv> Graph.outgoing c u"
      
    abbreviation Graph_delta :: "graph \<Rightarrow> node \<Rightarrow> edge set"
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<delta>(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<delta> u\<rbrace> \<equiv> Graph.adjacent c u"
      
    abbreviation Graph_incoming' :: "graph \<Rightarrow> node set \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<Delta>\<^sup>+(_)\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<Delta>\<^sup>+ u\<rbrace> \<equiv> Graph.incoming' c u"  
    
    abbreviation Graph_outgoing' :: "graph \<Rightarrow> node set \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<Delta>\<^sup>-(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<Delta>\<^sup>- u\<rbrace> \<equiv> Graph.outgoing' c u"
      
    abbreviation Graph_delta' :: "graph \<Rightarrow> node set \<Rightarrow> edge set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<Delta>(_)\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<Delta> u\<rbrace> \<equiv> Graph.adjacent' c u"
    (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
    (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
    (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  end  
  
  
  
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
    
    definition connected :: "node \<Rightarrow> node \<Rightarrow> bool" 
    where "connected u v \<equiv> \<exists>p. isPath u p v" 
    
    abbreviation (input) "isReachable \<equiv> connected" (* Deprecated *)

    definition reachableNodes :: "node \<Rightarrow> node set"  
    where "reachableNodes u \<equiv> {v. connected u v}"
    
    definition isShortestPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where "isShortestPath u p v \<equiv> isPath u p v \<and> (\<forall>p'. isPath u p' v \<longrightarrow> length p \<le> length p')"
        
    definition isSimplePath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
    where "isSimplePath u p v \<equiv> isPath u p v \<and> distinct (pathVertices u p)"
  end  

  context Graph_Loc_Syntax begin
    notation isPath ("\<langle>\<leadsto>/ _,/ _,/ _\<rangle>"  1000)
    notation connected ("\<langle>_/ \<leadsto>/ _\<rangle>" 1000)
    notation reachableNodes ("\<langle>\<star>/ _\<rangle>" 1000)
    notation isShortestPath ("\<langle>\<rightarrow>/ _,/ _,/ _\<rangle>" 1000) 
    notation isSimplePath ("\<langle>\<Rightarrow>/ _,/ _,/ _\<rangle>" 1000)
  end

  context Graph_Syntax begin  
    abbreviation Graph_isPath :: "graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<leadsto> _, _, _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<leadsto> u, p, v\<rangle>\<rbrace> \<equiv> Graph.isPath c u p v"
      
    abbreviation Graph_connected :: "graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>_/ \<leadsto>/ _\<rangle>\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>u \<leadsto> v\<rangle>\<rbrace> \<equiv> Graph.connected c u v"
      
    abbreviation Graph_reachableNodes :: "graph \<Rightarrow> node \<Rightarrow> node set" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<star>/ _\<rangle>\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<star> u\<rangle>\<rbrace> \<equiv> Graph.reachableNodes c u"
      
    abbreviation Graph_isShortestPath :: "graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<rightarrow> _, _, _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<rightarrow> u, p, v\<rangle>\<rbrace> \<equiv> Graph.isShortestPath c u p v"
      
    abbreviation Graph_isSimplePath :: "graph \<Rightarrow> node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool"
      ("\<lbrace>_/ \<parallel>\<^sub>G/ \<langle>\<Rightarrow> _, _, _\<rangle>\<rbrace>" 1000) 
    where "\<lbrace>c \<parallel>\<^sub>G \<langle>\<Rightarrow> u, p, v\<rangle>\<rbrace> \<equiv> Graph.isSimplePath c u p v"
  end  
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
    
  
  
  
  (* Flow definitions *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  type_synonym flow = "edge \<Rightarrow> capacity"
  
  locale Flow = Graph +
    fixes s t :: node
    fixes f :: flow
    assumes capacity_const: "\<forall>e. 0 \<le> f e \<and> f e \<le> c e"
    assumes conservation_const: "\<forall>v \<in> V - {s, t}. (\<Sum>e \<in> incoming v. f e) = (\<Sum>e \<in> outgoing v. f e)"
  begin
    definition val :: "capacity"
    where "val \<equiv> (\<Sum>e \<in> outgoing s. f e) - (\<Sum>e \<in> incoming s. f e)"
  end

  context Graph_Syntax begin    
    abbreviation Flow_val :: "graph \<Rightarrow> node \<Rightarrow> flow \<Rightarrow> capacity"
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
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
  (* Path lemmas *)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  (*@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@*)
  context Graph
  begin 
    lemma isPath_append: "isPath u (p1 @ p2) v \<longleftrightarrow> (\<exists>w. isPath u p1 w \<and> isPath w p2 v)"  
      by (induction p1 arbitrary: u) auto 
      
    lemma isPath_head: "isPath u (e#p) v \<longleftrightarrow> fst e = u \<and> e \<in> E \<and> isPath (snd e) p v"
      by (cases e) auto

    lemma isPath_head2: "isPath u (e#p) v \<Longrightarrow> (p = [] \<or> (p \<noteq> [] \<and> fst (hd p) = snd e))"
      by (metis Graph.isPath_head list.collapse)
      
    lemma isPath_tail: "isPath u (p@[e]) v \<longleftrightarrow> isPath u p (fst e) \<and> e \<in> E \<and> snd e = v"
      by (induction p) (auto simp: isPath_append isPath_head)
    
    lemma isPath_tail2: "isPath u (p@[e]) v \<Longrightarrow> (p = [] \<or> (p \<noteq> [] \<and> snd (last p) = fst e))"
      by (metis Graph.isPath_tail append_butlast_last_id)
      
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
          then have "(u, u2) \<in> E" and "(u2, v) \<in> E\<^sup>*" using E_def Cons.IH by auto
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
    lemma pathVertices_alt: "p \<noteq> [] \<Longrightarrow> pathVertices u p = map fst p @ [snd (last p)]"
      by (induction p arbitrary: u) auto
    
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
    
    lemma pathVertices_edge: "isPath u p v \<Longrightarrow> e \<in> set p \<Longrightarrow> 
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
          by (induction p arbitrary: s) (auto simp: isPath_head E_def V_alt) 
      qed

    lemma connected_refl[simp, intro!]: "connected v v" 
      unfolding connected_def by (force intro: exI[where x="[]"])

    lemma connected_edgeRtc: "connected u v \<longleftrightarrow> (u, v) \<in> E\<^sup>*"  
    proof
      assume "connected u v"
      then obtain p where "isPath u p v" by (auto simp add: connected_def)
      thus "(u,v)\<in>E\<^sup>*"
        apply (induction p arbitrary: u)
        apply (auto simp: E_def intro: converse_rtrancl_into_rtrancl)
        done
    next
      assume "(u,v)\<in>E\<^sup>*"
      thus "connected u v"
        proof (induction rule: converse_rtrancl_induct)
          case (step y z)
            from step.IH obtain p where "isPath z p v" by (auto simp add: connected_def)
            moreover from step.hyps have "(y,z) \<in> E" by (simp add: E_def)
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
        ultimately have "\<exists>vs1 vs2. pathVertices u p = vs1 @ u1 # u1 # vs2" 
          using pathVertices_edge by auto
        then obtain vs1 vs2 where "pathVertices u p = vs1 @ u1 # u1 # vs2" by blast
        then have "\<not> distinct (pathVertices u p)" 
          by (metis distinct_append distinct_length_2_or_more)
        thus "False" using asm isSimplePath_def by auto
      qed
      
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
                    using pathVertices_edge[OF obt2 `(u1, v2) \<in> (set w1)`] by auto
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
                 note pathVertices_edge[OF this `(u1, v2) \<in> (set w2)`] 
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
                    using pathVertices_edge[OF _ `(u2, v1) \<in> (set w1)`] by (metis fst_conv snd_conv)
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
                    note pathVertices_edge[OF this]
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
                    using pathVertices_edge by auto
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
                        note pathVertices_edge[OF this `(v2, u1) \<in> (set w1)`]
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
                      note pathVertices_edge[OF this `(v2, u1) \<in> (set w2)`]
                      then have " \<exists>vs1 vs2. pathVertices v1 w2 = vs1 @ v2 # u1 # vs2" by auto
                    }
                    ultimately obtain vs1 vs2 vs3 where 
                      "pathVertices u p = vs1 @ (u1 # vs2 @ v2 # u1 # vs3 )" by auto
                    then have "\<not> distinct (pathVertices u p)"
                      by (metis (mono_tags, hide_lams) Un_insert_right append_Cons distinct.simps(2)
                      distinct_append in_set_conv_decomp set_append set_simps(2))
                    thus ?thesis using asm1 isSimplePath_def by auto
                  qed
              qed
          qed
      qed
      
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
        then have "\<not> distinct (pathVertices u p)" by (metis append.simps(2) 
          distinct_append insert_iff not_distinct_conv_prefix set_simps(2))
        thus "False" using asm isSimplePath_def by auto
      qed
  end
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^*)
  (*^^^^^^^^^^^^^^^^^^^^^^^END^^^^^^^^^^^^^^^^^^^^^^^^*)
  
  
  
  
end
