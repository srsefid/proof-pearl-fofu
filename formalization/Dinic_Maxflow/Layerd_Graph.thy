theory Layerd_Graph
imports 
  Graph
begin

lemma (in Graph) isPath_connected_head1:
  assumes "isPath u p v" and "(a, b) \<in> set p"
  shows "connected u a"
using assms proof (induction arbitrary: u v a b rule:isPath.induct)
  case 1
    thus ?case by auto
next
  case (2 u' a' b' p)
  have "u = a'" and "(a', b') \<in> E" and "isPath b' p v" using "2.prems"(1) by auto
  have "(a, b) = (a', b') \<or> (a, b) \<in> set p" using "2.prems"(2) by simp
  thus ?case
  proof 
    assume "(a, b) = (a', b')"
    thus ?thesis using `u = a'` unfolding connected_def using isPath.simps(1) by blast
  next
    assume "(a, b) \<in> set p"
    then have "connected b' a" using "2.IH" `isPath b' p v` by simp
    moreover have "(u, b') \<in> E" using `u = a'` `(a', b') \<in> E` by simp
    ultimately show ?thesis unfolding connected_def  using isPath.simps(2) by blast
  qed
qed

lemma (in Graph) isPath_connected_head2: "\<lbrakk>isPath u p v; (a, b) \<in> set p\<rbrakk> \<Longrightarrow> connected u b"
proof -
  assume asm1: "isPath u p v" and asm2: "(a, b) \<in> set p"

  have "connected u a" using asm1 asm2 isPath_connected_head1 by simp
  moreover have "(a,b) \<in> E" using asm1 asm2 isPath_edgeset by simp
  ultimately show ?thesis unfolding connected_def using isPath_append_edge by blast
qed

locale Layerd_Graph = Graph +
  fixes s
  fixes t
  assumes s_node: "s \<in> V"
  assumes t_node: "t \<in> V"
begin  
  definition V_l where
    "V_l i \<equiv> {v. connected s v \<and> min_dist s v = i}"

  abbreviation V\<^sub>l where
    "V\<^sub>l i \<equiv> V_l i"

  definition isLayered where 
    "isLayered \<equiv> \<forall>(u, v)\<in>E. \<exists>i. u \<in> V\<^sub>l i \<and> v \<in> V\<^sub>l (Suc i)"

  definition isCleaned_in where
    "isCleaned_in = (\<forall>v \<in> V - {s}. incoming v \<noteq> {})"

  definition isCleaned_out where
    "isCleaned_out = (\<forall>v \<in> V - {t}. outgoing v \<noteq> {})"
  
   
  lemma V_l_zero: "V\<^sub>l 0 = {s}"
  proof
    show "V\<^sub>l 0 \<subseteq> {s}"
    proof
      fix x
      assume "x \<in> V\<^sub>l 0"
      then have "connected s x" and "min_dist s x = 0" using V_l_def connected_def by auto
      thus "x \<in> {s}" using min_dist_z_iff by simp
    qed
  next
    show "{s} \<subseteq> V\<^sub>l 0"
    proof
      fix x
      assume "x \<in> {s}"
      then have "isPath s [] x" by simp
      thus "x \<in> V\<^sub>l 0" unfolding V_l_def min_dist_def dist_def by fastforce
    qed
  qed

  lemma isLayered_V_l_ex: "\<lbrakk>isLayered; v \<in> V\<rbrakk> \<Longrightarrow> \<exists>i. v \<in> V_l i"
    unfolding isLayered_def V_def by auto

  lemma isLayered_V_l_unique: "\<lbrakk>isLayered; v \<in> V_l i; v \<in> V_l j\<rbrakk> \<Longrightarrow> i = j"
    unfolding isLayered_def V_l_def by auto

  lemma isLayered_isCleaned: "isLayered \<Longrightarrow> isCleaned_in"
  proof (rule ccontr)
    assume "isLayered"
    assume "\<not> isCleaned_in"
    then obtain v x where "v \<noteq> s" and "(v, x) \<in> E" and "incoming v = {}"
      unfolding isCleaned_in_def incoming_def V_def by blast
    
    have "\<not> connected s v"
    proof (rule ccontr)
      assume "\<not> \<not> local.connected s v"   
      then have "(s, v) \<in> E\<^sup>*" using connected_edgeRtc by blast
      then have "\<exists>x. (x, v) \<in> E" using `v \<noteq> s` by (meson rtrancl.cases)
      thus "False" using `incoming v = {}` incoming_def by blast
    qed
    then have "\<not>isLayered" unfolding isLayered_def V_l_def using `(v, x) \<in> E` by auto
    thus "False" using `isLayered` by blast
  qed

  lemma isLayared_connected:
    assumes "isLayered" and "connected u v" and "u \<in> V_l i" and "v \<in> V_l j"
    shows "i \<le> j"
  proof -
    obtain p where obt: "isPath u p v" using `connected u v` connected_def by blast
    then show ?thesis using assms(1,3,4)
    proof (induction p arbitrary: u v i j)
      case (Nil)
        thus ?case unfolding V_l_def by auto
    next
      case (Cons e p)
      obtain x where obt1: "(u, x) \<in> E" and obt2: "isPath x p v"
        using Cons.prems(1) isPath_head by (cases e) auto
      then obtain i' where obt3: "x \<in> V_l i'" using isLayered_V_l_ex[OF Cons.prems(2)] V_def by auto

      obtain d where obt4: "u \<in> V_l d \<and> x \<in> V_l (Suc d)" using obt1 Cons.prems(2) isLayered_def by blast      
      then have "d = i" and "Suc d = i'" using Cons.prems(3) obt3 isLayered_V_l_unique[OF Cons.prems(2)] by auto

      from this have "i \<le> i'" by simp
      also have "i' \<le> j" using Cons.IH[of x v i' j] obt2 Cons.prems(2) obt3 Cons.prems(4) by simp
      finally show ?case .
    qed
  qed

  lemma isLayered_all_paths_simple: "\<lbrakk>isLayered; u \<in> V; v \<in> V; isPath u p v\<rbrakk> \<Longrightarrow> isSimplePath u p v"
  proof (induction rule:isPath.induct)
    case (2 u u' w p v)             
    have "u = u'" and "w \<in> V" and "(u', w) \<in> E" and "isPath w p v" using "2.prems"(4) V_def by auto
    have "u' \<noteq> w" using "2.prems"(1) `(u', w) \<in> E` unfolding isLayered_def V_l_def by auto
    have "connected u w" using `u = u'` `(u', w) \<in> E` connected_def connected_edgeRtc by blast
    
    have "distinct (pathVertices w p)" 
      using "2.IH" "2.prems"(1,3) isSimplePath_def `w \<in> V` `isPath w p v` by blast
    moreover have "u' \<notin> set (pathVertices w p)"
    proof (cases "p = []")
      case True
      then show ?thesis using `u' \<noteq> w` by auto
    next
      case False
      show ?thesis
      proof (rule ccontr)
        assume "\<not> u' \<notin> set (pathVertices w p)"
        then have "u' \<in> set (pathVertices_fwd w p)" using pathVertices_fwd[OF `isPath w p v`] by simp
        then obtain x where "(x, u') \<in> set p" using pathVertices_fwd_def `u' \<noteq> w` by auto
        then have "connected w u'" using `isPath w p v` isPath_connected_head2 by blast

        obtain i1 i2 where "u \<in> V\<^sub>l i1" and "u' \<in> V\<^sub>l i1" and "w \<in> V\<^sub>l i2"
          using isLayered_V_l_ex "2.prems"(1) `w \<in> V` "2.prems"(2) `u = u'` by blast
        moreover obtain d where "u' \<in> V_l d \<and> w \<in> V_l (Suc d)" 
          using  "2.prems"(1) isLayered_def `(u', w) \<in> E` by blast
        ultimately have *: "i1 = d" and **:"i2 = Suc d" using isLayered_V_l_unique "2.prems"(1) by auto
        
        have "i2 \<le> i1" using `connected w u'` `u' \<in> V\<^sub>l i1` `w \<in> V\<^sub>l i2` 
          "2.prems"(1) isLayared_connected by blast
        also have "i1 \<le> i2" using `connected u w` `u \<in> V\<^sub>l i1` `w \<in> V\<^sub>l i2` 
          "2.prems"(1) isLayared_connected by blast
        finally have ***: "i1 = i2" by simp

        show False using * ** *** by auto
      qed
    qed
    ultimately have "distinct (pathVertices u ((u', w) # p))" by auto
    thus ?case unfolding isSimplePath_def using "2.prems"(4) by blast
  qed auto
         
  lemma isLayered_connected_s: 
    assumes "isLayered" and "v \<in> V"
    shows "connected s v"
    using assms by (auto simp add: V_def isLayered_def V_l_def)
 
  lemma isLCO_vertices_distance: 
    assumes isL: "isLayered"
    assumes isC_o: "isCleaned_out"
    assumes v_in: "v \<in> V"
    assumes V_finite: "finite V"
    shows "connected v t"
    proof (cases "v = t")
      case False
      
      let ?SC = "{v. v\<in> V \<and> connected v t}"
      let ?SN = "{v. v\<in> V \<and> \<not>connected v t}"
      have "finite ?SC" and "finite ?SN" using V_finite by auto
      have "V = ?SC \<union> ?SN" and "?SC \<inter> ?SN = {}" by auto
      moreover have "?SN = {}"
      proof (rule ccontr)
        assume "\<not> ?SN = {}"
        let ?last_vertex = 
          "SOME v. v \<in> ?SN \<and> (\<exists>d. dist s d v \<and> (\<forall>v' d'. v' \<in> ?SN \<and> dist s d' v' \<longrightarrow> d' \<le> d))"

find_theorems name:Hilbert_Choice finite
        

        
        obtain u where "u \<in> V" and "\<not>connected u t" using `\<not> ?SN = {}` by blast
        then obtain w where "(u, w) \<in> E" using isC_o unfolding isCleaned_out_def outgoing_def by blast
        
        find_theorems Sup
      
      show ?thesis sorry
    qed auto
    

..
    
    shows "(\<forall>v\<in>V. connected s v \<and> connected v t \<and> (\<exists>i. min_dist s v = i \<and> min_dist v t = d - i))"
  proof
    have isC_i: "isCleaned_in" using `isLayered` isLayered_isCleaned by blast
    have s_t_con: "connected s t" 
     and s_t_dis: "min_dist s t = d" using t_lay V_l_def by auto

    fix v
    assume v_in: "v \<in> V"

    have "connected s v" using v_in V_def isL isLayered_def V_l_def by auto
    have "connected v t"
    proof (rule ccontr)
      
    


    show "connected s v \<and> connected v t \<and> (\<exists>i. min_dist s v = i \<and> min_dist v t = d - i)" sorry
  qed


end


end