theory Layerd_Graph
imports 
  Graph
begin

lemma  (in Graph) isPath_transfer: "\<lbrakk>isPath u p v; set p \<subseteq> Graph.E c'\<rbrakk> \<Longrightarrow> Graph.isPath c' u p v"
proof (induction arbitrary: u v rule:isPath.induct)
  case 1
    thus ?case using isPath.simps(1) Graph.isPath.simps(1) by blast
next
  case (2 a x y p)
  then have "Graph.isPath c' y p v" and "(x, y) \<in> Graph.E c'" and "u = x" by auto
  thus ?case using Graph.isPath.simps(2) by blast
qed

lemma (in Graph) isSimplePath_transfer: 
  assumes "isSimplePath u p v"
      and "set p \<subseteq> Graph.E c'"
    shows "Graph.isSimplePath c' u p v"
proof -
  have "Graph.isPath c' u p v" using assms isPath_transfer unfolding isSimplePath_def by auto
  moreover have "distinct (pathVertices u p)" using assms(1) unfolding isSimplePath_def by blast
  ultimately show ?thesis unfolding Graph.isSimplePath_def by blast
qed

lemma (in Graph) isShortestPath_transfer:
  assumes "isShortestPath u p v"
      and "Graph.E c' \<subseteq> E"
      and "set p \<subseteq> Graph.E c'"
    shows "Graph.isShortestPath c' u p v"
proof -
  have "isSimplePath u p v" using assms(1) shortestPath_is_simple by blast
  then have "Graph.isSimplePath c' u p v" using assms(3) isSimplePath_transfer by blast
  
  show ?thesis
  proof (rule ccontr)
    assume c_asm: "\<not> Graph.isShortestPath c' u p v"
    then obtain p' where obt: "Graph.isShortestPath c' u p' v" using `Graph.isSimplePath c' u p v`
      unfolding Graph.isSimplePath_def by (meson Graph.connected_def Graph.obtain_shortest_path)

    have *: "length p' < length p"  using `Graph.isSimplePath c' u p v` obt c_asm
      unfolding Graph.isShortestPath_def Graph.isSimplePath_def by auto

    have "Graph.isPath c' u p' v" using Graph.shortestPath_is_path[OF obt] .
    then have "set p' \<subseteq> E" using Graph.isPath_edgeset assms(2) subset_eq by blast
    then have "isPath u p' v" using Graph.isPath_transfer[OF `Graph.isPath c' u p' v`, of c] by blast
    thus False using assms(1) * unfolding isShortestPath_def by auto
  qed
qed


lemma (in Graph) isPath_head_connected_edge1:
  assumes "isPath u p v"
      and "(a, b) \<in> set p"
  shows "connected u a"
using assms proof (induction arbitrary: u v a b rule:isPath.induct)
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
qed auto

lemma (in Graph) isPath_head_connected_edge2: "\<lbrakk>isPath u p v; (a, b) \<in> set p\<rbrakk> \<Longrightarrow> connected u b"
proof -
  assume asm1: "isPath u p v" and asm2: "(a, b) \<in> set p"

  have "connected u a" using asm1 asm2 isPath_head_connected_edge1 by simp
  moreover have "(a,b) \<in> E" using asm1 asm2 isPath_edgeset by simp
  ultimately show ?thesis unfolding connected_def using isPath_append_edge by blast
qed

(* TODO: did not use these lemmas yet, I have only proved them to have a complete set of rules*)
lemma (in Graph) isPath_tail_connected_edge1:
  assumes "isPath u p v"
      and "(a, b) \<in> set p"
  shows "connected b v"
using assms proof (induction arbitrary: u v a b rule:isPath.induct)
  case (2 u' a' b' p)
  have "isPath b' p v" using "2.prems"(1) by auto
  have "(a, b) = (a', b') \<or> (a, b) \<in> set p" using "2.prems"(2) by simp
  thus ?case
  proof 
    assume "(a, b) = (a', b')"
    thus ?thesis using `isPath b' p v` unfolding connected_def by blast
  next
    assume "(a, b) \<in> set p"
    thus ?thesis using "2.IH" `isPath b' p v` by blast
  qed
qed auto

lemma (in Graph) isPath_tail_connected_edge2: "\<lbrakk>isPath u p v; (a, b) \<in> set p\<rbrakk> \<Longrightarrow> connected a b"
proof -
  assume asm1: "isPath u p v" and asm2: "(a, b) \<in> set p"

  have "connected b v" using asm1 asm2 isPath_tail_connected_edge1 by simp
  moreover have "(a,b) \<in> E" using asm1 asm2 isPath_edgeset by simp
  ultimately show ?thesis using connected_append_edge connected_def by blast
qed
(* END todo *)


context Graph
begin
  definition VL where
    "VL s i \<equiv> {v. connected s v \<and> min_dist s v = i}"

  (* Layered With the Root *)
  definition layered where
    "layered s \<equiv> \<forall>(u, v)\<in>E. \<exists>i. u \<in> VL s i \<and> v \<in> VL s (Suc i)"

  (* All With Incoming Edges Except *)
  definition awin_except where
    "awin_except s \<equiv> (\<forall>v \<in> V - {s}. incoming v \<noteq> {})"

  (* All With outgoing Edges Except *)
  definition awout_except where
    "awout_except t = (\<forall>v \<in> V - {t}. outgoing v \<noteq> {})"

  lemma VL_of_zero: 
      shows "VL s 0 = {s}"
  proof
    show "VL s 0 \<subseteq> {s}"
    proof
      fix x
      assume "x \<in> VL s 0"
      then have "connected s x" and "min_dist s x = 0" using VL_def connected_def by auto
      thus "x \<in> {s}" using min_dist_z_iff by simp
    qed
  next
    show "{s} \<subseteq> VL s 0"
    proof
      fix x
      assume "x \<in> {s}"
      then have "isPath s [] x" by simp
      thus "x \<in> VL s 0" unfolding VL_def min_dist_def dist_def by fastforce
    qed
  qed

  lemma VL_unique: "\<lbrakk>v \<in> VL s i; v \<in> VL s j\<rbrakk> \<Longrightarrow> i = j"
    unfolding VL_def by auto

  lemma VL_isShortestPath1: 
    assumes "v \<in> VL s i"
      shows "\<exists>p. isShortestPath s p v \<and> length p = i"
  proof -
    have "connected s v" and "min_dist s v = i" using assms unfolding VL_def by auto
    thus ?thesis using isShortestPath_min_dist_def by (meson obtain_shortest_path)
  qed

  lemma VL_isShortestPath2: 
    assumes "isShortestPath s p v"
      shows "v \<in> VL s (length p)"
  proof -
    have "connected s v" and "min_dist s v = length p" using assms isShortestPath_min_dist_def
      unfolding connected_def by auto
    thus ?thesis unfolding VL_def by blast
  qed

  lemma layered_VL_exists: "\<lbrakk>layered s; v \<in> V\<rbrakk> \<Longrightarrow> \<exists>i. v \<in> VL s i"
    unfolding layered_def V_def by auto

  lemma layered_awin_except: 
    assumes "layered s"
      shows "awin_except s"
  proof (rule ccontr)
    assume "\<not> awin_except s"
    then obtain v x where "v \<noteq> s" and "(v, x) \<in> E" and "incoming v = {}"
      unfolding awin_except_def incoming_def V_def by blast
    
    have "\<not> connected s v"
    proof (rule ccontr)
      assume "\<not> \<not> connected s v"   
      then have "\<exists>x. (x, v) \<in> E" using `v \<noteq> s` connected_edgeRtc by (meson rtrancl.cases)
      thus "False" using `incoming v = {}` incoming_def by blast
    qed
    then have "\<not>layered s" unfolding layered_def VL_def using `(v, x) \<in> E` by auto
    thus "False" using `layered s` by blast
  qed

  lemma layared_connected_nodes_ids:
    assumes "layered s" 
        and "connected u v"
        and "u \<in> VL s i" 
        and "v \<in> VL s j"
      shows "i \<le> j"
  proof -
    obtain p where "isPath u p v" using `connected u v` connected_def by blast
    then show ?thesis using assms(1,3,4)
    proof (induction p arbitrary: u v i j)
      case (Nil)
        thus ?case unfolding VL_def by auto
    next
      case (Cons e p)
      obtain w where "(u, w) \<in> E" and "isPath w p v" using Cons.prems(1) isPath_head by (cases e) auto
      obtain i' where "w \<in> VL s i'" using `(u, w) \<in> E` layered_VL_exists[OF Cons.prems(2)] V_def by auto
      obtain d where "u \<in> VL s d \<and> w \<in> VL s (Suc d)" using `(u, w) \<in> E` Cons.prems(2) layered_def by blast      
      then have *: "d = i \<and> Suc d = i'" using `w \<in> VL s i'` Cons.prems(3) VL_unique by auto

      have "i \<le> i'" using * by simp
      also have "i' \<le> j" using `isPath w p v` `w \<in> VL s i'` Cons.IH Cons.prems(2)  Cons.prems(4) by simp
      finally show ?case .
    qed
  qed

  lemma layered_path_length: "\<lbrakk>layered s; u \<in> V; v \<in> V; isPath u p v; u \<in> VL s i; v \<in> VL s j\<rbrakk> 
    \<Longrightarrow> length p + i = j"
  proof (induction p arbitrary: u v i j)
    case Nil
    thus ?case using isPath.simps(1) list.size(3) VL_def by auto
  next
    case (Cons e p)
    then obtain x y where "e = (x, y)" by (cases e)
    then have "isPath y p v" and "(u, y) \<in> E" and "y \<in> V" using Cons.prems(4) V_def by auto
    then obtain k where "y \<in> VL s k" using layered_VL_exists[OF Cons.prems(1)] by blast

    obtain d where "u \<in> VL s d" and "y \<in> VL s (Suc d)" using `(u, y) \<in> E` Cons.prems(1) layered_def by blast
    then have "k = Suc d" and "d = i" using VL_unique `y \<in> VL s k` Cons.prems(5) by auto
    then have "k = Suc i" by blast
    moreover have "length p + k = j" using Cons.IH `isPath y p v` `y \<in> VL s k` `y \<in> V` 
      Cons.prems(1) Cons.prems(3) Cons.prems(6) by blast
    moreover have "length (e # p) = length p + 1" by simp
    ultimately show ?case by auto
  qed

  lemma layered_path_shortestPath: 
    assumes "layered s"
        and "u \<in> V"
        and "v \<in> V"
      shows "isPath u p v \<longleftrightarrow> isShortestPath u p v" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    show ?R
    proof (rule ccontr)
      assume "\<not>isShortestPath u p v"
      
      obtain p1 where "isPath u p1 v" and "length p1 < length p"
        using isShortestPath_def `isPath u p v` `\<not>isShortestPath u p v` by auto
      obtain i j where "u \<in> VL s i" and "v \<in> VL s j" 
        using layered_VL_exists `layered s` `u \<in> V` `v \<in> V` by metis    
  
      have "length p + i = j"  using layered_path_length 
        `layered s` `u \<in> V` `v \<in> V` `u \<in> VL s i` `v \<in> VL s j` `isPath u p v` by blast
      moreover have "length p1 + i = j"  using layered_path_length 
        `layered s` `u \<in> V` `v \<in> V` `u \<in> VL s i` `v \<in> VL s j` `isPath u p1 v` by blast
      ultimately have "length p = length p1" by simp
      thus False using `length p1 < length p` by simp
    qed
  next
    assume ?R
    thus ?L using shortestPath_is_path by blast
  qed
  
  lemma layered_connected_s: 
    assumes "layered s" 
        and "v \<in> V"
      shows "connected s v"
    using assms by (auto simp add: V_def layered_def VL_def)

  lemma layered_awout_connected_t: 
    assumes "layered s"
        and "awout_except t"
        and "finite V"
        and "v \<in> V"
      shows "connected v t"
  proof (cases "v = t")
    case False
    
    let ?SC = "{v. v\<in> V \<and> connected v t}"
    let ?SN = "{v. v\<in> V \<and> \<not>connected v t}"

    have "V = ?SC \<union> ?SN" and "?SC \<inter> ?SN = {}" by auto
    have "finite ?SC" and "finite ?SN" using `finite V` by auto    
    have "?SN = {}"
    proof (rule ccontr)
      assume "\<not> ?SN = {}"
      
      let ?SN_mds = "{min_dist s v|v. v \<in> ?SN}"
      let ?MAX_d = "Max ?SN_mds"

      {
        have h1:"finite ?SN_mds" using `finite ?SN` by auto
        moreover have h2: "?SN_mds \<noteq> {}"
        proof -
          obtain x where "x \<in>?SN" using `\<not> ?SN = {}` by blast
          then have "connected s x" using layered_connected_s[OF `layered s`] by blast
          then obtain d where "min_dist s x = d" unfolding min_dist_def dist_def connected_def by auto
          then have "d \<in> ?SN_mds" using `x \<in>?SN` by blast
          thus ?thesis by auto
        qed
        ultimately have h3: "?MAX_d \<in> ?SN_mds" using Max_in by blast
        note h1 h2 h3
      }

      obtain last_v where "last_v \<in> ?SN" and "min_dist s last_v = ?MAX_d" 
        using `?MAX_d \<in> ?SN_mds` by auto

      have "w \<in> ?SN \<Longrightarrow> (last_v, w) \<notin> E" for w
      proof (rule ccontr)
        assume "w \<in> ?SN"
        assume "\<not> (last_v, w) \<notin> E"
        then have "min_dist s w = Suc (min_dist s last_v)" using `layered s` layered_def VL_def by auto
        moreover have "v \<in> ?SN \<Longrightarrow> min_dist s v \<le> min_dist s last_v" for v 
          using `min_dist s last_v = ?MAX_d` `finite ?SN_mds` `?SN_mds \<noteq> {}` Max.bounded_iff by auto
        ultimately show False using `w \<in> ?SN` by force
      qed
      moreover obtain n where "(last_v, n) \<in> E" using `awout_except t` `last_v \<in> ?SN`
        unfolding awout_except_def outgoing_def by auto
      ultimately have "n \<notin> ?SN" and "n \<in> V" and "last_v \<in> V" unfolding V_def by auto

      then have "connected n t" using `V = ?SC \<union> ?SN` `?SC \<inter> ?SN = {}` by auto
      then have "connected last_v t"  unfolding connected_def
        using `(last_v, n) \<in> E`  isPath.simps(2) by blast
      then have "last_v \<in> ?SC" using `last_v \<in> V` by auto
      then have "?SC \<inter> ?SN \<noteq> {}" using `last_v \<in> ?SN` by blast
      thus False using `?SC \<inter> ?SN = {}` by blast
    qed

    show ?thesis using `v \<in> V` `V = ?SC \<union> ?SN` `?SC \<inter> ?SN = {}` `?SN = {}`  by blast
  qed auto
end


    

context Graph
begin
  definition layeredSubGraph where
    "layeredSubGraph g s \<equiv> (\<forall>e \<in> (Graph.E g). g e = c e) \<and>
      Graph.E g = {(u, v)|u v. (\<exists>i. u \<in> VL s i \<and> v \<in> VL s (Suc i))}"

  definition awout_exceptSubGraph where
    "awout_exceptSubGraph g t \<equiv> (\<forall>e \<in> (Graph.E g). g e = c e) \<and>
      Graph.V g = {v. v \<in> V \<and>  (v \<noteq> t \<longrightarrow> outgoing v \<noteq> {})}"

  lemma layeredSubGraph_subset_Edges: 
    assumes "layeredSubGraph g s"
      shows "Graph.E g \<subseteq> E"
  proof
    fix x
    assume "x \<in> Graph.E g"
    then have "g x \<noteq> 0" unfolding Graph.E_def by blast
    then have "c x \<noteq> 0" using assms `x \<in> Graph.E g` unfolding layeredSubGraph_def by simp
    thus "x \<in> E" unfolding E_def by blast
  qed

  lemma layeredSubGraph_shortestPath_EdgeSet:
    assumes "layeredSubGraph g s"
        and "isShortestPath s p v"
      shows "set p \<subseteq> Graph.E g"
  proof
    fix x
    assume asm: "x \<in> set p"
    obtain u v where obt: "x = (u, v)" by (cases x)

    have "min_dist s v = min_dist s u + 1" 
      using isShortestPath_level_edge(4) assms(2) asm obt by simp
    moreover have "connected s u" using shortestPath_is_path[OF assms(2)] 
      isPath_head_connected_edge1 asm obt by simp
    moreover have "connected s v" using shortestPath_is_path[OF assms(2)]
      isPath_head_connected_edge2 asm obt by simp
    ultimately show "x \<in> Graph.E g" using asm obt assms(1) unfolding layeredSubGraph_def VL_def
      by auto
  qed    

  lemma layeredSubGraph_shortestPaths:
    assumes "layeredSubGraph g s"
      shows "isShortestPath s p v \<longleftrightarrow> Graph.isShortestPath g s p v" (is "?L \<longleftrightarrow> ?R")
  proof
    assume "?L"
    then have "set p \<subseteq> Graph.E g" using assms layeredSubGraph_shortestPath_EdgeSet by blast
    thus "?R" using isShortestPath_transfer[OF `?L` layeredSubGraph_subset_Edges[OF assms]] by simp
  next
    assume "?R"
    
    show "?L" sorry
  qed



end


end