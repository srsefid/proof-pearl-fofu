theory Layerd_Graph
imports 
  Graph
begin

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

  (* CAN be derived as a collorary from the next lemma

  lemma layered_path_simplePath: "\<lbrakk>layered s; u \<in> V; v \<in> V; isPath u p v\<rbrakk> \<Longrightarrow> isSimplePath u p v"
  proof (induction rule:isPath.induct)
    case (2 u u' w p v)             
    have "u = u'" and "w \<in> V" and "(u', w) \<in> E" and "isPath w p v" using "2.prems"(4) V_def by auto
    have "u' \<noteq> w" using "2.prems"(1) `(u', w) \<in> E` unfolding layered_def VL_def by auto
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
        then have "connected w u'" using `isPath w p v` isPath_head_connected_edge2 by blast

        obtain i1 i2 where "u \<in> VL s i1" and "u' \<in> VL s i1" and "w \<in> VL s i2"
          using layered_VL_exists "2.prems"(1) `w \<in> V` "2.prems"(2) `u = u'` by blast
        moreover obtain d where "u' \<in> VL s d \<and> w \<in> VL s (Suc d)" 
          using  "2.prems"(1) layered_def `(u', w) \<in> E` by blast
        ultimately have *: "i1 = d" and **:"i2 = Suc d" using VL_unique by auto
        
        have "i2 \<le> i1" using `connected w u'` `u' \<in> VL s i1` `w \<in> VL s i2` 
          "2.prems"(1) layared_connected_nodes_ids by blast
        also have "i1 \<le> i2" using `connected u w` `u \<in> VL s i1` `w \<in> VL s i2` 
          "2.prems"(1) layared_connected_nodes_ids by blast
        finally have ***: "i1 = i2" by simp

        show False using * ** *** by auto
      qed
    qed
    ultimately have "distinct (pathVertices u ((u', w) # p))" by auto
    thus ?case unfolding isSimplePath_def using "2.prems"(4) by blast
  qed auto *)

  lemma layered_path_shortestPath: 
    assumes "layered s"
        and "u \<in> V"
        and "v \<in> V"
        and "isPath u p v"
      shows "isShortestPath u p v"
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

  (*corollary layered_path_simplePath: "\<lbrakk>layered s; u \<in> V; v \<in> V; isPath u p v\<rbrakk> \<Longrightarrow> isSimplePath u p v"
    using layered_path_shortestPath shortestPath_is_simple by blast*)
  
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


end