section \<open>Residual Graph\<close>
theory ResidualGraph
imports Network
begin
text \<open>
  In this theory, we define the residual graph.
  \<close>

subsection \<open>definition\<close>
text \<open>The \emph{residual graph} of a network and a flow indicates how much 
  flow can be effectively pushed along or reverse to a network edge,
  by increasing or decreasing the flow on that edge:\<close>
definition residualGraph :: "_ graph \<Rightarrow> _ flow \<Rightarrow> _ graph"
where "residualGraph c f \<equiv> \<lambda>(u, v).
  if (u, v) \<in> Graph.E c then
    c (u, v) - f (u, v)
  else if (v, u) \<in> Graph.E c then
    f (v, u)
  else
    0"

(*<*) (* Old syntax, not used any more *)
  notation (in Graph_Syntax) residualGraph ("\<langle>\<C>\<^sub>\<f>/ _,/ _\<rangle>" 1000)
(*>*)

text \<open>Let's fix a network with a flow @{term f} on it\<close>
context NFlow
begin
  text \<open>We abbreviate the residual graph by @{term cf}.\<close>
  abbreviation "cf \<equiv> residualGraph c f"
  sublocale cf!: Graph cf .
  lemmas cf_def = residualGraph_def[of c f]

subsection \<open>Properties\<close>

text \<open>The edges of the residual graph are either parallel or reverse 
  to the edges of the network.\<close>
lemma cfE_ss_invE: "Graph.E cf \<subseteq> E \<union> E\<inverse>"
  unfolding residualGraph_def Graph.E_def
  by auto

text \<open>The nodes of the residual graph are exactly the nodes of the network.\<close>
lemma resV_netV[simp]: "cf.V = V"
proof
  show "V \<subseteq> Graph.V cf"
  proof 
    fix u
    assume "u \<in> V"
    then obtain v where "(u, v) \<in> E \<or> (v, u) \<in> E" unfolding V_def by auto
    (* TODO: Use nifty new Isabelle2016 case-distinction features here! *)
    moreover {
      assume "(u, v) \<in> E"
      then have "(u, v) \<in> Graph.E cf \<or> (v, u) \<in> Graph.E cf"
      proof (cases)
        assume "f (u, v) = 0"
        then have "cf (u, v) = c (u, v)"
          unfolding residualGraph_def using `(u, v) \<in> E` by (auto simp:)
        then have "cf (u, v) \<noteq> 0" using `(u, v) \<in> E` unfolding E_def by auto
        thus ?thesis unfolding Graph.E_def by auto
      next
        assume "f (u, v) \<noteq> 0"
        then have "cf (v, u) = f (u, v)" unfolding residualGraph_def
          using `(u, v) \<in> E` no_parallel_edge by auto
        then have "cf (v, u) \<noteq> 0" using \<open>f (u, v) \<noteq> 0\<close> by auto
        thus ?thesis unfolding Graph.E_def by auto
      qed
    } moreover {
      assume "(v, u) \<in> E"
      then have "(v, u) \<in> Graph.E cf \<or> (u, v) \<in> Graph.E cf"
      proof (cases)
        assume "f (v, u) = 0"
        then have "cf (v, u) = c (v, u)"
          unfolding residualGraph_def using `(v, u) \<in> E` by (auto)
        then have "cf (v, u) \<noteq> 0" using `(v, u) \<in> E` unfolding E_def by auto
        thus ?thesis unfolding Graph.E_def by auto
      next
        assume "f (v, u) \<noteq> 0"
        then have "cf (u, v) = f (v, u)" unfolding residualGraph_def
          using `(v, u) \<in> E` no_parallel_edge by auto
        then have "cf (u, v) \<noteq> 0" using \<open>f (v, u) \<noteq> 0\<close> by auto
        thus ?thesis unfolding Graph.E_def by auto
      qed
    } ultimately show "u\<in>cf.V" unfolding cf.V_def by auto
  qed  
next
  show "Graph.V cf \<subseteq> V" using cfE_ss_invE unfolding Graph.V_def by auto
qed

text \<open>Note, that Isabelle is powerful enough to prove the above case 
  distinctions completely automatically, although it takes some time:\<close>
lemma "cf.V = V"
  unfolding residualGraph_def Graph.E_def Graph.V_def
  using no_parallel_edge[unfolded E_def]
  by auto
  
text \<open>As the residual graph has the same nodes as the network, it is also finite:\<close>
(* TODO: Move. Interpret finite-graph for cf, and move lemmas in general form their *)
lemma finite_cf_incoming[simp, intro!]: "finite (cf.incoming v)" 
  unfolding cf.incoming_def 
  apply (rule finite_subset[where B="V\<times>V"])
  using cf.E_ss_VxV by auto

lemma finite_cf_outgoing[simp, intro!]: "finite (cf.outgoing v)" 
  unfolding cf.outgoing_def 
  apply (rule finite_subset[where B="V\<times>V"])
  using cf.E_ss_VxV by auto

text \<open>The capacities on the edges of the residual graph are non-negative\<close>
lemma resE_nonNegative: "cf e \<ge> 0"
proof -
  obtain u v where obt: "e = (u, v)" by (cases e)
  have "((u, v) \<in> E \<or> (v, u) \<in> E) \<or> ((u, v) \<notin> E \<and> (v, u) \<notin> E)" by blast
  thus ?thesis
  proof
    assume "(u, v) \<in> E \<or> (v, u) \<in> E"
    thus ?thesis
    proof
      assume "(u, v) \<in> E"
      then have "cf e = c e - f e" using cf_def obt by auto
      thus ?thesis using capacity_const cap_positive obt 
        by (metis diff_0_right diff_eq_diff_less_eq eq_iff 
          eq_iff_diff_eq_0 linear)
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

text \<open>Again, there is an almost automatic proof, which can be easily found 
  using the sledgehammer tool for the final arithmetic argument.\<close>
lemma "cf e \<ge> 0"
  apply (cases e)
  unfolding residualGraph_def
  using no_parallel_edge capacity_const cap_positive
  apply clarsimp
  by (metis diff_0_right diff_eq_diff_less_eq eq_iff 
    eq_iff_diff_eq_0 linear)


text \<open>All edges of the residual graph are labeled with positive capacities:\<close>
corollary resE_positive: "e \<in> cf.E \<Longrightarrow> cf e > 0"
proof -
  assume "e \<in> cf.E"
  hence "cf e \<noteq> 0" unfolding cf.E_def by auto
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

end -- \<open>Network with flow\<close>
  
end
