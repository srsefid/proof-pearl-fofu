section \<open>Flows, Cuts, and Networks\<close>
theory Network
imports Graph
begin
text \<open>
  In this theory, we define the basic concepts of flows, cuts, 
  and (flow) networks.
  \<close>  

subsection \<open>Definitions\<close>

subsubsection \<open>Flows\<close>

type_synonym 'capacity flow = "edge \<Rightarrow> 'capacity"

locale Preflow = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s t :: node
  fixes f :: "'capacity flow"  
  (* TODO: Move \<forall>-quantifiers to meta-level!? *)
  assumes capacity_const: "\<forall>e. 0 \<le> f e \<and> f e \<le> c e"
  assumes no_deficient_nodes: "\<forall>v \<in> V-{s,t}.
    (\<Sum>e\<in>outgoing v. f e) \<le> (\<Sum>e\<in>incoming v. f e)" 
begin
definition excess :: "node \<Rightarrow> 'capacity" where
  "excess v \<equiv> (\<Sum>e\<in>incoming v. f e) - (\<Sum>e\<in>outgoing v. f e)"

lemma excess_non_negative: "\<forall>v\<in>V-{s,t}. excess v \<ge> 0"
  unfolding excess_def using no_deficient_nodes by auto
end  
  
  
text \<open>An $s$-$t$ flow on a graph is a labeling of the edges with 
  real values, such that: 
  \begin{description}
    \item[capacity constraint] the flow on each edge is non-negative and 
      does not exceed the edge's capacity;
    \item[conservation constraint] for all nodes except $s$ and $t$, 
      the incoming flows equal the outgoing flows.
  \end{description}    
\<close>

locale Flow = Preflow c s t f
  for c :: "'capacity::linordered_idom graph"
  and s t :: node
  and f +
  assumes no_active_nodes: 
    "\<forall>v \<in> V - {s,t}. (\<Sum>e\<in>outgoing v. f e) \<ge> (\<Sum>e\<in>incoming v. f e)"
begin
  lemma conservation_const: "\<forall>v \<in> V - {s, t}. 
    (\<Sum>e \<in> incoming v. f e) = (\<Sum>e \<in> outgoing v. f e)"
    using no_deficient_nodes no_active_nodes 
    by force
  
  text \<open>The value of a flow is the flow that leaves $s$ and does not return.\<close>
  definition val :: "'capacity"
    where "val \<equiv> (\<Sum>e \<in> outgoing s. f e) - (\<Sum>e \<in> incoming s. f e)"
end

locale Finite_Preflow = Preflow c s t f + Finite_Graph c 
  for c :: "'capacity::linordered_idom graph" and s t f
  
locale Finite_Flow = Flow c s t f + Finite_Preflow c s t f
  for c :: "'capacity::linordered_idom graph" and s t f


subsubsection \<open>Cuts\<close>
text \<open>A cut is a partitioning of the nodes into two sets. 
  We define it by just specifying one of the partitions.\<close>
type_synonym cut = "node set" 

locale Cut = Graph +  (* TODO: We probably do not need the cut-locale, 
  only NCut.*)
  fixes k :: cut
  assumes cut_ss_V: "k \<subseteq> V"

subsubsection \<open>Networks\<close>
text \<open>A network is a finite graph with two distinct nodes, source and sink, 
  such that all edges are labeled with positive capacities. 
  Moreover, we assume that 
  \begin{itemize}
    \item the source has no incoming edges, and the sink has no outgoing edges
    \item we allow no parallel edges, i.e., for any edge, the reverse edge must not be in the network
    \item Every node must lay on a path from the source to the sink
  \end{itemize}
\<close>

locale Network = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s t :: node
  assumes s_node[simp, intro!]: "s \<in> V"
  assumes t_node[simp, intro!]: "t \<in> V"
  assumes s_not_t[simp, intro!]: "s \<noteq> t"
  assumes cap_non_negative: "\<forall>u v. c (u, v) \<ge> 0"
  assumes no_incoming_s: "\<forall>u. (u, s) \<notin> E"
  assumes no_outgoing_t: "\<forall>u. (t, u) \<notin> E"
  assumes no_parallel_edge: "\<forall>u v. (u, v) \<in> E \<longrightarrow> (v, u) \<notin> E"
  assumes nodes_on_st_path: "\<forall>v \<in> V. connected s v \<and> connected v t"
  assumes finite_reachable: "finite (reachableNodes s)"
begin
  text \<open>Our assumptions imply that there are no self loops\<close>
  lemma no_self_loop: "\<forall>u. (u, u) \<notin> E"
    using no_parallel_edge by auto

  text \<open>A flow is maximal, if it has a maximal value\<close>  
  definition isMaxFlow :: "_ flow \<Rightarrow> bool" 
  where "isMaxFlow f \<equiv> Flow c s t f \<and> 
    (\<forall>f'. Flow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
    
  lemma t_not_s[simp]: "t \<noteq> s" using s_not_t by blast
    
end  
  
subsubsection \<open>Networks with Flows and Cuts\<close>  
text \<open>For convenience, we define locales for a network with a fixed flow,
  and a network with a fixed cut\<close>

locale NPreflow = Network c s t + Preflow c s t f 
  for c :: "'capacity::linordered_idom graph" and s t f
begin
lemma excess_nodes_only: "excess v > 0 \<Longrightarrow> v \<in> V"  
  unfolding excess_def incoming_def outgoing_def V_def 
  using sum.not_neutral_contains_not_neutral by fastforce
  
lemma excess_non_negative: "\<forall>v \<in> V - {s}. excess v \<ge> 0"
proof -
  have "excess t \<ge> 0" unfolding excess_def outgoing_def 
    by (auto simp add: no_outgoing_t capacity_const sum_nonneg)
  thus ?thesis using excess_non_negative by blast
qed 
end
    
locale NFlow = NPreflow c s t f + Flow c s t f 
  for c :: "'capacity::linordered_idom graph" and s t f

lemma (in Network) isMaxFlow_alt: 
  "isMaxFlow f \<longleftrightarrow> NFlow c s t f \<and> 
    (\<forall>f'. NFlow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
  unfolding isMaxFlow_def     
  by (auto simp: NFlow_def Flow_def NPreflow_def) intro_locales  

text \<open>A cut in a network separates the source from the sink\<close>
locale NCut = Network c s t + Cut c k 
  for c :: "'capacity::linordered_idom graph" and s t k +
  assumes s_in_cut: "s \<in> k"
  assumes t_ni_cut: "t \<notin> k"
begin
  text \<open>The capacity of the cut is the capacity of all edges going from the 
    source's side to the sink's side.\<close>
  definition cap :: "'capacity"
    where "cap \<equiv> (\<Sum>e \<in> outgoing' k. c e)"
end

text \<open>A minimum cut is a cut with minimum capacity.\<close> 
(* TODO: The definitions of min-cut and max-flow are done in different contexts. 
  Align, probably both in network context! *)
definition isMinCut :: "_ graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cut \<Rightarrow> bool" 
where "isMinCut c s t k \<equiv> NCut c s t k \<and>
  (\<forall>k'. NCut c s t k' \<longrightarrow> NCut.cap c k \<le> NCut.cap c k')"

subsection \<open>Properties\<close>
subsubsection \<open>Flows\<close>

context Preflow 
begin

text \<open>Only edges are labeled with non-zero flows\<close>
lemma zero_flow_simp[simp]:
  "(u,v)\<notin>E \<Longrightarrow> f(u,v) = 0"
  by (metis capacity_const eq_iff zero_cap_simp)

end -- \<open>Preflow\<close>   
    
context Flow
begin
text \<open>We provide a useful equivalent formulation of the 
  conservation constraint.\<close>
lemma conservation_const_pointwise: 
  assumes "u\<in>V - {s,t}"
  shows "(\<Sum>v\<in>E``{u}. f (u,v)) = (\<Sum>v\<in>E\<inverse>``{u}. f (v,u))"
  using conservation_const assms
  by (auto simp: sum_incoming_pointwise sum_outgoing_pointwise)

end -- \<open>Flow\<close>   

text \<open>Introduce a flow via the conservation constraint\<close>  
lemma (in Graph) intro_Flow:
  assumes cap: "\<forall>e. 0 \<le> f e \<and> f e \<le> c e"
  assumes cons: "\<forall>v \<in> V - {s, t}. 
    (\<Sum>e \<in> incoming v. f e) = (\<Sum>e \<in> outgoing v. f e)"
  shows "Flow c s t f"  
  using assms by unfold_locales auto  
  
context Finite_Preflow 
begin

text \<open>The summation of flows over incoming/outgoing edges can be 
  extended to a summation over all possible predecessor/successor nodes,
  as the additional flows are all zero.\<close>  
lemma sum_outgoing_alt_flow:
  fixes g :: "edge \<Rightarrow> 'capacity"
  assumes "u\<in>V"
  shows "(\<Sum>e\<in>outgoing u. f e) = (\<Sum>v\<in>V. f (u,v))"
  apply (subst sum_outgoing_alt)
  using assms capacity_const
  by auto
  
lemma sum_incoming_alt_flow:
  fixes g :: "edge \<Rightarrow> 'capacity"
  assumes "u\<in>V"
  shows "(\<Sum>e\<in>incoming u. f e) = (\<Sum>v\<in>V. f (v,u))"
  apply (subst sum_incoming_alt)
  using assms capacity_const
  by auto
end -- \<open>Finite Preflow\<close>   

subsubsection \<open>Networks\<close>  
context Network
begin
  
lemmas [simp] = no_incoming_s no_outgoing_t
  
lemma incoming_s_empty[simp]: "incoming s = {}"
  unfolding incoming_def using no_incoming_s by auto
  
lemma outgoing_t_empty[simp]: "outgoing t = {}"
  unfolding outgoing_def using no_outgoing_t by auto
  
text \<open>The network constraints implies that all nodes are 
  reachable from the source node\<close>  

lemma reachable_is_V[simp]: "reachableNodes s = V"
proof
  show "V \<subseteq> reachableNodes s"
  unfolding reachableNodes_def using s_node nodes_on_st_path
    by auto
qed (simp add: reachable_ss_V)

sublocale Finite_Graph 
  apply unfold_locales
  using reachable_is_V finite_reachable by auto
  
lemma cap_positive: "e \<in> E \<Longrightarrow> c e > 0"
  unfolding E_def using cap_non_negative le_neq_trans by fastforce 

lemma V_not_empty: "V\<noteq>{}" using s_node by auto
lemma E_not_empty: "E\<noteq>{}" using V_not_empty by (auto simp: V_def)
    
end -- \<open>Network\<close>

subsubsection \<open>Networks with Flow\<close>

context NPreflow 
begin

sublocale Finite_Preflow by unfold_locales

text \<open>As there are no edges entering the source/leaving the sink, 
  also the corresponding flow values are zero:\<close>
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

text \<open>For an edge, there is no reverse edge, and thus, no flow in the reverse direction:\<close>
lemma zero_rev_flow_simp[simp]: "(u,v)\<in>E \<Longrightarrow> f(v,u) = 0"
  using no_parallel_edge by auto

lemma excess_non_negative': "\<forall>v\<in>V-{s}. excess v \<ge> 0"
  unfolding excess_def using no_deficient_nodes 
  by (metis Diff_iff capacity_const insert_iff outgoing_t_empty sum.empty sum_nonneg zero_comp_diff_simps(1))  
    
    
end -- \<open>Network with preflow\<close>

context NFlow begin  
  sublocale Finite_Preflow by unfold_locales
  text \<open>There is no outflow from the sink in a network. 
    Thus, we can simplify the definition of the value:\<close>  
  corollary val_alt: "val = (\<Sum>e \<in> outgoing s. f e)"
    unfolding val_def by (auto simp: no_inflow_s)
      
end  
  
end -- \<open>Theory\<close>
