theory Augmenting_Ext
imports Augmenting
begin

  locale NFlowExt
  begin     
    definition "ntRepeating p \<equiv> distinct p \<and> (\<forall>(u, v) \<in> set p. (v, u) \<notin> set p)"  
      
    lemma ntRep_Cons: "ntRepeating (e # p) \<Longrightarrow> ntRepeating p"    
      unfolding ntRepeating_def by auto
      
    lemma isSPath_ntRep: "Graph.isSimplePath g u p v \<Longrightarrow> ntRepeating p"
      unfolding ntRepeating_def  
      using Graph.isSPath_nt_parallel Graph.isSPath_distinct by blast  
          
    definition augment :: "graph \<Rightarrow> capacity \<Rightarrow> path \<Rightarrow> graph" where
      "augment g cap p \<equiv> \<lambda>(u, v). 
        if (u, v) \<in> set p then
          g (u, v) - cap
        else if (v, u) \<in> set p then
          g (u, v) + cap
        else
          g (u, v)"
          
    definition augment_edge :: "capacity \<Rightarrow> edge \<Rightarrow> graph \<Rightarrow> graph" where
      "augment_edge cap e g \<equiv> \<lambda>(u, v).
        if e = (u, v) then
          g e - cap
        else if e = (v, u) then
          g (u, v) + cap
        else 
          g (u, v)"
    
    lemma augment_Nil[simp]: "augment g cap [] = g"  
      unfolding augment_def by auto      
          
    lemma augment_Cons: "ntRepeating (e # p) \<Longrightarrow>
      augment g cap (e # p) = augment (augment_edge cap e g) cap p"
      unfolding ntRepeating_def augment_def augment_edge_def 
      by fastforce
      
    lemma augment_fold: "ntRepeating p \<Longrightarrow> augment c cap p = fold (augment_edge cap) p c"  
        by (induction p arbitrary: c) (auto simp: augment_Cons dest!: ntRep_Cons)   
  end
  
  context NFlow
  begin
    definition "zeroFlow \<equiv> \<lambda>(u, v). 0"
    
    lemma zeroflow_resGraph: "f = zeroFlow \<Longrightarrow> cf = c"
      unfolding zeroFlow_def residualGraph_def E_def by auto  
  
    definition "augment' p \<equiv> NFlowExt.augment cf (bottleNeck p) p"
  
    lemma resAug_sim_netAug: "isAugmenting p \<Longrightarrow> f = augment (augmentingFlow p) \<Longrightarrow>
      cf = augment' p"
      oops
  end
  
end