section \<open>Augmenting Paths\<close>
theory Augmenting_Path
imports ResidualGraph
begin
text \<open>We define the concept of an augmenting path in the residual graph,
  and the residual flow induced by an augmenting path.\<close>

text \<open>We fix a network with a flow @{term f} on it.\<close>
context NFlow
begin

subsection \<open>Definitions\<close>

text \<open>An \emph{augmenting path} is a simple path from the source to the sink in the residual graph:\<close>
definition isAugmenting :: "path \<Rightarrow> bool" (* TODO: Rename to isAugmentingPath *)
where "isAugmenting p \<equiv> cf.isSimplePath s p t"

text \<open>The \emph{residual capacity} of an augmenting path is the smallest capacity 
  annotated to its edges:\<close>
definition bottleNeck :: "path \<Rightarrow> 'capacity"  (* TODO: Rename to residualCapacity*)
where "bottleNeck p \<equiv> Min {cf e | e. e \<in> set p}"

lemma bottleNeck_alt: "bottleNeck p = Min (cf`set p)"  
  -- \<open>Useful characterization for finiteness arguments\<close>
  unfolding bottleNeck_def apply (rule arg_cong[where f=Min]) by auto

text \<open>An augmenting path induces an \emph{augmenting flow}, which pushes as 
  much flow as possible along the path:\<close>
definition augmentingFlow :: "path \<Rightarrow> 'capacity flow"
where "augmentingFlow p \<equiv> \<lambda>(u, v).
  if (u, v) \<in> (set p) then
    bottleNeck p
  else
    0"

(*<*) (* Old syntax sugar, not used any more *)
end
  locale NFlow_Loc_Syntax = Graph_Loc_Syntax + NFlow begin
    notation isAugmenting ("\<langle>\<Rightarrow>\<^sup>A/ _\<rangle>" 1000)
    notation bottleNeck ("\<langle>\<nabla>/ _\<rangle>" 1000)
    notation augmentingFlow ("\<langle>\<F>\<^sub>\<p>/ _\<rangle>" 1000)
  end

  context Graph_Syntax begin  
    abbreviation NFlow_isAugmenting :: "_ graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> _ flow \<Rightarrow> path \<Rightarrow> bool"
      ("\<lbrace>_,/ _,/ _,/ _/ \<parallel>\<^sub>N\<^sub>F/ \<langle>\<Rightarrow>\<^sup>A/ _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c, s, t, f \<parallel>\<^sub>N\<^sub>F \<langle>\<Rightarrow>\<^sup>A p\<rangle>\<rbrace> \<equiv> NFlow.isAugmenting c s t f p"
    
    abbreviation NFlow_bottleNeck :: "_ graph \<Rightarrow> _ flow \<Rightarrow> path \<Rightarrow> _"
      ("\<lbrace>_,/ _/ \<parallel>\<^sub>N\<^sub>F/ \<langle>\<nabla>/ _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c, f \<parallel>\<^sub>N\<^sub>F \<langle>\<nabla> p\<rangle>\<rbrace> \<equiv> NFlow.bottleNeck c f p"
    
    abbreviation NFlow_augmentingFlow :: "_ graph \<Rightarrow> _ flow \<Rightarrow> path \<Rightarrow> _ flow"
      ("\<lbrace>_,/ _/ \<parallel>\<^sub>N\<^sub>F/ \<langle>\<F>\<^sub>\<p>/ _\<rangle>\<rbrace>" 1000)
    where "\<lbrace>c, f \<parallel>\<^sub>N\<^sub>F \<langle>\<F>\<^sub>\<p> p\<rangle>\<rbrace> \<equiv> NFlow.augmentingFlow c f p"
  end
context NFlow begin
(*>*)

subsection \<open>Augmenting Flow is Valid Flow\<close>
text \<open>In this section, we show that the augmenting flow induced by an 
  augmenting path is a valid flow in the residual graph.

  We start with some auxiliary lemmas.\<close>

text \<open>The residual capacity of an augmenting path is always positive.\<close>
lemma bottleNeck_gzero_aux: "cf.isPath s p t \<Longrightarrow> 0<bottleNeck p"
proof -
  assume PATH: "cf.isPath s p t"
  hence "set p\<noteq>{}" using s_not_t by (auto)
  moreover have "\<forall>e\<in>set p. cf e > 0"
    using cf.isPath_edgeset[OF PATH] resE_positive by (auto)
  ultimately show ?thesis unfolding bottleNeck_alt by (auto)
qed 

lemma bottleNeck_gzero: "isAugmenting p \<Longrightarrow> 0<bottleNeck p"
  using bottleNeck_gzero_aux[of p] by (auto simp: isAugmenting_def cf.isSimplePath_def)

text \<open>As all edges of the augmenting flow have the same value, we can factor 
  this out from a summation:\<close>
lemma setsum_augmenting_alt:
  assumes "finite A"          
  shows "(\<Sum>e \<in> A. (augmentingFlow p) e) = bottleNeck p * of_nat (card (A\<inter>set p))"
proof -
  have "(\<Sum>e \<in> A. (augmentingFlow p) e) = setsum (\<lambda>_. bottleNeck p) (A\<inter>set p)"
    apply (subst setsum.inter_restrict)
    apply (auto simp: augmentingFlow_def assms)
    done
  thus ?thesis by auto
qed  

lemma augFlow_resFlow: "isAugmenting p \<Longrightarrow> Flow cf s t (augmentingFlow p)"
proof (unfold_locales; intro allI ballI)
  assume AUG: "isAugmenting p"
  hence SPATH: "cf.isSimplePath s p t" by (simp add: isAugmenting_def)
  hence PATH: "cf.isPath s p t" by (simp add: cf.isSimplePath_def)

  { text \<open>We first show the capacity constraint\<close>
    fix e
    show "0 \<le> (augmentingFlow p) e \<and> (augmentingFlow p) e \<le> cf e"
    proof cases 
      assume "e \<in> set p"
      hence "bottleNeck p \<le> cf e" unfolding bottleNeck_alt by auto
      moreover  have "(augmentingFlow p) e = bottleNeck p" 
        unfolding augmentingFlow_def using \<open>e \<in> set p\<close> by auto
      moreover have "0 < bottleNeck p" using bottleNeck_gzero[OF AUG] by simp 
      ultimately show ?thesis by auto
    next
      assume "e \<notin> set p"
      hence "(augmentingFlow p) e = 0" unfolding augmentingFlow_def by auto
      thus ?thesis using resE_nonNegative by auto
    qed
  } 

  { text \<open>Next, we show the conservation constraint\<close>
    fix v
    assume asm_s: "v \<in> Graph.V cf - {s, t}"

    have "card (Graph.incoming cf v \<inter> set p) = card (Graph.outgoing cf v \<inter> set p)"
    proof (cases)  
      assume "v\<in>set (cf.pathVertices_fwd s p)"
      from cf.split_path_at_vertex[OF this PATH] obtain p1 p2 where
        P_FMT: "p=p1@p2" 
        and 1: "cf.isPath s p1 v"
        and 2: "cf.isPath v p2 t" 
        .
      from 1 obtain p1' u1 where [simp]: "p1=p1'@[(u1,v)]"    
        using asm_s by (cases p1 rule: rev_cases) (auto simp: split_path_simps)
      from 2 obtain p2' u2 where [simp]: "p2=(v,u2)#p2'"    
        using asm_s by (cases p2) (auto)
      from 
        cf.isSPath_sg_outgoing[OF SPATH, of v u2]  cf.isSPath_sg_incoming[OF SPATH, of u1 v]
        cf.isPath_edgeset[OF PATH] 
      have "cf.outgoing v \<inter> set p = {(v,u2)}" "cf.incoming v \<inter> set p = {(u1,v)}"
        by (fastforce simp: P_FMT cf.outgoing_def cf.incoming_def)+

      thus ?thesis by auto
    next
      assume "v\<notin>set (cf.pathVertices_fwd s p)"
      then have "\<forall>u. (u,v)\<notin>set p \<and> (v,u)\<notin>set p"
        by (auto dest: cf.pathVertices_edge[OF PATH])
      hence "cf.incoming v \<inter> set p = {}" "cf.outgoing v \<inter> set p = {}"
        by (auto simp: cf.incoming_def cf.outgoing_def)
      thus ?thesis by auto
    qed  
    thus "(\<Sum>e \<in> Graph.incoming cf v. (augmentingFlow p) e) =
      (\<Sum>e \<in> Graph.outgoing cf v. (augmentingFlow p) e)"
      by (auto simp: setsum_augmenting_alt)
  }
qed


subsection \<open>Value of Augmenting Flow is Residual Capacity\<close>
text \<open>Finally, we show that the value of the augmenting flow is the residual 
  capacity of the augmenting path\<close>

lemma augFlow_val: 
  "isAugmenting p \<Longrightarrow> Flow.val cf s (augmentingFlow p) = bottleNeck p"
proof -
  assume AUG: "isAugmenting p"
  with augFlow_resFlow interpret f!: Flow cf s t "augmentingFlow p" .

  note AUG 
  hence SPATH: "cf.isSimplePath s p t" by (simp add: isAugmenting_def)
  hence PATH: "cf.isPath s p t" by (simp add: cf.isSimplePath_def)
  then obtain v p' where "p=(s,v)#p'" "(s,v)\<in>cf.E" 
    using s_not_t by (cases p) auto
  hence "cf.outgoing s \<inter> set p = {(s,v)}"  
    using cf.isSPath_sg_outgoing[OF SPATH, of s v] cf.isPath_edgeset[OF PATH] 
    by (fastforce simp: cf.outgoing_def)
  moreover have "cf.incoming s \<inter> set p = {}" using SPATH no_incoming_s
    by (auto 
      simp: cf.incoming_def \<open>p=(s,v)#p'\<close> in_set_conv_decomp[where xs=p']
      simp: cf.isSimplePath_append cf.isSimplePath_cons)  
  ultimately show ?thesis
    unfolding f.val_def
    by (auto simp: setsum_augmenting_alt)
qed    

end -- \<open>Network with flow\<close>
end -- \<open>Theory\<close>
