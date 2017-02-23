theory Preflow_Complexity_Test
imports Preflow
begin
  
context Height_Bounded_Labeling begin 
(***********************
************************
**TODO: Clean up *******
************************
************************)  
(* TODO: Used in the following lemmas which both look to be redundant *)
lemma sum_arb:
  assumes A_fin: "finite A"
      and x_mem: "x \<in> A" 
      and x_dif: "\<forall>y\<in>A. y \<noteq> x \<longrightarrow> g y = h y"
    shows "(\<Sum>a\<in>A. g a) = (\<Sum>a\<in>A - {x}. h a) + g x"
proof -
  have "A = (A - {x}) \<union> {x}" using x_mem by auto
  moreover note sum.union_disjoint[of "A - {x}" "{x}" g]
  moreover note sum.cong[of "A - {x}" "A - {x}" g h]
  ultimately show ?thesis using A_fin x_dif by auto
qed

(* TODO: I think there was already a similar lemma, adapt 26.23 part I and II to that lemma *)
lemma push_excess_out:
  assumes "(u, v) \<in> cf.E"
  defines X_def:"X \<equiv> min (excess f u) (cf (u,v))"  
    shows "excess (push_effect f (u, v)) u = excess f u - X"
proof -
  have "(u, v)\<in>E \<or> (v, u)\<in>E" using assms cfE_ss_invE by fastforce
  thus ?thesis 
  proof 
    assume "(u, v) \<in> E"
    then have "(v, u) \<notin> E" using no_parallel_edge by blast
        
    define f' where "f' \<equiv> push_effect f (u, v)"
    then have[simp]: "f' = f( (u,v) := f (u,v) + X )" 
      unfolding f'_def push_effect_def augment_edge_def X_def using `(u, v) \<in> E` by simp  
        
    { 
      have f1:"(u, v) \<in> outgoing u" unfolding outgoing_def using `(u, v) \<in> E` by simp
      have f2: "\<forall>e \<in> (outgoing u). e \<noteq> (u, v) \<longrightarrow> f' e = f e" by simp
      have f3: "\<forall>e \<in> (outgoing u). e \<noteq> (u, v) \<longrightarrow> f e = f e"  by blast
      
      note sum_arb[OF finite_outgoing[OF finite_V] f1 f2]
      moreover note sum_arb[OF finite_outgoing[OF finite_V] f1 f3, symmetric]
      ultimately have "(\<Sum>e\<in>outgoing u. f' e) = (\<Sum>e\<in>outgoing u. f e) + X" by auto
    }
    moreover {    
      have "\<forall>e \<in> (incoming u). e \<noteq> (u, v) \<longrightarrow> f' e = f e" by simp
      moreover have "(u, v) \<notin> (incoming u)" unfolding incoming_def using `(v, u) \<notin> E` by auto
      ultimately have "\<forall>e \<in> (incoming u). f' e = f e" by auto
      then have "(\<Sum>e\<in>incoming u. f' e) = (\<Sum>e\<in>incoming u. f e)" by auto 
    }
    ultimately have "excess f' u = excess f u - X" unfolding excess_def by auto        
    thus ?thesis unfolding f'_def by simp
  next
    assume "(v, u) \<in> E"
    then have "(u, v) \<notin> E" using no_parallel_edge by blast
        
    define f' where "f' \<equiv> push_effect f (u, v)"
    then have[simp]: "f' = f( (v,u) := f (v,u) - X )" 
      unfolding f'_def push_effect_def augment_edge_def X_def using `(v, u) \<in> E` `(u, v) \<notin> E` by simp
        
    { 
      have f1:"(v, u) \<in> incoming u" unfolding incoming_def using `(v, u) \<in> E` by simp
      have f2: "\<forall>e \<in> (incoming u). e \<noteq> (v, u) \<longrightarrow> f' e = f e" by simp
      have f3: "\<forall>e \<in> (incoming u). e \<noteq> (v, u) \<longrightarrow> f e = f e"  by blast
      
      note sum_arb[OF finite_incoming[OF finite_V] f1 f2]
      moreover note sum_arb[OF finite_incoming[OF finite_V] f1 f3, symmetric]
      ultimately have "(\<Sum>e\<in>incoming u. f' e) = (\<Sum>e\<in>incoming u. f e) - X" by auto
    }
    moreover {    
      have "\<forall>e \<in> (outgoing u). e \<noteq> (v, u) \<longrightarrow> f' e = f e" by simp
      moreover have "(v, u) \<notin> (outgoing u)" unfolding outgoing_def using `(u, v) \<notin> E` by auto
      ultimately have "\<forall>e \<in> (outgoing u). f' e = f e" by auto
      then have "(\<Sum>e\<in>outgoing u. f' e) = (\<Sum>e\<in>outgoing u. f e)" by auto 
    }
    ultimately have "excess f' u = excess f u - X" unfolding excess_def by auto        
    thus ?thesis unfolding f'_def by simp
  qed
qed
  
(* TODO: I think there was already a similar lemma, adapt 26.23 part I and II to that lemma *)
lemma push_excess_in:
  assumes "(u, v) \<in> cf.E"
  defines X_def:"X \<equiv> min (excess f u) (cf (u,v))"  
    shows "excess (push_effect f (u, v)) v = excess f v + X"
proof -
  have "(u, v)\<in>E \<or> (v, u)\<in>E" using assms cfE_ss_invE by fastforce
  thus ?thesis 
  proof 
    assume "(u, v) \<in> E"
    then have "(v, u) \<notin> E" using no_parallel_edge by blast
        
    define f' where "f' \<equiv> push_effect f (u, v)"
    then have[simp]: "f' = f( (u,v) := f (u,v) + X )" 
      unfolding f'_def push_effect_def augment_edge_def X_def using `(u, v) \<in> E` by simp  
        
    { 
      have f1:"(u, v) \<in> incoming v" unfolding incoming_def using `(u, v) \<in> E` by simp
      have f2: "\<forall>e \<in> (incoming v). e \<noteq> (u, v) \<longrightarrow> f' e = f e" by simp
      have f3: "\<forall>e \<in> (incoming v). e \<noteq> (u, v) \<longrightarrow> f e = f e"  by blast
      
      note sum_arb[OF finite_incoming[OF finite_V] f1 f2]
      moreover note sum_arb[OF finite_incoming[OF finite_V] f1 f3, symmetric]
      ultimately have "(\<Sum>e\<in>incoming v. f' e) = (\<Sum>e\<in>incoming v. f e) + X" by auto
    }
    moreover {    
      have "\<forall>e \<in> (outgoing v). e \<noteq> (u, v) \<longrightarrow> f' e = f e" by simp
      moreover have "(u, v) \<notin> (outgoing v)" unfolding outgoing_def using `(v, u) \<notin> E` by auto
      ultimately have "\<forall>e \<in> (outgoing v). f' e = f e" by auto
      then have "(\<Sum>e\<in>outgoing v. f' e) = (\<Sum>e\<in>outgoing v. f e)" by auto 
    }
    ultimately have "excess f' v = excess f v + X" unfolding excess_def by auto        
    thus ?thesis unfolding f'_def by simp
  next
    assume "(v, u) \<in> E"
    then have "(u, v) \<notin> E" using no_parallel_edge by blast
        
    define f' where "f' \<equiv> push_effect f (u, v)"
    then have[simp]: "f' = f( (v,u) := f (v,u) - X )" 
      unfolding f'_def push_effect_def augment_edge_def X_def using `(v, u) \<in> E` `(u, v) \<notin> E` by simp
        
    { 
      have f1:"(v, u) \<in> outgoing v" unfolding outgoing_def using `(v, u) \<in> E` by simp
      have f2: "\<forall>e \<in> (outgoing v). e \<noteq> (v, u) \<longrightarrow> f' e = f e" by simp
      have f3: "\<forall>e \<in> (outgoing v). e \<noteq> (v, u) \<longrightarrow> f e = f e"  by blast
      
      note sum_arb[OF finite_outgoing[OF finite_V] f1 f2]
      moreover note sum_arb[OF finite_outgoing[OF finite_V] f1 f3, symmetric]
      ultimately have "(\<Sum>e\<in>outgoing v. f' e) = (\<Sum>e\<in>outgoing v. f e) - X" by auto
    }
    moreover {    
      have "\<forall>e \<in> (incoming v). e \<noteq> (v, u) \<longrightarrow> f' e = f e" by simp
      moreover have "(v, u) \<notin> (incoming v)" unfolding incoming_def using `(u, v) \<notin> E` by auto
      ultimately have "\<forall>e \<in> (incoming v). f' e = f e" by auto
      then have "(\<Sum>e\<in>incoming v. f' e) = (\<Sum>e\<in>incoming v. f e)" by auto 
    }
    ultimately have "excess f' v = excess f v + X" unfolding excess_def by auto        
    thus ?thesis unfolding f'_def by simp
  qed
qed
  
(*TODO: used in lemma before which is not required any more. *)  
lemma relabel_adm_measure:
  assumes "relabel_precond f l u"
  shows "card_adm_measure f (relabel_effect f l u) \<le> card V + card_adm_measure f l"
proof -
  let ?l' = "relabel_effect f l u"
  {
    have "adm_edges f l \<inter> cf.outgoing u = {}" using assms 
      unfolding relabel_precond_def adm_edges_def cf.E_def cf.outgoing_def by auto
    moreover note edge_changes = relabel_adm_edges[OF assms]
    ultimately have "adm_edges f ?l' - cf.outgoing u = adm_edges f l - cf.incoming u" 
      unfolding cf.adjacent_def by auto
  } note fct = this

  have "card_adm_measure f ?l' - card (cf.outgoing u) \<le> card (adm_edges f ?l' - cf.outgoing u)"
    by (simp add: card_adm_measure_def diff_card_le_card_Diff)
  then have "card_adm_measure f ?l' - card (cf.outgoing u) \<le> card (adm_edges f l - cf.incoming u)"
    using fct by auto
  moreover have "\<dots> \<le> card (adm_edges f l)"
    by (simp add: Diff_subset card_mono)
  moreover have "card (cf.outgoing u) \<le> card cf.V" using cf.outgoing_alt
    by (metis (mono_tags) card_image_le card_mono cf.succ_ss_V finite_V finite_subset le_trans resV_netV)
  ultimately have "card_adm_measure f ?l' - card cf.V \<le> card (adm_edges f l)"
    by auto
  thus ?thesis using card_adm_measure_def by auto
qed
  
(*TODO: used for old measure on saturating push giving V^3 complexity, not required any more. *)  
lemma relabel_sum_height_card_adm_measure:
  assumes "relabel_precond f l u"
  shows "card V * sum_heights_measure (relabel_effect f l u) + card_adm_measure f (relabel_effect f l u)
   \<le> card V * sum_heights_measure l + card_adm_measure f l" (is "?L1 + ?L2 \<le> _")
proof -
  have "?L1 + ?L2 \<le> ?L1 + card V + card_adm_measure f l"
    using relabel_adm_measure[OF assms] by auto
  also have "card V * sum_heights_measure (relabel_effect f l u) + card V = 
    card V * (sum_heights_measure (relabel_effect f l u) + 1)" by auto
  also have "sum_heights_measure (relabel_effect f l u) + 1 \<le> sum_heights_measure l"
    using relabel_measure[OF assms] by auto
  finally show ?thesis by auto
qed
(***********************
************************
******* END TODO *******
************************
************************)  
  
  
(* Cormen 26.23 part I *)
lemma sat_push_unsat_potential:
  assumes "sat_push_precond f l e"
  shows "unsat_potential (push_effect f e) l \<le> 2 * card V + unsat_potential f l"
proof - 
  obtain u v where obt:"e = (u, v)" by (cases e) auto   
  
  have u_inV: "u \<in> V" using assms obt excess_nodes_only unfolding sat_push_precond_def by blast
  have v_inV: "v \<in> V" using assms obt unfolding sat_push_precond_def using  cf.V_def by auto
  have u_not_v: "u \<noteq> v" using assms obt unfolding sat_push_precond_def by auto
  have unsat_pot_decomp: "{x\<in>V. P x} = ({x\<in>V - {u, v}. P x}) \<union> {x\<in>{u,v}. P x}" for P
    using u_inV v_inV by auto
  
  note unsat_pot_decomp[of "\<lambda>x. excess (push_effect f e) x > 0"] 
  then have 
    "unsat_potential (push_effect f e) l =  sum l {x \<in> V-{u,v}. 0 < excess (push_effect f e) x} +
    sum l {x\<in>{u,v}. 0 < excess (push_effect f e) x}" (is "_ = ?R1 + ?R2")unfolding unsat_potential_def
    using sum.union_disjoint[of "{x \<in> V-{u,v}. 0 < excess (push_effect f e) x}"
      "{x \<in> {u,v}. 0 < excess (push_effect f e) x}" l] by auto
  also have "?R1 = sum l {x \<in> V - {u, v}. 0 < excess f x}" (is "_ = ?R1'")
  proof -
    {
      fix w e'
      assume "w \<noteq> u"
      assume "w \<noteq> v"
      have "\<lbrakk>e1 \<noteq> (u, v); e1\<noteq> (v, u)\<rbrakk> \<Longrightarrow> (push_effect f e) e1 = f e1" for e1
        unfolding push_effect_def augment_edge_def using obt by (auto split:if_split)
      then have "e1 \<in> incoming w \<Longrightarrow> (push_effect f (u, v)) e1 = f e1"
        and "e1 \<in> outgoing w \<Longrightarrow> (push_effect f (u, v)) e1 = f e1" for e1
        unfolding incoming_def outgoing_def using obt `w \<noteq> u` `w \<noteq> v` by auto
      then have "(\<Sum>e\<in>incoming w. (push_effect f (u, v)) e) = (\<Sum>e\<in>incoming w. f e)"
        and "(\<Sum>e\<in>outgoing w. (push_effect f (u, v)) e) = (\<Sum>e\<in>outgoing w. f e)" by auto   
      then have "excess (push_effect f e) w = excess f w" unfolding excess_def using obt by simp
    }
    thus ?thesis by (metis Diff_iff Un_commute insertI1 insert_is_Un)
  qed
  also have "?R2 \<le>  sum l {x \<in> {u, v}. 0 < excess f x} + 2 * card V " (is "_ \<le> ?R2'")
  proof -
    have f1: "excess f u > 0" using assms obt unfolding sat_push_precond_def by blast
    have f2: "excess (push_effect f e) u \<ge> 0" using assms obt push_excess_out 
      unfolding sat_push_precond_def by auto
    have f3: "excess (push_effect f e) v > excess f v" 
    proof -
      have "excess (push_effect f e) v = excess f v + cf (u, v)"
        using assms obt push_excess_in unfolding sat_push_precond_def resE_positive by auto
      moreover have "cf (u, v) > 0" using assms unfolding sat_push_precond_def
        by (simp add: obt resE_positive)
      ultimately show ?thesis by simp
    qed
    
    let ?set_be = "{x \<in> {u, v}. 0 < excess f x}"  
    let ?set_af = "{x \<in> {u, v}. 0 < excess (push_effect f e) x}"
      
    show ?thesis
    proof (cases "excess f v > 0"; cases "excess (push_effect f e) u \<noteq> 0")
      assume "0 < excess f v" and "excess (push_effect f e) u \<noteq> 0"
      then have "?set_af = {u, v}"
        and "?set_be = {u, v}" using f1 f2 f3 by auto
      then have "sum l ?set_af = sum l ?set_be" by auto
      thus ?thesis by simp
    next
      assume "0 < excess f v" and "\<not> excess (push_effect f e) u \<noteq> 0"
      then have "?set_af = {v}" and "?set_be = {u, v}" using f1 f2 f3 by auto
      then have " sum l ?set_af = sum l ?set_be - l u " using u_not_v by auto
      thus ?thesis by simp
    next
      assume "\<not> 0 < excess f v" and "excess (push_effect f e) u \<noteq> 0"
      then have "?set_af \<subseteq> {u, v}" and "{u} \<subseteq> ?set_af" and "?set_be = {u}" using f1 f2 by auto
      then have "sum l ?set_af \<le> l u + l v" and "sum l ?set_af \<ge> l u"  and "sum l ?set_be = l u"
        using sum_mono2[of ?set_af "{u}" l]  sum_mono2[of "{u, v}" ?set_af l] u_not_v by auto
      then have "sum l ?set_af \<ge> sum l ?set_be" and "sum l ?set_af \<le> sum l ?set_be + l v" by auto
      thus ?thesis using height_bound v_inV by auto
    next
      assume "\<not> 0 < excess f v" and "\<not> excess (push_effect f e) u \<noteq> 0"
      then have "?set_af \<subseteq> {v}" and "?set_be = {u}" using f1 by auto
      then have "sum l ?set_af \<le> l v" and "sum l ?set_be = l u" 
        using sum_mono2[of "{v}" ?set_af l] by auto
      then have "sum l ?set_af \<le> sum l ?set_be - 1"
        using assms obt unfolding sat_push_precond_def by auto
      thus ?thesis by simp
    qed
  qed   
  also have "?R1' + ?R2' = unsat_potential f l + 2 * card V"
    unfolding unsat_potential_def using unsat_pot_decomp[of "\<lambda>x. excess f x > 0"]
      sum.union_disjoint[symmetric, of "{x \<in> V-{u,v}. 0 < excess f x}""{x \<in> {u,v}. 0 < excess f x}" l]
    by auto
  finally show ?thesis by auto
qed
  
(* Cormen 26.23 part II *)
lemma relabel_unsat_potential:
  assumes "relabel_precond f l u"
  shows "unsat_potential f (relabel_effect f l u) \<le> 2 * card V + unsat_potential f l"
proof -  
  interpret l': Height_Bounded_Labeling c s t f "(relabel_effect f l u)"
    using relabel_pres_height_bound[OF assms] .
      
  have f0: "u \<in> V" using assms excess_nodes_only relabel_precond_def by auto
  have f1: "finite {v \<in> V. 0 < excess f v}" using finite_V by auto
  have f2: "u \<in> {v \<in> V. 0 < excess f v}" using assms excess_nodes_only relabel_precond_def by auto
  have f3: "\<forall>y\<in>{v \<in> V. 0 < excess f v}. y \<noteq> u \<longrightarrow> l y = l y" by auto
  have f4: "\<forall>y\<in>{v \<in> V. 0 < excess f v}. y \<noteq> u \<longrightarrow> 
    (relabel_effect f l u) y = (relabel_effect f l u) y" by auto
  
  note sum_arb[OF f1 f2 f4]
  moreover have "sum (relabel_effect f l u) ({v \<in> V. 0 < excess f v} - {u}) =
     sum l ({v \<in> V. 0 < excess f v} - {u})" using relabel_preserve_other by auto
  moreover note sum_arb[OF f1 f2 f3, symmetric]
  ultimately have fct: "unsat_potential f (relabel_effect f l u) = 
    unsat_potential f l + relabel_effect f l u u - l u" unfolding unsat_potential_def by auto  
  
  have "l u \<le> 2 * card V - 1" using f0 height_bound by auto
  moreover have "relabel_effect f l u u \<le> 2 * card V - 1" using  f0 l'.height_bound by auto
  ultimately show ?thesis using fct by auto
qed  
  
  
end  
  
context Labeling begin  
  
  lemma relabel_mono: "relabel_precond f l u \<Longrightarrow> l u' \<le> relabel_effect f l u u'"  
    apply (cases "u=u'")
    using relabel_preserve_other relabel_increase_u  
    apply force+
    done 
  
end


lemma card_Union_Sum_le:
  assumes "finite A"
    shows "card (\<Union>x\<in>A. S x) \<le> (\<Sum>x\<in>A. card (S x))"
  using assms 
proof (induction "card A" arbitrary: A)
  case 0
  then show ?case by auto
next
  case (Suc x)
  obtain a A' where obt1:"card A' = x" and obt2:"A = insert a A'" 
    using Suc.prems Suc.hyps(2) by (metis card_Suc_eq)

  have "(\<Union>x\<in>A. S x) = S a \<union> (\<Union>x\<in>A'. S x)" using obt2 by auto
  then have "card (\<Union>x\<in>A. S x) \<le> card (S a) + card (\<Union>x\<in>A'. S x)" using card_Un_le by auto
  also have "card (\<Union>x\<in>A'. S x) \<le> (\<Sum>x\<in>A'. card (S x))" 
    using Suc.prems obt1[symmetric] obt2 Suc.hyps(1) by auto
  also have "card (S a) + (\<Sum>x\<in>A'. card (S x)) = (\<Sum>x\<in>A. card (S x))"
    by (metis Suc.hyps(2) Suc.prems card_insert_if finite_insert n_not_Suc_n obt1 obt2 sum.insert)
  finally show ?case by auto
qed

  
  
context Network begin    
    
datatype op_type = is_RELABEL: RELABEL | is_UNSAT_PUSH: UNSAT_PUSH | is_SAT_PUSH: SAT_PUSH edge   
inductive_set algo_rel' where
  unsat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; unsat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),UNSAT_PUSH,(push_effect f e,l))\<in>algo_rel'"
| sat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; sat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),SAT_PUSH e,(push_effect f e,l))\<in>algo_rel'"
| relabel': "\<lbrakk>Height_Bounded_Labeling c s t f l; relabel_precond f l u \<rbrakk>
    \<Longrightarrow> ((f,l),RELABEL,(f,relabel_effect f l u))\<in>algo_rel'"
  
(*************************************************************************************************
  TODO: Remove! old bound
  Cormen bounds this by |V||E| instead of |V|\<^sup>3, so later he can use it to build the measure for
  un-saturating pushes (a |V| multiplier is added). We have to make this smaller, or come up with
  a new measure for un-sturated pushes.
*************************************************************************************************)
lemma
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter is_SAT_PUSH p) < card V * sum_heights_measure (snd fxl) + card_adm_measure (fst fxl) (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
  apply (auto elim!: algo_rel'.cases)  
  apply (drule (1) Height_Bounded_Labeling.sat_push_measure; auto)
  apply (drule (1) Height_Bounded_Labeling.unsat_push_measure(1); auto)
  apply (drule (1) Height_Bounded_Labeling.relabel_sum_height_card_adm_measure; auto)
  done  
(*************************************************************************************************
*************************************************************************************************)  
  
  
  
 
lemma algo_rel'_Height_Bounded_Labeling_fst:
  assumes "((f, l), a, (f', l')) \<in> algo_rel'"
  shows "Height_Bounded_Labeling c s t f l"
  using assms by (auto elim!:algo_rel'.cases)

lemma algo_rel'_Height_Bounded_Labeling_snd:
  assumes "((f, l), a, (f', l')) \<in> algo_rel'"
  shows "Height_Bounded_Labeling c s t f' l'"
  using assms 
  by (auto elim!:algo_rel'.cases simp add: push_precond_def sat_push_precond_def unsat_push_precond_def
    Height_Bounded_Labeling.push_pres_height_bound Height_Bounded_Labeling.relabel_pres_height_bound)    
    
lemma relabel_path_mono:
  assumes "((f,l),p,(f',l')) \<in> trcl algo_rel'"
  shows "l u \<le> l' u"
  using assms 
proof (induction p arbitrary: f l)  
  case Nil thus ?case by (auto elim!: algo_rel'.cases)
next
  case (Cons a as) 
  
  from Cons.prems Cons.IH show ?case
    apply (auto dest!: trcl_uncons elim!: algo_rel'.cases)
  proof -
    assume "Height_Bounded_Labeling c s t f l"
    then interpret Height_Bounded_Labeling c s t f l .  
    fix u'
    assume PRE: "relabel_precond f l u'"
    let ?l' = "relabel_effect f l u'"
      
    have "l u \<le> ?l' u" using relabel_mono[OF PRE] .
    also 
    assume "((f, ?l'), as, f', l') \<in> trcl algo_rel'"
    note Cons.IH[OF this]
    finally show ?case .
  qed        
qed    
    
  
(* When proving sat_push_no_vertex_chain_length lemma,
   I thought maybe it is possible to prove it without
   this lemma, however, I did not look into it. TODO *)  
lemma next_sat_push_at_increased_labeling:
  assumes "l u = l v + 1"
  assumes "cf_of f (u,v) = 0"  
  assumes "( (f,l), p@[SAT_PUSH (u,v)], (fE,lE) ) \<in> trcl algo_rel'"  
  shows "l u + l v < lE u + lE v" 
  using assms(3,1-2)    
proof (induction p arbitrary: f l)  
  case Nil thus ?case by (auto elim!: algo_rel'.cases simp: sat_push_precond_def Graph.E_def)
next
  case (Cons a as) 
  
  from Cons.prems(1) show ?case
    apply (auto dest!: trcl_uncons elim!: algo_rel'.cases)
  proof -
    assume "Height_Bounded_Labeling c s t f l"
    then interpret Height_Bounded_Labeling c s t f l .  
    
    {
      fix u' v'
      assume A: "unsat_push_precond f l (u', v')"  

      from A have NEQ: "(u',v')\<noteq>(u,v) \<and> (u',v')\<noteq>(v,u)"  
        using Cons.prems(2,3) unfolding unsat_push_precond_def
        using cfE_ss_invE unfolding Graph.E_def
        by auto
        
      from A interpret push_effect_locale c s t f l u' v'  
        apply unfold_locales using push_precond_eq_sat_or_unsat by auto
        
      have 1: "cf_of f' (u,v) = 0" using NEQ
        by (auto simp: unsat_push_alt[OF A] Cons.prems(3))

      assume 2: "((f', l), as @ [SAT_PUSH (u, v)], fE, lE) \<in> trcl algo_rel'"    
          
      from Cons.IH[OF 2 \<open>l u = l v + 1\<close> 1] show ?case .
    }    
      
    {
      fix u' v'
      assume A: "sat_push_precond f l (u', v')"  

      from A have NEQ: "(u',v')\<noteq>(u,v) \<and> (u',v')\<noteq>(v,u)"  
        using Cons.prems(2,3) unfolding sat_push_precond_def
        using cfE_ss_invE unfolding Graph.E_def
        by auto
        
      from A interpret push_effect_locale c s t f l u' v'  
        apply unfold_locales using push_precond_eq_sat_or_unsat by auto
        
      have 1: "cf_of f' (u,v) = 0" using NEQ
        by (auto simp: sat_push_alt[OF A] Cons.prems(3))

      assume 2: "((f', l), as @ [SAT_PUSH (u, v)], fE, lE) \<in> trcl algo_rel'"    
          
      from Cons.IH[OF 2 \<open>l u = l v + 1\<close> 1] show ?case .
    }    
      
    {
      fix u'
      let ?l' = "relabel_effect f l u'"
        
      assume PRE: "relabel_precond f l u'"  
        
      assume PATH: "((f, ?l'), as @ [SAT_PUSH (u, v)], fE, lE) \<in> trcl algo_rel'"  
        
      have U'_HEIGHT_INCR: "?l' u' > l u'" using relabel_increase_u[OF PRE] .
        
      {
        assume "u'\<in>{u,v}"
        with U'_HEIGHT_INCR have ?case 
          using relabel_path_mono[OF PATH, of u] relabel_path_mono[OF PATH, of v] 
          using relabel_mono[OF PRE]  
          apply auto
          apply (metis add_increasing2 add_less_le_mono le0 le_Suc_ex less_le_trans)
          by (metis add_le_less_mono le_Suc_ex less_le_trans trans_le_add1)
      } moreover {
        assume "u'\<notin>{u,v}"
        with relabel_preserve_other have L'EQ: "?l' u = l u" "?l' v = l v"
          by auto
        with Cons.prems(2) have "?l' u = ?l' v + 1" by simp  
        from Cons.IH[OF PATH this \<open>cf (u, v) = 0\<close>] have ?case by (simp add:  L'EQ)
      } ultimately show ?case by blast
    }  
  qed
qed
  
lemma arb_list_obtain:
  assumes "length LST \<ge> 2"
  obtains X' x1 x2 where "LST = X' @ [x1, x2]"
proof -
  have "\<exists> X' x1 x2. LST = X' @ [x1, x2]"
  using assms proof (induction LST)
    case Nil
    then show ?case by auto
  next
    case (Cons a X)
    show ?case
    proof (cases "length X \<ge> 2")
      case True
      then show ?thesis using Cons.IH by auto
    next
      case False  
      have "length X \<ge> 1" using Cons.prems by auto
      then have "length X = 1" using False by linarith
      then obtain b where "X = [b]" by (cases X) auto
      thus ?thesis by auto
    qed
  qed
  then obtain X' x1 x2 where "LST = X' @ [x1, x2]" by blast
  thus ?thesis ..
qed
  
lemma arb_filter_append:
  assumes "filter P C = A @ B"
  obtains C1 C2 where "C = C1 @ C2 \<and> filter P C1 = A \<and> filter P C2 = B"
proof -
  have "\<exists>C1 C2. C = C1 @ C2 \<and> filter P C1 = A \<and> filter P C2 = B"
  using assms proof (induction C arbitrary: A B)
    case Nil
    then show ?case by auto
  next
    case (Cons a C)  
    show ?case
    proof (cases "P a")
      case True                
      {
        assume "A = []"
        then have "a # C = [] @ (a # C) \<and> filter P [] = A \<and> filter P (a # C) = B"
          using Cons.prems True by auto
        then have ?thesis by blast
      }
      moreover {
        assume "A \<noteq> []"
        then obtain A' where "filter P (a # C) = a # A' @ B" and "a # A' = A"
          and "filter P C = A' @ B" using Cons.prems True
          by (metis filter.simps(2) list_Cons_eq_append_cases)
        then obtain C1 C2 where "C = C1 @ C2" and "filter P C1 = A'" and "filter P C2 = B" 
          using Cons.IH[of A' B] by auto
            
        have "a # C = (a # C1) @ C2 \<and> filter P (a # C1) = A \<and> filter P C2 = B"
          using `C = C1 @ C2` `filter P C1 = A'` `a # A' = A` `filter P C2 = B` True by auto
        then have ?thesis by blast
      } 
      ultimately show ?thesis by blast
    next
      case False
      then have "filter P C = A @ B" using Cons.prems by simp
      then obtain C1 C2 where "C = C1 @ C2" and "filter P C1 = A" and "filter P C2 = B" 
        using Cons.IH[of A B] by auto
      
      have "filter P (a # C1) = A" using False `filter P C1 = A` by simp
      moreover have "(a # C) = (a # C1) @ C2" using `C = C1 @ C2` by simp
      ultimately show ?thesis using `filter P C2 = B` `filter P C1 = A` `C = C1 @ C2` by metis
    qed
  qed
  then obtain C1 C2 where "C = C1 @ C2 \<and> filter P C1 = A \<and> filter P C2 = B" by blast
  thus ?thesis ..
qed   
      
lemma sat_push_no_vertex_chain_length:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  assumes "u \<notin> V \<or> v \<notin> V"
  shows "length (filter (op= (SAT_PUSH (u,v))) p) = 0"  
  using assms proof (induction rule: trcl.induct)
  case (empty c)
  then show ?case by auto
next
  case (cons c a c' w c'')
  show ?case
  proof (cases "a=SAT_PUSH (u, v)")
    case True
    obtain e where "e = (u, v)" by auto
    then have "(c, SAT_PUSH e, c') \<in> algo_rel'" using cons.hyps(1) True by simp
    then have "sat_push_precond (fst c) (snd c) e"  
      using Network.algo_rel'p.simps Network_axioms algo_rel'_def by fastforce
    then have "(u, v) \<in> cfE_of (fst c)" unfolding sat_push_precond_def `e = (u, v)` by auto
    then have "u \<in> V \<and> v \<in> V"  using cfE_of_ss_VxV by blast
    then show ?thesis using cons.prems by auto
  next
    case False
    then show ?thesis using cons.IH[OF cons.prems] by auto
  qed
qed  
  
lemma sat_push_edge_chain_height_sum:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (op= (SAT_PUSH (u,v))) p) \<le> (snd fxl') u + (snd fxl') v + 2"
  using assms
proof (induction "length (filter (op= (SAT_PUSH (u,v))) p)" arbitrary: p fxl fxl')
  case 0
  then show ?case by auto
next
  case (Suc x)
  show ?case
  proof (cases "length (filter (op= (SAT_PUSH (u,v))) p) < 2")
    case True
    then show ?thesis by simp
  next
    case False
    let ?L = "filter (op= (SAT_PUSH (u,v))) p"
      
    note arb_list_obtain [of ?L]
    moreover have "2 \<le> length ?L" using False by simp
    moreover have "\<forall>a\<in>set ?L. a= SAT_PUSH (u,v)" by auto
    moreover have "A = A' @ [a, b] \<Longrightarrow> (a \<in> set A \<and> b \<in> set A)" for A A' a b by auto
    ultimately obtain L' where L_split: "?L = L' @ [SAT_PUSH (u,v), SAT_PUSH (u,v)]" by metis
    
    obtain P1 P2 where p_spl1:"p = P1 @ P2" and p_spl2: "filter (op = (SAT_PUSH (u, v))) P1 = L'" 
      and p_spl3: "filter (op = (SAT_PUSH (u, v))) P2 = [SAT_PUSH (u, v), SAT_PUSH (u, v)]"
      using arb_filter_append[OF L_split] by metis
    then obtain P21 P22 where p_spl4: "P2 = P21 @ SAT_PUSH (u, v) # P22" and
      p_spl5: "(\<forall>ua\<in>set P21. SAT_PUSH (u, v) \<noteq> ua)" and
      "filter (op = (SAT_PUSH (u, v))) P22 = [SAT_PUSH (u, v)]" 
      using filter_eq_Cons_iff[of "op = (SAT_PUSH (u, v))" P2 "SAT_PUSH (u, v)"] by auto
    then obtain P22_1 P22_2 where p_spl6: "P22 = P22_1 @ SAT_PUSH (u, v) # P22_2" and 
      "(\<forall>ua\<in>set P22_1. SAT_PUSH (u, v) \<noteq> ua)" and
      p_spl8: "filter (op = (SAT_PUSH (u, v))) P22_2 = []"
      using filter_eq_Cons_iff[of "op = (SAT_PUSH (u, v))"] by auto
        
    obtain p1 p2 p3 where "p = (p1 @ [SAT_PUSH (u, v)]) @ (p2 @ (SAT_PUSH (u, v) # p3))"
      and "p1 = P1 @ P21" and "p2 = P22_1" and "p3=P22_2"
      and "filter (op = (SAT_PUSH (u, v))) p1 = L'"
      and "filter (op = (SAT_PUSH (u, v))) p2 = []"
      and "filter (op = (SAT_PUSH (u, v))) p3 = []"
      using p_spl1 p_spl2 p_spl3 p_spl4 p_spl5 p_spl6 p_spl8 by auto
    note p_split= this(1, 5-7)
            
    let ?p_app1 = "p1 @ [SAT_PUSH (u, v)]"
    let ?p_app2 = "(p2 @ (SAT_PUSH (u, v) # p3))"
    let ?L_app = "filter (op = (SAT_PUSH (u, v))) ?p_app1"    
      
    obtain fli where 
      trcl1: "(fxl,?p_app1,fli)\<in>trcl algo_rel'" and trcl1':"(fli,?p_app2,fxl')\<in>trcl algo_rel'"
      using trcl_unconcat[of fxl ?p_app1 ?p_app2 fxl' algo_rel'] p_split(1) Suc.prems by auto
    obtain fli' where trcl2: "(fli, p2 @ [SAT_PUSH (u, v)], fli') \<in> trcl algo_rel'"
        and trcl3: "(fli', p3, fxl') \<in> trcl algo_rel'"
      using trcl_unconcat[of fli "p2 @ [SAT_PUSH (u, v)]" p3 fxl' algo_rel'] trcl1' by auto
    obtain fi li where fli_def: "fli = (fi, li)" by (cases fli) auto
    
    {
      have "x = length ?L_app" using p_split(2) Suc.hyps L_split by auto    
      then have "length (filter (op = (SAT_PUSH (u, v))) ?p_app1) \<le> li u + li v + 2" 
        using Suc.hyps(1)[of ?p_app1 fxl fli] trcl1 fli_def by auto    
      then have "length (filter (op = (SAT_PUSH (u, v))) p) \<le> li u + li v + 3" 
        using p_split(2) L_split by auto
    }          
    also {
      obtain flb where "(flb, SAT_PUSH (u, v), fli) \<in> algo_rel'
        "using trcl_rev_uncons[OF trcl1] by blast
      moreover obtain fb lb where "flb = (fb, lb)" by (cases flb) auto
      ultimately have pe1: "Height_Bounded_Labeling c s t fb lb" and pe2:"sat_push_precond fb lb (u, v)"
        and pe3:"fi = (push_effect fb (u, v))" and pe4:"li = lb" using fli_def by (auto elim!: algo_rel'.cases)
      
      {
        interpret Height_Bounded_Labeling c s t fb lb using `Height_Bounded_Labeling c s t fb lb` .
        have "(u, v) \<notin> adm_edges fi lb" using sat_push_decr_adm_edges[OF pe2] pe3[symmetric] by auto
        moreover have "lb u = lb v + 1" using pe2 unfolding sat_push_precond_def by auto
        ultimately have "cf_of fi (u, v) = 0" unfolding adm_edges_def Graph.E_def by auto
      }
      then have "cf_of fi (u, v) = 0" and "li u = li v + 1" 
        using pe2 pe4 unfolding sat_push_precond_def by auto
      moreover note next_sat_push_at_increased_labeling[of li u v fi p2 "fst fli'" "snd fli'"]
      ultimately have "li u + li v < snd fli' u + snd fli' v" using trcl2 fli_def by auto
    }
    also {
      obtain fi' li' f' l' where 
        "fli' = (fi', li')" and "fxl' = (f', l')" by (cases fli', cases fxl') auto
      then have "snd fli' u + snd fli' v \<le> snd fxl' u + snd fxl' v" using trcl3
        relabel_path_mono[of fi' li' p3 f' l' u] relabel_path_mono[of fi' li' p3 f' l' v] by auto
    }
    finally show ?thesis by auto
  qed
qed
  
lemma sat_push_edge_chain_length:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (op= (SAT_PUSH (u,v))) p) \<le> 4 * card V"
proof (cases "p = []")
  case True
  then show ?thesis by auto
next
  case False
  then obtain x xs where "p = xs @ [x]" by (meson neq_Nil_rev_conv)
  then obtain fl where "(fl, x, fxl') \<in> algo_rel'" 
    using assms trcl_unconcat[of fxl xs "[x]" fxl' algo_rel'] by auto
  moreover obtain f l f' l' where "fl = (f, l)" and "fxl' = (f', l')" by (cases fl, cases fxl') auto
  ultimately have "Height_Bounded_Labeling c s t (fst fxl') (snd fxl')"
    using algo_rel'_Height_Bounded_Labeling_snd by auto

  then interpret Height_Bounded_Labeling c s t "(fst fxl')" "(snd fxl')" .
  
  {
    assume a1: "u \<in> V \<and> v \<in> V"
    then have "V \<noteq> {}" by auto
    then have "card V \<ge> 1" using min_dist_less_V nat_geq_1_eq_neqz by auto
      
    have "length (filter (op= (SAT_PUSH (u,v))) p) \<le> (snd fxl') u + (snd fxl') v + 2"
      using sat_push_edge_chain_height_sum[OF assms, of u v] by auto
    moreover have "(snd fxl') u \<le> 2 * card V - 1" and "(snd fxl') v \<le> 2 * card V - 1"
      using height_bound a1 by auto
    ultimately have ?thesis using `card V \<ge> 1` by auto
  }
  moreover {
    assume a1: "\<not> (u \<in> V \<and> v \<in> V)"
    then have ?thesis using sat_push_no_vertex_chain_length[OF assms] by auto
  }
  ultimately show ?thesis by blast
qed
end
  
context Height_Bounded_Labeling
begin
  
lemma unsat_push_action_count_AUX:
  assumes "relabel_precond f l u"
  shows "2 * card V * sum_heights_measure (relabel_effect f l u) + unsat_potential f (relabel_effect f l u)
   \<le> 2 * card V * sum_heights_measure l + unsat_potential f l" (is "?L1 + ?L2 \<le> _")
proof -
  have "?L1 + ?L2 \<le> ?L1 + 2 * card V + unsat_potential f l"
    using relabel_unsat_potential[OF assms] by auto
  also have "2 * card V * sum_heights_measure (relabel_effect f l u) + 2 * card V = 
    2 * card V * (sum_heights_measure (relabel_effect f l u) + 1)" by auto
  also have "sum_heights_measure (relabel_effect f l u) + 1 \<le> sum_heights_measure l"
    using relabel_measure[OF assms] by auto
  finally show ?thesis by auto
qed
  
end
  
  
context Network
begin  
(*************************************************************************************************
*****************************************NEW BOUNDS***********************************************
*************************************************************************************************)  
lemma relabel_action_count:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (is_RELABEL) p) < sum_heights_measure (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
  apply (auto elim!: algo_rel'.cases)  
  apply (drule (1) Height_Bounded_Labeling.relabel_measure)
  apply auto
  done

lemma sat_push_action_count: 
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter is_SAT_PUSH p) \<le> 8 * card V * card E" (is "?L \<le> ?R")
proof -
  let ?set_abs = "\<lambda>P. {i. i < length p \<and> P (p ! i)}"
  
  have "?L = card (?set_abs is_SAT_PUSH)" using length_filter_conv_card by auto
  also {
    have "?set_abs (is_SAT_PUSH) = (?set_abs (\<lambda>a.\<exists>u v.((u,v)\<notin>E\<and>(v,u)\<notin>E) \<and> a=SAT_PUSH (u,v)))
      \<union> (?set_abs (\<lambda>a. \<exists>u v. ((u,v)\<in>E\<or>(v,u)\<in>E) \<and> a = SAT_PUSH (u,v)))" (is "?SL = ?SR1 \<union> ?SR2") 
      using is_SAT_PUSH_def by auto
    then have fct1: "card ?SL \<le> card ?SR1 + card?SR2" by (simp add: card_Un_le)
    
    have "?SR2 = (?set_abs (\<lambda>a. \<exists>u v. (u,v)\<in>E \<and> a = SAT_PUSH (u,v)))
    \<union> (?set_abs (\<lambda>a. \<exists>u v. (v,u)\<in>E \<and> a = SAT_PUSH (u,v)))" (is "_ = ?SR21 \<union> ?SR22") by auto
    then have fct2: "card ?SR2 \<le> card ?SR21 + card ?SR22" by (simp add: card_Un_le)
  
    
    note fct1 fct2
    then have "card ?SL \<le> card ?SR1 + card ?SR21 + card ?SR22" by auto      
    also have "card ?SR1 = length (filter (\<lambda>a.\<exists>u v.((u,v)\<notin>E\<and>(v,u)\<notin>E) \<and> a=SAT_PUSH (u,v)) p)"
      using length_filter_conv_card[symmetric, of p] by auto
    also have "\<dots> = 0"
      using assms 
      apply(induction rule:trcl.induct)
      apply (auto elim!: algo_rel'.cases simp add:sat_push_precond_def)
      using cfE_of_ss_invE by blast
    also have "card ?SR21 \<le> (\<Sum>(u,v)\<in>E. length (filter (op= (SAT_PUSH (u,v))) p))"
    proof -
      have "?SR21 = (\<Union>(u, v)\<in>E. {i. i < length p \<and>  p ! i = SAT_PUSH (u, v)})" by auto
      then have "card ?SR21 \<le> (\<Sum>(u,v)\<in>E. card {i. i < length p \<and>  p ! i = SAT_PUSH (u, v)})" using
        card_Union_Sum_le[OF finite_E, of "\<lambda>(u,v). {i. i < length p \<and>  p ! i = SAT_PUSH (u,v)}"]
        by auto
      also have "\<dots> = (\<Sum>(u,v)\<in>E. length (filter (op= (SAT_PUSH (u,v))) p))"
      proof -
        have "card {i. i < length p \<and>  p ! i = SAT_PUSH (u, v)} = 
          length (filter (op= (SAT_PUSH (u,v))) p)" for u v
          using length_filter_conv_card[symmetric, of p "\<lambda>a. a= SAT_PUSH (u,v)"] 
          by (metis (mono_tags, lifting) filter_cong)
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed  
    also have "card ?SR22 \<le> (\<Sum>(v,u)\<in>E. length (filter (op= (SAT_PUSH (u,v))) p))"
    proof -
      have "?SR22 = (\<Union>(v, u)\<in>E. {i. i < length p \<and>  p ! i = SAT_PUSH (u, v)})" by auto
      then have "card ?SR22 \<le> (\<Sum>(v,u)\<in>E. card {i. i < length p \<and>  p ! i = SAT_PUSH (u, v)})" using
        card_Union_Sum_le[OF finite_E, of "\<lambda>(v,u). {i. i < length p \<and>  p ! i = SAT_PUSH (u,v)}"]
        by (metis (no_types, lifting) case_prod_conv cond_case_prod_eta) 
      also have "\<dots> = (\<Sum>(v,u)\<in>E. length (filter (op= (SAT_PUSH (u,v))) p))"
      proof -
        have "card {i. i < length p \<and>  p ! i = SAT_PUSH (u, v)} = 
          length (filter (op= (SAT_PUSH (u,v))) p)" for v u
          using length_filter_conv_card[symmetric, of p "\<lambda>a. a= SAT_PUSH (u,v)"] 
          by (metis (mono_tags, lifting) filter_cong)
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
    finally have "card ?SL \<le> (\<Sum>(u,v)\<in>E. length (filter (op= (SAT_PUSH (u,v))) p)) + 
      (\<Sum>(v,u)\<in>E. length (filter (op= (SAT_PUSH (u,v))) p))" by auto
  }
  also have "(\<Sum>(u, v)\<in>E. length (filter (op = (SAT_PUSH (u, v))) p)) \<le> 4 * card E * card V"
  proof -
    have "length (filter (op = (SAT_PUSH (u, v))) p) \<le> 4 * card V" for u v
      using sat_push_edge_chain_length[OF assms] by simp
    then have "(\<Sum>(u, v)\<in>E. length (filter (op = (SAT_PUSH (u, v))) p)) \<le> (\<Sum>(u, v)\<in>E. 4 * card V)"
      by (metis (no_types, lifting) case_prodE2 nat_le_linear old.prod.case sum_mono)
    thus ?thesis by auto
  qed
  also have "(\<Sum>(v, u)\<in>E. length (filter (op = (SAT_PUSH (u, v))) p)) \<le> 4 * card E * card V"
  proof -
    have "length (filter (op = (SAT_PUSH (u, v))) p) \<le> 4 * card V" for u v
      using sat_push_edge_chain_length[OF assms] by simp
    then have "(\<Sum>(v, u)\<in>E. length (filter (op = (SAT_PUSH (u, v))) p)) \<le> (\<Sum>(v, u)\<in>E. 4 * card V)"
      by (metis (no_types, lifting) case_prodE2 nat_le_linear old.prod.case sum_mono)
    thus ?thesis by auto
  qed
  finally show ?thesis by auto
qed
    
lemma unsat_push_action_count:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (is_UNSAT_PUSH) p) < unsat_potential (fst fxl) (snd fxl) +
    2 * card V * length (filter is_SAT_PUSH p) +
    2 * card V * sum_heights_measure (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
   apply (auto elim!: algo_rel'.cases)
  apply (drule (1) Height_Bounded_Labeling.sat_push_unsat_potential; simp add: sat_push_action_count)
  apply (drule (1) Height_Bounded_Labeling.unsat_push_measure(2); auto)
  apply (drule (1) Height_Bounded_Labeling.unsat_push_action_count_AUX; auto)  
  done

(***********************
************************
*******Complexity*******
************************
******** O(V\<^sup>2E) ********) 
theorem algo_rel'_complexity:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length p \<le> 
           4 * (card V)^2 + 8 * card V * card E +  4 * (card V)^3  + 16 *(card V)^2 * card E"
proof (cases "p = []")
  case True
  then show ?thesis by auto
next
  case False
  let ?set_abs = "\<lambda>P. {i. i < length p \<and> P (p ! i)}"
  
  have "length p = length (filter (\<lambda>_. True) p)" by auto
  also have "\<dots> = length (filter (\<lambda>a. a = RELABEL \<or> a = UNSAT_PUSH \<or> is_SAT_PUSH a) p)" 
    by (metis op_type.exhaust is_SAT_PUSH_def)
  also have "\<dots> = card (?set_abs (\<lambda>a. a = RELABEL \<or> a = UNSAT_PUSH \<or> is_SAT_PUSH a))"
    using length_filter_conv_card by auto
  also have "\<dots> \<le> card (?set_abs (is_RELABEL)) + card (?set_abs (is_UNSAT_PUSH)) +
    card (?set_abs is_SAT_PUSH)" (is "?C0 \<le> ?C1 + ?C2 + ?C3")
  proof -
    have "?set_abs (\<lambda>a. a = RELABEL \<or> a = UNSAT_PUSH \<or> is_SAT_PUSH a) = 
      ?set_abs (\<lambda>a. a = RELABEL) \<union> ?set_abs (\<lambda>a. a = UNSAT_PUSH \<or> is_SAT_PUSH a)" 
      (is "?SL = ?SR1 \<union> ?SR2") by auto
    then have fct1: "card ?SL \<le> card ?SR1 + card?SR2" by (simp add: card_Un_le)
    
    have "?SR2 = ?set_abs (\<lambda>a. a = UNSAT_PUSH) \<union> ?set_abs is_SAT_PUSH"
      (is "_ = ?SR21 \<union> ?SR22") by auto
    then have fct2: "card ?SR2 \<le> card ?SR21 + card ?SR22" by (simp add: card_Un_le)
  
    note fct1 fct2  
    then have "?C0 \<le> card ?SR1 + card ?SR21 + card ?SR22" by auto
    moreover have "card ?SR1 = ?C1" by (fo_rule arg_cong) auto
    moreover have "card ?SR21 = ?C2" by (fo_rule arg_cong) auto
    moreover have "card ?SR22 = ?C3" by metis
    ultimately show ?thesis by metis
  qed
  also have "?C1 = length (filter (is_RELABEL) p)" using length_filter_conv_card[symmetric] by auto
  also have "?C2 = length (filter (is_UNSAT_PUSH) p)" using length_filter_conv_card[symmetric] by auto
  also have "?C3 = length (filter is_SAT_PUSH p)" 
    using length_filter_conv_card[symmetric, of p "is_SAT_PUSH"] by auto
  finally have p_spl:"length p \<le> length (filter (is_RELABEL) p) + length (filter (is_UNSAT_PUSH) p) +
    length (filter is_SAT_PUSH p)" by auto
  
  {
    have f1: "sum_heights_measure l \<le> 2 * card V * card V" for l
      unfolding  sum_heights_measure_def
    proof -
      have "2 * card V - l v \<le> 2 * card V" for v by auto
      then have "(\<Sum>v\<in>V. 2 * card V - l v) \<le> (\<Sum>v\<in>V. 2 * card V)" by (meson sum_mono)
      also have "(\<Sum>v\<in>V. 2 * card V) = card V * (2 * card V)" using finite_V by auto
      finally show "(\<Sum>v\<in>V. 2 * card V - l v) \<le> 2 * card V * card V" by auto
    qed
    
    have f2: "unsat_potential (fst fxl) (snd fxl) \<le> 2 * card V * card V "
    proof -
      obtain a as where "p = a # as" using False by (cases p) auto
      then obtain fli where "(fxl, a, fli) \<in> algo_rel'" using assms by (meson trcl_uncons_cases)
      moreover obtain f l f' l' where "fxl = (f, l)" and "fli = (f', l')" by (cases fxl, cases fli) auto
      ultimately have "Height_Bounded_Labeling c s t f l" using algo_rel'_Height_Bounded_Labeling_fst by auto
      
      then interpret Height_Bounded_Labeling c s t f l .
      have "unsat_potential (fst fxl) (snd fxl) = (\<Sum>v\<in>{v \<in> V. 0 < excess f v}. l v)" 
        unfolding unsat_potential_def using `fxl = (f, l)` by auto
      also have "\<dots> \<le> (\<Sum>v\<in>V. l v)"
      proof -
        have f1:"{v \<in> V. 0 < excess f v} \<subseteq> V" by auto
        thus ?thesis using sum.subset_diff[OF f1 finite_V, of l] by auto
      qed
      also have "\<dots>  \<le> (\<Sum>v\<in>V. 2 * card V - 1)" using height_bound by (meson sum_mono)
      also have "\<dots> = card V * (2 * card V - 1)" by auto
      also have "card V * (2 * card V - 1) \<le> 2 * card V * card V" by auto
      finally show ?thesis .
    qed
    
    note f1 f2
  } note sum_abs = this
    
  note p_spl 
  also {
    have "length (filter (is_UNSAT_PUSH) p) \<le> 2 * card V * card V +
    2 * card V * length (filter is_SAT_PUSH p) +
    2 * card V * (sum_heights_measure (snd fxl))"
      using unsat_push_action_count[OF assms] sum_abs(2) by auto
    also have "\<dots> = 2 * card V * (card V + 
      length (filter is_SAT_PUSH p) + (sum_heights_measure (snd fxl)))"
      by (simp add: add_mult_distrib2)
    also have "length (filter is_SAT_PUSH p) \<le> 8 * card V * card E"
      using sat_push_action_count[OF assms] by auto
    also note sum_abs(1)[of "snd fxl"]
    also have "2 * card V * (card V + 8 * card V * card E + 2 * card V * card V) = 
       2 * card V * card V * (1 + 8 * card E + 2 * card V)" using add_mult_distrib2 by auto
    finally have "length (filter (is_UNSAT_PUSH) p) \<le>
       2 * card V * card V * (1 + 8 * card E + 2 * card V)" by auto
  }
  also have "length (filter (is_RELABEL) p) \<le> 2 * card V * card V" 
    using relabel_action_count[OF assms] sum_abs(1)[of "snd fxl"] by auto
  also have "length (filter is_SAT_PUSH p) \<le> 8 * card V * card E"
    using sat_push_action_count[OF assms] by auto
  also have "2 * card V * card V + 2 * card V * card V * (1 + 8 * card E + 2 * card V) =
     2 * card V * card V * (1 + (1 + 8 * card E + 2 * card V))" by simp
  also have "1 + (1 + 8 * card E + 2 * card V) = 2 * (1 + card V + 4 * card E)" by auto
  also have "2 * card V * card V * (2 * (1 + card V + 4 * card E)) = 
    4 * card V * card V * (1 + card V + 4 * card E)" by auto
  also have "\<dots> = 4 * card V * card V + 4 * card V * card V * card V + 4 * card V * card V * 4 * card E"
    by (simp add: distrib_left)
  also have "\<dots> = 4 * (card V)^2 + 4 * (card V)^3 + 16 *(card V)^2 * (card E)"
    by (simp add: power2_eq_square power3_eq_cube)
  finally show ?thesis by auto
qed

lemma sum_heights_measure_bound: "sum_heights_measure l \<le> 2 * (card V)^2"
  unfolding  sum_heights_measure_def
proof -
  have "2 * card V - l v \<le> 2 * card V" for v by auto
  then have "(\<Sum>v\<in>V. 2 * card V - l v) \<le> (\<Sum>v\<in>V. 2 * card V)" by (meson sum_mono)
  also have "(\<Sum>v\<in>V. 2 * card V) = card V * (2 * card V)" using finite_V by auto
  finally show "(\<Sum>v\<in>V. 2 * card V - l v) \<le> 2 * (card V)^2" by (simp add: power2_eq_square)
qed

lemma (in Height_Bounded_Labeling) unsat_potential_bound:
  shows "unsat_potential f l \<le> 2 * (card V)^2"
proof -
  have "unsat_potential f l = (\<Sum>v\<in>{v \<in> V. 0 < excess f v}. l v)" 
    unfolding unsat_potential_def by auto
  also have "\<dots> \<le> (\<Sum>v\<in>V. l v)"
  proof -
    have f1:"{v \<in> V. 0 < excess f v} \<subseteq> V" by auto
    thus ?thesis using sum.subset_diff[OF f1 finite_V, of l] by auto
  qed
  also have "\<dots>  \<le> (\<Sum>v\<in>V. 2 * card V - 1)" using height_bound by (meson sum_mono)
  also have "\<dots> = card V * (2 * card V - 1)" by auto
  also have "card V * (2 * card V - 1) \<le> 2 * card V * card V" by auto
  finally show ?thesis by (simp add: power2_eq_square)
qed

  
lemma relabel_action_bound:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter is_RELABEL p) < 2*(card V)^2 + 1"
proof -
  note relabel_action_count[OF assms]
  also note sum_heights_measure_bound
  finally show ?thesis 
    by (simp add: power2_eq_square)  
qed
  
lemma unsat_push_action_bound:
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (is_UNSAT_PUSH) p) < 
    2* (card V)^2 +
    16 * (card V)^2 * card E +
    4 * (card V)^3 
    + 1" (is "_ < ?B")
proof (cases p)
  case Nil thus ?thesis by simp
next
  case Cons then obtain f l where FXL[simp]: "fxl=(f,l)" "Height_Bounded_Labeling c s t f l"
    using assms by (cases fxl;auto dest!: trcl_uncons elim!: algo_rel'.cases)
  then interpret Height_Bounded_Labeling c s t f l by simp
    
  note unsat_push_action_count[OF assms, unfolded FXL fst_conv snd_conv]
  also note unsat_potential_bound
  also note sat_push_action_count[OF assms]
  also note sum_heights_measure_bound[of l]  
  finally have "length (filter (is_UNSAT_PUSH) p)
      < 2 * (card V)\<^sup>2 
      + 2 * card V * (8 * card V * card E) 
      + 2 * card V * (2 * (card V)\<^sup>2) 
      + 1" 
    by simp
  also have "\<dots> = ?B" by (simp add: power2_eq_square power3_eq_cube)
  finally show ?thesis .    
qed    
  
  
(* Estimating elementary operations: Push: O(1), Relabel: O(V) *)  
  
fun op_estimate where
  "op_estimate (RELABEL) = (card V)"
| "op_estimate (UNSAT_PUSH) = 1"
| "op_estimate (SAT_PUSH _) = 1"
  
lemma op_estimate_alt: 
  "op_estimate a = (case a of RELABEL \<Rightarrow> card V | _ \<Rightarrow> 1)" 
  by (cases a) auto
  
lemma pp_split_op_sum:
  fixes f :: "_ \<Rightarrow> _::comm_monoid_add"
  shows "sum_list (map f l) = 
    sum_list (map f (filter is_RELABEL l))
  + sum_list (map f (filter is_UNSAT_PUSH l))
  + sum_list (map f (filter is_SAT_PUSH l))"
  apply (induction l)
  applyS simp  
  subgoal for x l by (cases x) (auto simp: algebra_simps)
  done

end
  
context Network begin  
  
definition "algo_rel'_bound \<equiv> 
    card V
  + 2 * (card V)^2
  + 8 * card V * card E
  + 6 * (card V)^3
  + 16 * (card V)^2 * card E"
  
lemma algo_rel'_bound_is_OV2E: "algo_rel'_bound \<le> 39 * (card V)^2 * card E"  
proof -
  have "card V \<le> card (fst`E) + card (snd`E)"
    by (auto simp: card_Un_le V_alt)
  also note card_image_le[OF finite_E]
  also note card_image_le[OF finite_E]
  finally have "card V \<le> 2 * card E" by auto

  let ?V2E = "(card V)^2 * card E"
      
  have AUX: "card V \<le> card V * card E" 
    using \<open>card V \<le> 2 * card E\<close> by auto
  have 1: "card V * card E \<le> ?V2E" 
    by (simp add: power2_eq_square)
  have 2: "card V \<le> ?V2E"
    using 1 AUX order_trans by blast
  have 3: "(card V)^2 \<le> ?V2E" 
    using \<open>card V \<le> card V * card E\<close> by auto
  have 4: "(card V)^3 \<le> 2*?V2E" 
    by (simp add: \<open>card V \<le> 2 * card E\<close> power2_eq_square power3_eq_cube)
      
  from 1 2 3 4 show ?thesis
    unfolding algo_rel'_bound_def
    by linarith   
qed      
  
theorem algo_rel'_bound: 
  assumes P: "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "sum_list (map op_estimate p) \<le> algo_rel'_bound"
proof -  
  have 1: "map op_estimate (filter is_RELABEL p) = map (\<lambda>_. card V) (filter is_RELABEL p)"
    apply (rule map_cong)
    by (auto simp: op_estimate_alt split: op_type.split)
  have [simp]: "sum_list (map op_estimate (filter is_RELABEL p)) = card V * length (filter is_RELABEL p)"
    by (auto simp: 1 sum_list_triv) 
  

  have 2: "map op_estimate (filter is_UNSAT_PUSH p) = map (\<lambda>_. 1) (filter is_UNSAT_PUSH p)"
    apply (rule map_cong)
    by (auto simp: op_estimate_alt split: op_type.split)
  have [simp]: "sum_list (map op_estimate (filter is_UNSAT_PUSH p)) = length (filter is_UNSAT_PUSH p)"
    by (auto simp: 2 sum_list_triv) 
  
  have 3: "map op_estimate (filter is_SAT_PUSH p) = map (\<lambda>_. 1) (filter is_SAT_PUSH p)"
    apply (rule map_cong)
    by (auto simp: op_estimate_alt split: op_type.split)
  have [simp]: "sum_list (map op_estimate (filter is_SAT_PUSH p)) = length (filter is_SAT_PUSH p)"
    by (auto simp: 3 sum_list_triv) 
      
  have "sum_list (map op_estimate p) = 
      card V * length (filter is_RELABEL p) 
    + length (filter is_UNSAT_PUSH p) 
    + length (filter is_SAT_PUSH p)"
    unfolding pp_split_op_sum[where l=p]
    by simp
  also note relabel_action_bound[OF P]    
  also note unsat_push_action_bound[OF P]    
  also note sat_push_action_count[OF P]    
  finally show ?thesis  
    unfolding algo_rel'_bound_def
    using card_V_ge2
    by (simp add: algebra_simps power2_eq_square power3_eq_cube less_Suc_eq_le)
qed      
      
  
  
end
  
(* Let's show that our "algorithm" actually computes a maximum flow *)  
  
lemma trcl_len_bounded_imp_ex_terminal:
  assumes BOUNDED: "\<And>p s'. (s,p,s')\<in>trcl R \<Longrightarrow> length p \<le> B"
  shows "\<exists>p s'. (s,p,s')\<in>trcl R \<and> s'\<notin>Domain R"  
proof (rule ccontr; clarsimp)
  assume A: "\<forall>p s'. (s, p, s') \<in> trcl R \<longrightarrow> s' \<in> Domain R"
  have "\<exists>p s'. (s,p,s') \<in> trcl R \<and> length p = l" for l
  proof (induction l)
    case 0 thus ?case by auto
  next
    case (Suc n)
    then obtain p s' where STEPS: "(s, p, s') \<in> trcl R" and [simp]: "n = length p" by auto
    note STEPS
    also from A[rule_format, OF STEPS] obtain a s'' where "(s',a,s'') \<in> R" by auto
    finally show ?case by auto    
  qed      
  with BOUNDED show False by (metis impossible_Cons)
qed      
  
  
context Network begin
  definition "gpp_results \<equiv> { 
    f'. \<exists>p l'. ((pp_init_f,pp_init_l),p,(f',l')) \<in> trcl algo_rel' 
    \<and> (f',l')\<notin>Domain algo_rel' }"
  
  
  theorem has_result:
    shows "gpp_results \<noteq> {}"
    unfolding gpp_results_def
    apply clarsimp
    using trcl_len_bounded_imp_ex_terminal[of "(pp_init_f,pp_init_l)" algo_rel']
      algo_rel'_complexity[of "(pp_init_f,pp_init_l)"]
      by (simp;blast)
      
  lemma trcl_algo_rel'_Height_Bounded_Labeling_snd:
    assumes "((pp_init_f,pp_init_l),p,(f,l)) \<in> trcl algo_rel'"
    shows "Height_Bounded_Labeling c s t f l"  
    using assms
    apply (induction p arbitrary: f l rule: rev_induct)  
    by (auto simp: pp_init_height_bound algo_rel'_Height_Bounded_Labeling_snd dest!: trcl_rev_uncons)
        
  theorem results_correct: "gpp_results \<subseteq> Collect isMaxFlow"
    unfolding gpp_results_def
  proof (clarsimp)    
    fix p f l
    assume "((pp_init_f, pp_init_l), p, f, l) \<in> trcl algo_rel'" 
    then interpret Height_Bounded_Labeling c s t f l 
      by (rule trcl_algo_rel'_Height_Bounded_Labeling_snd)
      
    assume "(f,l)\<notin>Domain algo_rel'"    
    hence "\<forall>u v. \<not>sat_push_precond f l (u,v) \<and> \<not>unsat_push_precond f l (u,v) \<and> \<not>relabel_precond f l u"  
      by (meson Domain.DomainI Height_Bounded_Labeling_axioms algo_rel'.relabel' algo_rel'.sat_push' algo_rel'.unsat_push')

    thus "isMaxFlow f" 
      by (simp add: push_precond_eq_sat_or_unsat push_relabel_term_imp_maxflow)
  qed      
  
    
subsection \<open>Complexity Result Summary\<close>    
text \<open>
  We summarize the complexity result of \<open>O(V\<^sup>2E)\<close>.
\<close>
  
text \<open>
  First, we define a relation that describes steps of the generic push-relabel
  algorithm:
\<close>  
datatype relabel_or_push = is_RELABEL: RELABEL | is_PUSH: PUSH    
inductive_set pp_algo where
  push: "\<lbrakk>push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),PUSH,(push_effect f e,l))\<in>pp_algo"
| relabel: "\<lbrakk>relabel_precond f l u\<rbrakk>
    \<Longrightarrow> ((f,l),RELABEL,(f,relabel_effect f l u))\<in>pp_algo"

text \<open>
  Next, we estimate that relabel steps need \<open>V\<close> units, and push steps need \<open>1\<close> 
  unit of work.
\<close>  
fun cost_estimate :: "relabel_or_push \<Rightarrow> nat" where
  "cost_estimate RELABEL = card V"
| "cost_estimate PUSH = 1"  

text \<open>
  Finally, we show our main theorem:
  If the algorithm executes some steps from the beginning, then
    \<^enum> The cost of these steps is bounded by \<open>O(V\<^sup>2E)\<close>. Note that this also implies termination.
    \<^enum> If no further steps are possible from the reached state, we have computed a maximum flow.
\<close>  
theorem generic_preflow_push_OV2E_and_correct:
  assumes A: "((pp_init_f, pp_init_l), p, (f, l)) \<in> trcl pp_algo" 
  shows "(\<Sum>x\<leftarrow>p. cost_estimate x) \<le> 39 * (card V)^2 * card E" (is ?G1)
    and "(f,l)\<notin>Domain pp_algo \<longrightarrow> isMaxFlow f" (is ?G2)
proof -
  from A have "\<exists>p'. ((pp_init_f, pp_init_l), p', (f, l)) \<in> trcl algo_rel' 
    \<and> (\<Sum>x\<leftarrow>p. cost_estimate x) = (\<Sum>x\<leftarrow>p'. op_estimate x)" 
  proof (induction p arbitrary: f l rule: rev_induct)
    case Nil then show ?case by (auto intro: exI[where x="[]"])
  next
    case (snoc a p) 
    then obtain fh lh where 
      PREFIX: "((pp_init_f, pp_init_l), p, (fh,lh)) \<in> trcl pp_algo" 
      and LAST: "((fh,lh),a,(f,l)) \<in> pp_algo" 
      by (auto dest!: trcl_rev_uncons)
        
    from snoc.IH[OF PREFIX] obtain p' where IH:
      "((pp_init_f, pp_init_l), p', fh, lh) \<in> trcl algo_rel'"
      "sum_list (map cost_estimate p) = sum_list (map op_estimate p')"
      by auto
        
    from IH(1) trcl_algo_rel'_Height_Bounded_Labeling_snd 
    interpret Height_Bounded_Labeling c s t fh lh by simp
        
    from LAST have "\<exists>a'. ((fh,lh),a',(f,l))\<in>algo_rel' \<and> cost_estimate a = op_estimate a'"
    proof cases
      case (push e) note [simp] = push(1-3)
      from \<open>push_precond fh lh e\<close> have "sat_push_precond fh lh e \<or> unsat_push_precond fh lh e"
        by (simp add: push_precond_eq_sat_or_unsat)
      thus ?thesis
        apply (rule disjE)
        subgoal  
          apply (rule exI[where x="SAT_PUSH e"])
          apply (simp add: algo_rel'.intros Height_Bounded_Labeling_axioms)
          done  
        subgoal  
          apply (rule exI[where x="UNSAT_PUSH"])
          apply (simp add: algo_rel'.intros Height_Bounded_Labeling_axioms)
          done  
        done    
    next
      case (relabel u)
      then show ?thesis
        apply -
        apply (rule exI[where x="op_type.RELABEL"])
        apply (auto intro: algo_rel'.intros Height_Bounded_Labeling_axioms)
        done
    qed
    then obtain a' where "((fh,lh),a',(f,l))\<in>algo_rel'" and "cost_estimate a = op_estimate a'" by blast
    with IH show ?case 
      apply (rule_tac exI[where x="p'@[a']"])
      by (auto intro: trcl_rev_cons)  
      
  qed
  then obtain p' where
    A': "((pp_init_f, pp_init_l), p', (f, l)) \<in> trcl algo_rel'"
    and [simp]: "(\<Sum>x\<leftarrow>p. cost_estimate x) = (\<Sum>x\<leftarrow>p'. op_estimate x)" 
    by blast

  show ?G1
    using order_trans[OF algo_rel'_bound[OF A'] algo_rel'_bound_is_OV2E]
    by simp  
      
  show ?G2 proof
    have D_AUX: "Domain pp_algo = { (f,l). (\<exists>e. push_precond f l e) \<or> (\<exists>u. relabel_precond f l u) }"
      by (auto simp: Domain_iff pp_algo.simps; blast)
    
    assume "(f, l) \<notin> Domain pp_algo"
    hence ND: "(f, l) \<notin> Domain algo_rel'"  
      apply clarify
      apply (erule algo_rel'.cases; auto simp: D_AUX push_precond_eq_sat_or_unsat)  
      done  
    thus "isMaxFlow f"    
      using results_correct A' unfolding gpp_results_def
      by auto
  qed      
qed    
    
end  
  
end
