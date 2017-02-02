theory Preflow_Complexity_Test
imports Preflow
begin
  
context Height_Bounded_Labeling begin 
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
  
(* 26.23 part I *)
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
  
(* 26.23 part II *)
lemma relable_unsat_potential:
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
  
end  
  
context Network begin    
(*definition "RR \<equiv> 
  { ((f, relabel_effect f l u), (f,l)) | f u l. Height_Bounded_Labeling c s t f l \<and> relabel_precond f l u }
\<union> { ((push_effect f e,l),(f,l)) | f e l. Height_Bounded_Labeling c s t f l \<and> sat_push_precond f l e }
"
    
lemma "RR \<subseteq> measure (\<lambda>(f,l). (sum_heights_measure l + 1) * card_adm_measure f l)"
  unfolding RR_def 
  apply auto
  using Height_Bounded_Labeling.relabel_measure Height_Bounded_Labeling.unsat_push_measure
  apply auto
  oops*)
    
datatype op_type = RELABEL | UNSAT_PUSH | SAT_PUSH edge   
inductive_set algo_rel' where
  unsat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; unsat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),UNSAT_PUSH,(push_effect f e,l))\<in>algo_rel'"
| sat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; sat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),SAT_PUSH e,(push_effect f e,l))\<in>algo_rel'"
| relabel': "\<lbrakk>Height_Bounded_Labeling c s t f l; relabel_precond f l u \<rbrakk>
    \<Longrightarrow> ((f,l),RELABEL,(f,relabel_effect f l u))\<in>algo_rel'"
    
 
lemma
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (op= RELABEL) p) < sum_heights_measure (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
  apply (auto elim!: algo_rel'.cases)  
  apply (drule (1) Height_Bounded_Labeling.relabel_measure)
  apply auto
  done  

(*
  Cormen bounds this by |V||E| instead of |V|\<^sup>3, so later he can use it to build the measure for
  un-saturating pushes (a |V| multiplier is added). We have to make this smaller, or come up with
  a new measure for un-sturated pushes.
*)
lemma
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (\<lambda>x. \<exists>e. x = SAT_PUSH e) p) < card V * sum_heights_measure (snd fxl) + card_adm_measure (fst fxl) (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
  apply (auto elim!: algo_rel'.cases)  
  apply (drule (1) Height_Bounded_Labeling.sat_push_measure; auto)
  apply (drule (1) Height_Bounded_Labeling.unsat_push_measure(1); auto)
  apply (drule (1) Height_Bounded_Labeling.relabel_sum_height_card_adm_measure; auto)
  done

lemma
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (op= UNSAT_PUSH) p) <  card_adm_measure (fst fxl) (snd fxl) + unsat_potential (fst fxl) (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
  apply (auto elim!: algo_rel'.cases)
  apply (frule (1) Height_Bounded_Labeling.unsat_push_measure(1))
  apply (drule (1) Height_Bounded_Labeling.unsat_push_measure(2); auto)
  oops
    
lemma
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
      and "u \<in> V"
  shows "(snd fxl) u \<le> (snd fxl') u"
  using assms
  apply (induction rule: trcl.induct)
   apply (auto elim!: algo_rel'.cases)
  subgoal for _ _ _ _ _ u
  apply (drule (1) Height_Bounded_Labeling.relabel_measure)
  apply auto
  done      
    
    find_theorems "relabel_effect"
    
    
    (*
    
datatype zz_type = ZIG | ZAG
    
inductive_set zigzag_rel :: "nat \<Rightarrow> nat \<Rightarrow> (nat, zz_type list) LTS" for start max where
  z_flt[simp]: "\<lbrakk>start \<le> max\<rbrakk> \<Longrightarrow> (start, [], start) \<in> (zigzag_rel start max)"
| z_rhs[simp]: "\<lbrakk>(a, [], a) \<in> (zigzag_rel start max); a + 1 \<le> max\<rbrakk> 
              \<Longrightarrow> (a, [ZIG], a + 1) \<in> (zigzag_rel start max)"
| z_lhs[simp]: "\<lbrakk>(a, [], a) \<in> (zigzag_rel start max); a + 1 \<le> max\<rbrakk> 
              \<Longrightarrow> (a + 1, [ZAG], a) \<in> (zigzag_rel start max)"    
| z_zig[simp]: "\<lbrakk>(a + 1, p, a) \<in> (zigzag_rel start max); hd p = ZAG; a + 2 \<le> max\<rbrakk> 
              \<Longrightarrow> (a + 1, ZIG#p, a + 2) \<in> (zigzag_rel start max)"
| z_zag[simp]: "\<lbrakk>(a, p, a + 1) \<in> (zigzag_rel start max); hd p = ZIG; a + 2 \<le> max\<rbrakk> 
              \<Longrightarrow> (a + 2, ZAG#p, a + 1) \<in> (zigzag_rel start max)"
  
lemma 
  assumes "(a, p, b) \<in> (zigzag_rel st mx)"
  shows "(p = [] \<and> a = b \<and> a = st) \<or> (p \<noteq> [] \<and> ((a = b + 1) \<or> (b = a + 1)))"
    and "st \<le> a" and "a \<le> mx" and "st \<le> b" and "b \<le> mx"
  using assms
  by (induction rule: zigzag_rel.induct) auto
    
lemma
  assumes "x = y + 1"
      and "x \<le> mx" and "st \<le> y"
    obtains p where "(x, p, y) \<in> (zigzag_rel st mx)"
  apply (auto elim:zigzag_rel.cases)
      sledgehammer
proof -
qed
  
  
  
  
inductive_set zigzag_chn :: "nat \<Rightarrow> nat \<Rightarrow> (nat, zz_type list) LTS" for start max where
  empty[simp]: "\<lbrakk>start \<le> max\<rbrakk> \<Longrightarrow>(start, [], start) \<in> (zigzag_chn start max)"
  zrgt
| cons1[simp]: "\<lbrakk> (a,ZIG,b) \<in> (zigzag_rel start max); (a',xs,ab'') \<in> (zigzag_chn start max); \<rbrakk>
                \<Longrightarrow> (ab,x#xs,ab'') \<in> (zigzag_chn start max)"
  
lemma arb1:
  assumes "((a, b), lbl, (a', b')) \<in> (zigzag_rel st mx)"
    shows "a' \<ge> a" and "b' \<ge> b"
  using assms
  by (induction rule: zigzag_rel.induct) auto
    
lemma arb1':
  assumes "((a, b), lbl, (a', b')) \<in> (zigzag_rel st mx)"
    shows "st \<le> a" and "b' \<le> mx"
  using assms
  by (induction rule: zigzag_rel.induct) auto
    
lemma arb2:
  assumes "(ab, P, ab') \<in> (zigzag_chn st mx)"
  shows "fst ab \<le> fst ab'" and "snd ab \<le> snd ab'"
  using assms 
   apply (induction rule: zigzag_chn.induct)
    apply (auto elim: zigzag_chn.cases)
   apply (drule arb1; simp)
  by (drule arb1; simp)
    
lemma arb2':
  assumes "(ab, P, ab') \<in> (zigzag_chn st mx)"
  shows "st \<le> fst ab" and "snd ab' \<le> mx"    
  using assms 
   apply (induction rule: zigzag_chn.induct)
     apply (auto elim: zigzag_chn.cases) 
  by (drule arb1', simp)
    

  
    *)
end
end
