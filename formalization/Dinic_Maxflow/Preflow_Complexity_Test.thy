theory Preflow_Complexity_Test
imports Preflow
begin
  
context Height_Bounded_Labeling begin
lemma relabel_adm_measure_change:
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
  
lemma relabel_measure_height_adm:
  assumes "relabel_precond f l u"
  shows "card V * sum_heights_measure (relabel_effect f l u) + card_adm_measure f (relabel_effect f l u)
   \<le> card V * sum_heights_measure l + card_adm_measure f l" (is "?L1 + ?L2 \<le> _")
proof -
  have "?L1 + ?L2 \<le> ?L1 + card V + card_adm_measure f l"
    using relabel_adm_measure_change[OF assms] by auto
  also have "card V * sum_heights_measure (relabel_effect f l u) + card V = 
    card V * (sum_heights_measure (relabel_effect f l u) + 1)" by auto
  also have "sum_heights_measure (relabel_effect f l u) + 1 \<le> sum_heights_measure l"
    using relabel_measure[OF assms] by auto
  finally show ?thesis by auto
qed
  
  
end  
  
context Network begin    
definition "RR \<equiv> 
  { ((f, relabel_effect f l u), (f,l)) | f u l. Height_Bounded_Labeling c s t f l \<and> relabel_precond f l u }
\<union> { ((push_effect f e,l),(f,l)) | f e l. Height_Bounded_Labeling c s t f l \<and> sat_push_precond f l e }
"
    
lemma "RR \<subseteq> measure (\<lambda>(f,l). (sum_heights_measure l + 1) * card_adm_measure f l)"
  unfolding RR_def 
  apply auto
  using Height_Bounded_Labeling.relabel_measure Height_Bounded_Labeling.unsat_push_measure
  apply auto
  oops
    
datatype op_type = RELABEL | UNSAT_PUSH | SAT_PUSH    
inductive_set algo_rel' where
  unsat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; unsat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),UNSAT_PUSH,(push_effect f e,l))\<in>algo_rel'"
| sat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; sat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),SAT_PUSH,(push_effect f e,l))\<in>algo_rel'"
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

lemma
  assumes "(fxl,p,fxl') \<in> trcl algo_rel'"
  shows "length (filter (op= SAT_PUSH) p) < card V * sum_heights_measure (snd fxl) + card_adm_measure (fst fxl) (snd fxl) + 1"
  using assms
  apply (induction rule: trcl.induct)
  apply (auto elim!: algo_rel'.cases)  
  apply (drule (1) Height_Bounded_Labeling.sat_push_measure; auto)
  apply (drule (1) Height_Bounded_Labeling.unsat_push_measure(1); auto)
  apply (drule (1) Height_Bounded_Labeling.relabel_measure_height_adm; auto)
  done
  
  end
end
