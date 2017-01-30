theory Preflow_Complexity_Test
imports Preflow
begin
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
  oops    
    
    


  end
end
