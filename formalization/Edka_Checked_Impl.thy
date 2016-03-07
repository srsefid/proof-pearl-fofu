theory Edka_Checked_Impl
imports NetCheck EdmondsKarp_Impl
begin

  definition stat_outer_c :: "unit Heap" where "stat_outer_c = return ()"
  lemma insert_stat_outer_c: "m = stat_outer_c \<guillemotright> m" unfolding stat_outer_c_def by simp
  definition stat_inner_c :: "unit Heap" where "stat_inner_c = return ()"
  lemma insert_stat_inner_c: "m = stat_inner_c \<guillemotright> m" unfolding stat_inner_c_def by simp


  code_printing
    code_module stat \<rightharpoonup> (SML) \<open>
      structure stat = struct
        val outer_c = ref 0;
        fun outer_c_incr () = (outer_c := !outer_c + 1; ())
        val inner_c = ref 0;
        fun inner_c_incr () = (inner_c := !inner_c + 1; ())
      end
      \<close>
  | constant stat_outer_c \<rightharpoonup> (SML) "stat.outer'_c'_incr"  
  | constant stat_inner_c \<rightharpoonup> (SML) "stat.inner'_c'_incr"  


  schematic_lemma [code]: "edka_imp_run_0 s t N f brk = ?foo"
    apply (subst edka_imp_run.code)
    apply (rewrite in "\<hole>" insert_stat_outer_c)
    by (rule refl)
    

  schematic_lemma [code]: "bfs_impl_0 t u l = ?foo"
    apply (subst bfs_impl.code)
    apply (rewrite in "\<hole>" insert_stat_inner_c)
    by (rule refl)

  definition "edmonds_karp el s t \<equiv> do {
    case prepareNet el s t of
      None \<Rightarrow> return None
    | Some (c,ps,N) \<Rightarrow> do {
        f \<leftarrow> edka_imp c s t N ps ;
        return (Some (N,f))
    }
  }"
  export_code edmonds_karp checking SML

  lemma network_is_impl: "Network c s t \<Longrightarrow> Network_Impl c s t" by intro_locales

  theorem edmonds_karp_correct:
    "<emp> edmonds_karp el s t <\<lambda>
        None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
      | Some (N,fi) \<Rightarrow> \<exists>\<^sub>Af. Network_Impl.is_rflow (ln_\<alpha> el) N f fi * \<up>(Network.isMaxFlow (ln_\<alpha> el) s t f)
          * \<up>(ln_invar el \<and> Network (ln_\<alpha> el) s t \<and> Graph.V (ln_\<alpha> el) \<subseteq> {0..<N})
    >\<^sub>t"
    unfolding edmonds_karp_def
    using prepareNet_correct[of el s t]
    by (sep_auto 
      split: option.splits 
      heap: Network_Impl.edka_imp_correct 
      simp: ln_rel_def br_def network_is_impl)

context
begin
private definition "is_rflow \<equiv> Network_Impl.is_rflow"

text_raw \<open>\DefineSnippet{edmonds_karp_correct}{\<close>       
theorem
  fixes el defines "c \<equiv> ln_\<alpha> el"
  shows "<emp> edmonds_karp el s t <\<lambda>
      None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network c s t)
    | Some (N,cf) \<Rightarrow> 
      \<up>(ln_invar el \<and> Network c s t \<and> Graph.V c \<subseteq> {0..<N})
    * (\<exists>\<^sub>Af. is_rflow c N f cf * \<up>(Network.isMaxFlow c s t f))>\<^sub>t"
text_raw \<open>}%EndSnippet\<close>
  unfolding c_def is_rflow_def
  by (sep_auto heap: edmonds_karp_correct[of el s t] split: option.split)

end

  (* TODO: Justify this by abstract definition + refinement *)  
  definition get_flow :: "capacity_impl graph \<Rightarrow> nat \<Rightarrow> Graph.node \<Rightarrow> capacity_impl mtx \<Rightarrow> capacity_impl Heap" where
    "get_flow c N s fi \<equiv> do {
      imp_nfoldli ([0..<N]) (\<lambda>_. return True) (\<lambda>v cap. do {
        let csv = c (s,v);
        cfsv \<leftarrow> mtx_get N fi (s,v);
        let fsv = csv - cfsv;
        return (cap + fsv)
      }) 0
    }"


  export_code nat_of_integer integer_of_nat int_of_integer integer_of_int
    edmonds_karp edka_imp edka_imp_tabulate edka_imp_run prepareNet get_flow
    in SML_imp 
    module_name Fofu 
    file "evaluation/fofu-SML/Fofu_Export.sml"  

end
