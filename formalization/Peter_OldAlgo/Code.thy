theory Code
imports NetCheck EdmondsKarp_Impl "~~/src/HOL/Library/Rewrite"
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


  schematic_lemma [code]: "edka_imp N ps c s t = ?foo"
    unfolding edka_imp_def
    apply (rewrite in "heap_WHILET _ \<hole> _" insert_stat_outer_c)
    by (rule refl)
    

  schematic_lemma [code]: "bfs_impl N c s t = ?foo"
    unfolding bfs_impl_def
    apply (rewrite in "imp_nfoldli _ _ \<hole> _" insert_stat_inner_c)
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

  theorem edmonds_karp_correct:
    "<emp> edmonds_karp el s t <\<lambda>
        None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
      | Some (N,fi) \<Rightarrow> \<exists>\<^sub>Af. Network.is_rflow (ln_\<alpha> el) N f fi * \<up>(isMaxFlow (ln_\<alpha> el) s t f)
          * \<up>(ln_invar el \<and> Network (ln_\<alpha> el) s t \<and> Graph.V (ln_\<alpha> el) \<subseteq> {0..<N})
    >\<^sub>t"
    unfolding edmonds_karp_def
    using prepareNet_correct[of el s t]
    by (sep_auto split: option.splits heap: Network.edka_imp_correct simp: ln_rel_def br_def)


  (* TODO: Justify this by abstract definition + refinement *)  
  definition get_flow :: "graph \<Rightarrow> nat \<Rightarrow> Graph.node \<Rightarrow> capacity mtx \<Rightarrow> capacity Heap" where
    "get_flow c N s fi \<equiv> do {
      imp_nfoldli ([0..<N]) (\<lambda>_. return True) (\<lambda>v cap. do {
        let csv = c (s,v);
        cfsv \<leftarrow> mtx_get N fi (s,v);
        let fsv = csv - cfsv;
        return (cap + fsv)
      }) 0
    }"


  export_code nat_of_integer integer_of_nat 
    edmonds_karp edka_imp prepareNet get_flow
    in SML_imp 
    module_name Fofu 
    file "evaluation/fofu-SML/Fofu_Export.sml"  

end
