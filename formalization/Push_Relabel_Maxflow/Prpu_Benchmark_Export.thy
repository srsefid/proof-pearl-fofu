theory Prpu_Benchmark_Export
imports Preflow_Push_Impl
begin

  (*TODO: Reapeted from old code, Cleanup*)
 subsection \<open>Adding Statistic Counters\<close>
text \<open>We first add some statistic counters, that we use for profiling\<close>
definition stat_outer_c :: "unit Heap" where "stat_outer_c = return ()"
lemma insert_stat_outer_c: "m = stat_outer_c \<then> m" 
  unfolding stat_outer_c_def by simp
definition stat_inner_c :: "unit Heap" where "stat_inner_c = return ()"
lemma insert_stat_inner_c: "m = stat_inner_c \<then> m" 
  unfolding stat_inner_c_def by simp

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
  
  (**)
  export_code nat_of_integer integer_of_nat int_of_integer integer_of_int
  prepareNet 
  (*relabel_to_front_impl*) relabel_to_front_impl_tab_am fifo_push_relabel
  in SML_imp 
  module_name Prpu
  file "evaluation/prpu-SML/Prpu_Export.sml"  

  
end
