section \<open>Code Generation for Benchmarks\<close>
theory Prpu_Benchmark_Export
imports Relabel_To_Front_Impl2 Fifo_Push_Relabel_Impl2
begin


subsection \<open>Adding Statistic Counters\<close>
text \<open>We first add some statistic counters, that we use for profiling\<close>
definition stat_gap_c :: "unit Heap" where "stat_gap_c = return ()"
lemma insert_stat_gap_c: "m = stat_gap_c \<then> m" 
  unfolding stat_gap_c_def by simp
definition stat_push_c :: "unit Heap" where "stat_push_c = return ()"
lemma insert_stat_push_c: "m = stat_push_c \<then> m" 
  unfolding stat_push_c_def by simp
definition stat_relabel_c :: "unit Heap" where "stat_relabel_c = return ()"
lemma insert_stat_relabel_c: "m = stat_relabel_c \<then> m" 
  unfolding stat_relabel_c_def by simp

code_printing
  code_module stat \<rightharpoonup> (SML) \<open>
    structure stat = struct
      val gap_c = ref 0;
      fun gap_c_incr () = (gap_c := !gap_c + 1; ())
      val push_c = ref 0;
      fun push_c_incr () = (push_c := !push_c + 1; ())
      val relabel_c = ref 0;
      fun relabel_c_incr () = (relabel_c := !relabel_c + 1; ())
    end
    \<close>
| constant stat_gap_c \<rightharpoonup> (SML) "stat.gap'_c'_incr"  
| constant stat_push_c \<rightharpoonup> (SML) "stat.push'_c'_incr"  
| constant stat_relabel_c \<rightharpoonup> (SML) "stat.relabel'_c'_incr"  
  
term CNV  
thm gap_impl_def  
schematic_goal [code]: "gap_impl = ?x" 
  apply (rule CNV_eqD)
  unfolding gap_impl_def
  apply (rewrite insert_stat_gap_c)
  by (rule CNV_I)
  
schematic_goal [code]: "fifo_push_impl = ?x" 
  apply (rule CNV_eqD)
  unfolding fifo_push_impl_def
  apply (rewrite insert_stat_push_c)
  by (rule CNV_I)

schematic_goal [code]: "relabel_impl = ?x" 
  apply (rule CNV_eqD)
  unfolding relabel_impl_def
  apply (rewrite insert_stat_relabel_c)
  by (rule CNV_I)
    
subsection \<open>Code Export\<close>    
export_code 
  nat_of_integer integer_of_nat int_of_integer integer_of_int
  
  prepareNet 
  
  (*relabel_to_front_impl relabel_to_front_impl_tab_am*)
  
  fifo_push_relabel fifo_push_relabel_prepare_impl fifo_push_relabel_run_impl
  
  compute_flow_val_impl
  in SML_imp 
  module_name Prpu
  file "../evaluation/prpu-SML/Prpu_Export.sml"  
  
  
end
