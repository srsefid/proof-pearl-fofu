section \<open>The Ford-Fulkerson Method\<close>
theory FordFulkerson_Algo
imports 
  Ford_Fulkerson
  Refine_Add_Fofu
  Refine_Monadic_Syntax_Sugar
begin
text \<open>In this theory, we formalize the abstract Ford-Fulkerson
  method, which is independent of how an augmenting path is chosen\<close>

context Network 
begin

subsection \<open>Algorithm\<close>
text \<open>
  We abstractly specify the procedure for finding an augmenting path:
  Assuming a valid flow, the procedure must return an augmenting path 
  iff there exists one.
  \<close>
definition "find_augmenting_spec f \<equiv> do {
    assert (NFlow c s t f);
    selectp p. NFlow.isAugmenting c s t f p
  }"

text \<open>
  We also specify the loop invariant, and annotate it to the loop.
\<close>
abbreviation "fofu_invar \<equiv> \<lambda>(f,brk). 
        NFlow c s t f 
      \<and> (brk \<longrightarrow> (\<forall>p. \<not>NFlow.isAugmenting c s t f p))
    "  

text \<open>Finally, we obtain the Ford-Fulkerson algorithm.
  Note that we annotate some assertions to ease later refinement\<close>
definition "fofu \<equiv> do {
  let f = (\<lambda>_. 0);

  (f,_) \<leftarrow> while\<^bsup>fofu_invar\<^esup>
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_augmenting_spec f;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> do {
          assert (p\<noteq>[]);
          assert (NFlow.isAugmenting c s t f p);
          let f' = NFlow.augmentingFlow c f p;
          let f = NFlow.augment c f f';
          assert (NFlow c s t f);
          return (f, False)
        }  
    })
    (f,False);
  assert (NFlow c s t f);
  return f 
}"

subsection \<open>Partial Correctness\<close>
text \<open>Correctness of the algorithm is a consequence from the 
  Ford-Fulkerson theorem. We need a few straightforward 
  auxiliary lemmas, though:
\<close>

text \<open>The zero flow is a valid flow\<close>
lemma zero_flow: "NFlow c s t (\<lambda>_. 0)" 
  unfolding NFlow_def Flow_def 
  using Network_axioms
  by (auto simp: s_node t_node cap_non_negative)  

text \<open>Augmentation preserves the flow property\<close>
lemma (in NFlow) augment_pres_nflow:
  assumes AUG: "isAugmenting p"
  shows "NFlow c s t (augment (augmentingFlow p))"
proof -
  note augment_flow_presv[OF augFlow_resFlow[OF AUG]]
  thus ?thesis
    by intro_locales
qed    

text \<open>Augmenting paths cannot be empty\<close>
lemma (in NFlow) augmenting_path_not_empty:
  "\<not>isAugmenting []"
  unfolding isAugmenting_def using s_not_t by auto


text \<open>Finally, we can use the verification condition generator to
  show correctness\<close>
theorem fofu_partial_correct: "fofu \<le> (spec f. isMaxFlow f)"
  unfolding fofu_def find_augmenting_spec_def
  apply (refine_vcg)
  apply (vc_solve simp: 
    zero_flow 
    NFlow.augment_pres_nflow 
    NFlow.augmenting_path_not_empty
    NFlow.noAugPath_iff_maxFlow[symmetric])
  done

subsection \<open>Algorithm without Assertions\<close>
text \<open>For presentation purposes, we extract a version of the algorithm
  without assertions, and using a bit more concise notation\<close>

(* TODO: May be a good idea for main refinement branch, too! *)
definition (in NFlow) "augment_with_path p \<equiv> augment (augmentingFlow p)"

context begin

private abbreviation (input) "augment 
  \<equiv> NFlow.augment_with_path"
private abbreviation (input) "is_augmenting_path f p 
  \<equiv> NFlow.isAugmenting c s t f p"

text \<open> {} \<close>
text_raw \<open>\DefineSnippet{ford_fulkerson_algo}{\<close>       
definition "ford_fulkerson_method \<equiv> do {
  let f = (\<lambda>(u,v). 0);

  (f,brk) \<leftarrow> while (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,brk). do {
      p \<leftarrow> selectp p. is_augmenting_path f p;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> return (augment c f p, False)
    })
    (f,False);
  return f 
}"
text_raw \<open>}%EndSnippet\<close>

text \<open> {} \<close>

end -- \<open>Anonymous context\<close> 
end -- \<open>Network\<close> 

text \<open> {} \<close>
text_raw \<open>\DefineSnippet{ford_fulkerson_correct}{\<close>       
theorem (in Network) "ford_fulkerson_method \<le> (spec f. isMaxFlow f)"
text_raw \<open>}%EndSnippet\<close>
text \<open> {} \<close>
proof -
  have [simp]: "(\<lambda>(u,v). 0) = (\<lambda>_. 0)" by auto
  have "ford_fulkerson_method \<le> fofu"
    unfolding ford_fulkerson_method_def fofu_def Let_def find_augmenting_spec_def
    apply (rule refine_IdD)
    apply (refine_vcg)
    apply (refine_dref_type)
    apply (vc_solve simp: NFlow.augment_with_path_def)
    done
  also note fofu_partial_correct  
  finally show ?thesis .
qed  

end -- \<open>Theory\<close>
