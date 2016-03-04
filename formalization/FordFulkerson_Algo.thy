section \<open>The Ford-Fulkerson Method\<close>
theory FordFulkerson_Algo
imports 
  Ford_Fulkerson
  Refine_Add_Fofu
  Refine_Monadic_Syntax_Sugar
begin
  text \<open>In this theory, we formalize the abstract Ford-Fulkerson
    method, which is independent of how an augmenting flow is chosen
    \<close>

  context Network 
  begin
    
    text \<open>
      We abstractly specify the procedure for finding an augmenting path:
      Assuming a valid flow, the procedure must return an augmenting path 
      iff there exists one.
      \<close>
    definition "find_augmenting_spec f \<equiv> ASSERT (NFlow c s t f) \<guillemotright> 
      SPEC (\<lambda> Some p \<Rightarrow> NFlow.isAugmenting c s t f p 
            | None \<Rightarrow> \<forall>p. \<not>NFlow.isAugmenting c s t f p)"

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

      (f,_) \<leftarrow> WHILEI fofu_invar
        (\<lambda>(f,brk). \<not>brk) 
        (\<lambda>(f,_). do {
          p \<leftarrow> find_augmenting_spec f;
          case p of 
            None \<Rightarrow> RETURN (f,True)
          | Some p \<Rightarrow> do {
              ASSERT (p\<noteq>[]);
              ASSERT (NFlow.isAugmenting c s t f p);
              let f' = NFlow.augmentingFlow c f p;
              let f = NFlow.augment c f f';
              ASSERT (NFlow c s t f);
              RETURN (f, False)
            }  
        })
        (f,False);
      ASSERT (NFlow c s t f);
      RETURN f 
    }"

    text \<open>Augmentation preserves the flow property\<close>
    lemma (in NFlow) augment_pres_nflow:
      assumes AUG: "isAugmenting p"
      shows "NFlow c s t (augment (augmentingFlow p))"
    proof -
      note augment_flow_presv[OF augFlow_resFlow[OF AUG]]
      thus ?thesis
        by intro_locales
    qed    

    lemma int_of_integer_less_iff: "int_of_integer x < int_of_integer y \<longleftrightarrow> x<y"
      by (simp add: less_integer_def)

    lemma nat_of_integer_less_iff: "x\<ge>0 \<Longrightarrow> y\<ge>0 \<Longrightarrow> nat_of_integer x < nat_of_integer y \<longleftrightarrow> x<y"
      unfolding nat_of_integer.rep_eq
      by (auto simp: int_of_integer_less_iff nat_less_eq_zless int_of_integer_less_iff[of 0, simplified])
      
      
      


    text \<open>Correctness of the algorithm is a consequence from the 
      Ford-Fulkerson theorem. Note that we use the verification 
      condition generator of the refinement framework, and then discharge
      the non-obvious verification conditions explicitly.

      Moreover note, that we show total correctness here. 
      As our capacities are natural numbers, the algorithm always terminates.
      \<close>
    lemma fofu_partial_correct: "fofu \<le> SPEC (\<lambda>f. isMaxFlow c s t f)"
      unfolding fofu_def find_augmenting_spec_def
      apply (refine_vcg)
      apply clarsimp_all
    proof -
      show "NFlow c s t (\<lambda>_. 0)" unfolding NFlow_def Flow_def 
        using Network_axioms
        by (auto simp: s_node t_node cap_positive)  
        
      (*  
      txt \<open>Note: Exploiting integer capacities. For irrational numbers, the 
        general Ford-Fulkerson scheme needs not terminate.\<close>  
      let ?S = "measure (\<lambda>f. nat ((\<Sum>e\<in> outgoing s. c e) - Flow.val c s f)) <*lex*> measure (\<lambda>True \<Rightarrow> 0 | False \<Rightarrow> 1)"
      show "wf ?S" by auto
      *)

      {
        fix f p
        assume asm1: "NFlow c s t f"
        assume asm2: "NFlow.isAugmenting c s t f p"
        let ?F'' = "NFlow.augment c f (NFlow.augmentingFlow c f p)"
        from NFlow.augment_pres_nflow[OF asm1 asm2] show "NFlow c s t ?F''" .
        then interpret F''!: NFlow c s t ?F'' .

        (*{
          {
            have "Graph.isPath (residualGraph c f) s p t" 
              using asm2 unfolding NFlow.isAugmenting_def[OF asm1] Graph.isSimplePath_def by auto
            then have "0 < NFlow.bottleNeck c f p" using NFlow.bottleNeck_gzero[OF asm1] by auto
            then have "Flow.val (residualGraph c f) s (NFlow.augmentingFlow c f p) > 0"
              using NFlow.augFlow_val[OF asm1 asm2] by auto
            then have "Flow.val c s ?F'' > Flow.val c s f" using asm2 
              NFlow.augment_flow_value[OF asm1 NFlow.augFlow_resFlow[OF asm1]] by auto
          } 
          moreover 
          { 
            have "outgoing s \<subseteq> E" unfolding outgoing_def by auto
            then have "finite (outgoing s)" using finite_subset[OF _ finite_E] by auto
            moreover have "\<And>e. e \<in> outgoing s \<Longrightarrow> ?F'' e \<le> c e" using F''.capacity_const by auto
            ultimately have "(\<Sum>e \<in> outgoing s. ?F'' e) \<le> (\<Sum>e \<in> outgoing s. c e)"
              using setsum_mono by blast
            then have "F''.val \<le> (\<Sum>e \<in> outgoing s. c e)" using F''.val_alt by auto
          }
          ultimately show "((NFlow.augment c f
             (NFlow.augmentingFlow c f p), False),
            (f,False)) \<in> ?S"
            by (simp)
        }*)
      }
      {
        fix f
        assume asm1: "NFlow c s t f"
        assume asm2: "(\<forall>p. \<not>NFlow.isAugmenting c s t f p)"
        show "isMaxFlow c s t f" using NFlow.maxFlow_iff_noAugPath[OF asm1] asm2 by blast
      }
      (*{ fix f
        show "((f, True), f, False) \<in> ?S" by auto
      } *) 

      {
        fix f
        assume "NFlow c s t f" then interpret NFlow c s t f .
        
        assume "isAugmenting []"
        thus False unfolding isAugmenting_def Graph.isSimplePath_def
          using s_not_t
          by (simp add: Graph.isPath.simps)

      }
    qed   

    (* TODO: May be a good idea for main refinement branch, too! *)
    definition (in NFlow) "augment_with_path p \<equiv> augment (augmentingFlow p)"

    context begin interpretation Refine_Monadic_Syntax .

      private abbreviation "augment \<equiv> NFlow.augment_with_path"

      text \<open>A polished version for presentation\<close>
(* FIXME: Indentation unfortunate, but required to extract snippet for latex presentation *)    
text_raw \<open>\DefineSnippet{ford_fulkerson_algo}{\<close>       
definition "ford_fulkerson_algo \<equiv> do {
  let f = (\<lambda>_. 0);

  (f,_) \<leftarrow> while
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_augmenting_spec f;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> return (augment c f p, False)
    })
    (f,False);
  return f 
}"
text_raw \<open>}%EndSnippet\<close>

      theorem "ford_fulkerson_algo \<le> (spec f. isMaxFlow c s t f)"
      proof -
        have "ford_fulkerson_algo \<le> fofu"
          unfolding ford_fulkerson_algo_def fofu_def Let_def
          apply (rule refine_IdD)
          apply (refine_rcg)
          apply (refine_dref_type)
          apply (vc_solve simp: NFlow.augment_with_path_def)
          done
        also note fofu_partial_correct  
        finally show ?thesis .
      qed  
    end  

  end
end
