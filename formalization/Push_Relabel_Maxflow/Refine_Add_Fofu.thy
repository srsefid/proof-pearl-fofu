theory Refine_Add_Fofu
imports Fofu_Impl_Base Refine_Monadic_Syntax_Sugar
  "$AFP/DFS_Framework/Misc/DFS_Framework_Refine_Aux"
begin

(* TODO: Move to Misc *)  
lemma swap_in_iff_inv: "prod.swap p \<in> S \<longleftrightarrow> p \<in> S\<inverse>"
  apply (cases p) by auto
  
    
    
  notation Heap_Monad.return ("return")

  (* TODO: Move to Refine_Basic convenience *)  

  lemma strengthen_SPEC': "m \<le> SPEC \<Phi> \<Longrightarrow> m \<le> SPEC(\<lambda>s. inres m s \<and> nofail m \<and> \<Phi> s)"
    -- "Strengthen SPEC by adding trivial upper bound for result"
    by (auto simp: pw_le_iff refine_pw_simps)

lemma (in -) refine2spec_aux:
  "a \<le> \<Down>R b \<longleftrightarrow> ( (nofail b \<longrightarrow> a \<le> SPEC ( \<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )) )"
  by (auto simp: pw_le_iff refine_pw_simps)
  
lemma (in -) refine2specI:
  assumes "nofail b \<Longrightarrow> a \<le> SPEC (\<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )"
  shows "a \<le> \<Down>R b"  
  using assms by (simp add: refine2spec_aux)  
  


(* Refinement Framework VCG control:
  Idea: Put a frame around stuff in the program where the VCG shall not look into
    on outermost pass, and discharge the frame's content with nested vcg call.
    Very useful with subgoal command, to set up some auxiliary context before
    discharging, e.g., interpret locales, etc.
 
*)  
(* TODO: Make this a generic technique:
  Problems: 
    * Splitter will split inside VCG_FRAME (e.g., ifs)

*)  
  
definition VCG_FRAME :: "_ nres \<Rightarrow> _ nres" where "VCG_FRAME m \<equiv> m"
lemma VCG_FRAME_cong[cong]: "VCG_FRAME x \<equiv> VCG_FRAME x" by simp

lemma vcg_intro_frame: "m \<equiv> VCG_FRAME m" unfolding VCG_FRAME_def by simp
lemma vcg_rem_frame: "m\<le>m' \<Longrightarrow> VCG_FRAME m \<le> m'" unfolding VCG_FRAME_def by simp
  
  
  
      
      

  (* TODO: Integrate into Refinement Framework! *)

  lemma LFO_pre_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "(ci,c)\<in>R \<rightarrow> bool_rel"
    assumes "(fi,f)\<in>A\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nres_rel"
    assumes "(s0i,s0)\<in>R"
    shows "LIST_FOREACH' (RETURN li) ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0)"
  proof -
    from assms(1) have [simp]: "finite l" by (auto simp: list_set_rel_def br_def)
    show ?thesis
      unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH
      apply simp
      apply (rule LIST_FOREACH_autoref[param_fo, THEN nres_relD])
      using assms
      apply auto
      apply (auto simp: it_to_sorted_list_def nres_rel_def pw_le_iff refine_pw_simps
        list_set_rel_def br_def)
      done
  qed    
      

  lemma LFOci_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0)"
  proof -
    from assms LFO_pre_refine[of li l A ci c R fi f s0i s0] show ?thesis
      unfolding fun_rel_def nres_rel_def LIST_FOREACH'_def
      apply (simp add: pw_le_iff refine_pw_simps)
      apply blast+
      done
  qed    

  lemma LFOc_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHc l c f s0)"
    unfolding FOREACHc_def
    by (rule LFOci_refine[OF assms])

    
  lemma LFO_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACH l f s0)"
    unfolding FOREACH_def
    apply (rule LFOc_refine)
    apply (rule assms | simp)+
    done

  lemma LFOi_refine: (* TODO: Move and generalize! *)
    assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
    assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
    assumes "(s0i,s0)\<in>R"
    shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACHi I l f s0)"
    unfolding FOREACHi_def
    apply (rule LFOci_refine)
    apply (rule assms | simp)+
    done

  (* TODO: Move to refinement framework. Combine with select from CAVA-Base. *)
  definition "SELECTp P \<equiv> if Ex P then RES {Some x | x. P x} else RETURN None"

  lemma selectp_rule[refine_vcg]: 
    assumes "\<forall>x. \<not>P x \<Longrightarrow> RETURN None \<le> SPEC \<Phi>"
    assumes "\<And>x. P x \<Longrightarrow> RETURN (Some x) \<le> SPEC \<Phi>"
    shows "SELECTp P \<le> SPEC \<Phi>"
    using assms unfolding SELECTp_def
    by (auto)

  lemma selectp_refine_eq:
    "SELECTp P \<le> \<Down>(\<langle>R\<rangle>option_rel) (SELECTp Q) \<longleftrightarrow> 
    (\<forall>x. P x \<longrightarrow> (\<exists>y. (x,y)\<in>R \<and> Q y)) \<and> ((\<forall>x. \<not>P x) \<longrightarrow> (\<forall>y. \<not>Q y))"
    by (auto simp: SELECTp_def option_rel_def
      simp: pw_le_iff refine_pw_simps)

  lemma selectp_refine[refine]:
    assumes "SPEC P \<le>\<Down>R (SPEC Q)"  
    assumes "\<And>y. \<forall>x. \<not>P x \<Longrightarrow> \<not>Q y"
    shows "SELECTp P \<le> \<Down>(\<langle>R\<rangle>option_rel) (SELECTp Q)"
    unfolding selectp_refine_eq
    using assms by (auto simp: pw_le_iff refine_pw_simps)

  lemma selectp_refine_Id[refine]:  
    assumes "\<And>x. P x \<Longrightarrow> Q x"
    assumes "\<And>y. \<forall>x. \<not>P x \<Longrightarrow> \<not>Q y"
    shows "SELECTp P \<le> \<Down>Id (SELECTp Q)"
    using selectp_refine[where R=Id, of P Q] assms by auto
    
  lemma selectp_pw[refine_pw_simps]:
    "nofail (SELECTp P)"  
    "inres (SELECTp P) r \<longleftrightarrow> (r=None \<longrightarrow> (\<forall>x. \<not>P x)) \<and> (\<forall>x. r=Some x \<longrightarrow> P x)"
    unfolding SELECTp_def
    by auto

  lemma selectp_pw_simps[simp]:
    "nofail (SELECTp P)"
    "inres (SELECTp P) None \<longleftrightarrow> (\<forall>x. \<not>P x)"
    "inres (SELECTp P) (Some x) \<longleftrightarrow> P x"
    by (auto simp: refine_pw_simps)

  context Refine_Monadic_Syntax begin 
    notation SELECTp (binder "selectp " 10)

    term "selectp x. P x"
  end


definition setsum_impl :: "('a \<Rightarrow> 'b::comm_monoid_add nres) \<Rightarrow> 'a set \<Rightarrow> 'b nres" where
  "setsum_impl g S \<equiv> foreach S (\<lambda>x a. do { b \<leftarrow> g x; return (a+b)}) 0"

lemma setsum_imp_correct: 
  assumes [simp]: "finite S"
  assumes [THEN order_trans, refine_vcg]: "\<And>x. x\<in>S \<Longrightarrow> gi x \<le> (spec r. r=g x)"
  shows "setsum_impl gi S \<le> (spec r. r=sum g S)"
  unfolding setsum_impl_def
  apply (refine_vcg FOREACH_rule[where I="\<lambda>it a. a = sum g (S - it)"])
  apply (auto simp: it_step_insert_iff algebra_simps)
  done


  lemma int_of_integer_less_iff: "int_of_integer x < int_of_integer y \<longleftrightarrow> x<y"
    by (simp add: less_integer_def)

  lemma nat_of_integer_less_iff: "x\<ge>0 \<Longrightarrow> y\<ge>0 \<Longrightarrow> nat_of_integer x < nat_of_integer y \<longleftrightarrow> x<y"
    unfolding nat_of_integer.rep_eq
    by (auto simp: int_of_integer_less_iff nat_less_eq_zless int_of_integer_less_iff[of 0, simplified])
    
      
(* TODO: Move *)  
  
lemma uminus_hnr[sepref_import_param]: "(uminus,uminus)\<in>int_rel \<rightarrow> int_rel" by auto  
  
  (* TODO: Move *)  
  lemma (in -) rev_append_hnr[param,sepref_import_param]:
    "(rev_append, rev_append) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
    unfolding rev_append_def by parametricity
    
      
(* TODO: Move. Allow monadic_nfoldli to be used in abstract programs *)      
(* Refinement Setup for nfoldli  *)
lemma monadic_nfoldli_arities[sepref_monadify_arity]:
  "monadic_nfoldli \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (monadic_nfoldli)$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma monadic_nfoldli_comb[sepref_monadify_comb]:
  "\<And>s c f \<sigma>. (monadic_nfoldli)$s$c$f$\<sigma> \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. Refine_Basic.bind$(EVAL$\<sigma>)$(\<lambda>\<^sub>2\<sigma>. 
      SP (monadic_nfoldli)$s$c$f$\<sigma>
    ))"
  by (simp_all)
      

end
