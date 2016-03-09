theory Refine_Add_Fofu
imports Fofu_Impl_Base Refine_Monadic_Syntax_Sugar
begin

  notation Heap_Monad.return ("return")



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

  

(* TODO: Move! *)
(* TODO: We do not really need the lower-bound for D in most cases.
  So let the default rules be without lower bound *)
lemma REC_rule_arb':
  fixes x::"'x" and arb::'arb
  assumes M: "trimono body"
  assumes I0: "pre arb x"
  assumes IS: "\<And>f arb x. \<lbrakk>
    \<And>arb' x. pre arb' x \<Longrightarrow> f x \<le> M arb' x; pre arb x
  \<rbrakk> \<Longrightarrow> body f x \<le> M arb x"
  shows "REC body x \<le> M arb x"
  apply (rule REC_rule_arb[where M=M and pre=pre])
  apply fact
  apply fact
  apply (rule IS)
  apply assumption+
  done

lemma RECT_rule_arb':
  fixes x::"'x" and arb::'arb
  assumes "trimono body"
    and "wf V"
    and "pre arb x"
    and
    IS: "\<And>f arb x.
        \<lbrakk>\<And>arb' x'. \<lbrakk>pre arb' x'; (x', x) \<in> V\<rbrakk> \<Longrightarrow> f x' \<le> M arb' x'; pre arb x;
         f \<le> REC\<^sub>T body\<rbrakk>
        \<Longrightarrow> body f x \<le> M arb x"
  shows "REC\<^sub>T body x \<le> M arb x"
  apply (rule RECT_rule_arb[where M=M and pre=pre])
  apply fact
  apply fact
  apply fact
  apply (rule IS)
  apply assumption+
  apply simp
  done

  (* TODO: Move to refinement framework. Combine with select from CAVA-Base. *)
  definition "SELECTp \<equiv> select o Collect"

  lemma selectp_rule[refine_vcg]: 
    assumes "\<forall>x. \<not>P x \<Longrightarrow> RETURN None \<le> SPEC \<Phi>"
    assumes "\<And>x. P x \<Longrightarrow> RETURN (Some x) \<le> SPEC \<Phi>"
    shows "SELECTp P \<le> SPEC \<Phi>"
    using assms unfolding SELECTp_def select_def[abs_def]
    by (auto)

  lemma selectp_refine_eq:
    "SELECTp P \<le> \<Down>(\<langle>R\<rangle>option_rel) (SELECTp Q) \<longleftrightarrow> 
    (\<forall>x. P x \<longrightarrow> (\<exists>y. (x,y)\<in>R \<and> Q y)) \<and> ((\<forall>x. \<not>P x) \<longrightarrow> (\<forall>y. \<not>Q y))"
    by (auto simp: SELECTp_def select_def option_rel_def
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
    unfolding SELECTp_def select_def[abs_def]
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

  (* TODO: Move to refinement framework! *)
  lemma WHILEIT_less_WHILEI:
    assumes "wf V"
    assumes VAR: "\<And>s. \<lbrakk> I s; b s; f s \<le> SPEC I \<rbrakk> \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. (s',s)\<in>V)"
    shows "WHILEIT I b f s \<le> WHILEI I b f s"
    using \<open>wf V\<close>
    apply (induction s rule: wf_induct[consumes 1])
    apply (subst WHILEIT_unfold) 
    apply (subst WHILEI_unfold)
  proof (clarsimp)
    fix x
    assume A: "I x" "b x"
    assume IH: "\<forall>y. (y, x) \<in> V \<longrightarrow> WHILE\<^sub>T\<^bsup>I\<^esup> b f y \<le> WHILE\<^bsup>I\<^esup> b f y"

    show "f x \<guillemotright>= WHILE\<^sub>T\<^bsup>I\<^esup> b f \<le> f x \<guillemotright>= WHILE\<^bsup>I\<^esup> b f"
    proof cases
      assume B: "f x \<le> SPEC I"
      show "?thesis"
        apply (rule Refine_Basic.bind_mono(1)[OF order_refl])
        using IH VAR[OF A B]
        by (auto simp: pw_le_iff)
    next
      assume B: "\<not>(f x \<le> SPEC I)"
      hence "f x \<guillemotright>= WHILE\<^bsup>I\<^esup> b f = FAIL"
        apply (subst WHILEI_unfold[abs_def])
        apply (auto simp: pw_eq_iff pw_le_iff refine_pw_simps)
        done
      thus ?thesis by simp  
    qed
  qed

  lemmas WHILEIT_refine_WHILEI = order_trans[OF WHILEIT_less_WHILEI WHILEI_refine]

  (* TODO: Move to refinement framework! *)
  lemma bind_sim_select_rule:
    assumes "m\<guillemotright>=f' \<le> SPEC \<Psi>"
    assumes "\<And>x. \<lbrakk>nofail m; inres m x; f' x\<le>SPEC \<Psi>\<rbrakk> \<Longrightarrow> f x\<le>SPEC \<Phi>"
    shows "m\<guillemotright>=f \<le> SPEC \<Phi>"
    -- \<open>Simultaneously select a result from assumption and verification goal.
      Useful to work with assumptions that restrict the current program to 
      be verified, as, e.g., introduced by @{thm [source] WHILEIT_less_WHILEI}.\<close>
    using assms 
    by (auto simp: pw_le_iff refine_pw_simps)

  (* TODO: Move to refinement framework! *)
  lemma assert_bind_spec_conv: "ASSERT \<Phi> \<guillemotright> m \<le> SPEC \<Psi> \<longleftrightarrow> (\<Phi> \<and> m \<le> SPEC \<Psi>)"  
    -- \<open>Simplify a bind-assert verification condition. 
      Useful if this occurs in the assumptions, and considerably faster than 
      using pointwise reasoning, which may causes a blowup for many chained 
      assertions.\<close>
    by (auto simp: pw_le_iff refine_pw_simps)



    (* TODO: Move *)
    lemma (in -) fold_partial_uncurry: "uncurry (\<lambda>(ps, cf). f ps cf) = uncurry2 f" by auto



    (* TODO: Move. Should this replace hn_refine_cons? *)
    lemma (in -) hn_refine_cons':
      assumes I: "P\<Longrightarrow>\<^sub>AP'"
      assumes R: "hn_refine P' c Q R m"
      assumes I': "Q\<Longrightarrow>\<^sub>AQ'*true"
      assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>A R' x y"
      shows "hn_refine P c Q' R' m"
      using R unfolding hn_refine_def
      apply clarsimp
      apply (rule cons_pre_rule[OF I])
      apply (erule cons_post_rule)
      apply sep_auto
      by (simp add: I' R' assn_aci(10) ent_star_mono ent_true_drop(1))
      
    (* TODO: Move *)  
    lemma param_prod_swap[param]: "(prod.swap, prod.swap)\<in>A\<times>\<^sub>rB \<rightarrow> B\<times>\<^sub>rA" by auto
    lemmas [sepref_import_param] = param_prod_swap
    

(* Refinement Setup for nfoldli \<rightarrow> move to Sepref-Foreach *)
lemma nfoldli_arities[sepref_monadify_arity]:
  "nfoldli \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (nfoldli)$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma nfoldli_comb[sepref_monadify_comb]:
  "\<And>s c f \<sigma>. (nfoldli)$s$(\<lambda>\<^sub>2x. c x)$f$\<sigma> \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. Refine_Basic.bind$(EVAL$\<sigma>)$(\<lambda>\<^sub>2\<sigma>. 
      SP (monadic_nfoldli)$s$(\<lambda>\<^sub>2x. (EVAL$(c x)))$f$\<sigma>
    ))"
  by (simp_all add: nfoldli_to_monadic)

text {* Setup for linearity analysis. *}
lemma monadic_nfoldli_skel[sepref_la_skel]:
  "\<And>s c f \<sigma>. SKEL (monadic_nfoldli$s$c$f$\<sigma>) = 
    la_seq 
      (la_op (s,\<sigma>)) 
      (la_rec (\<lambda>D. la_seq (SKEL c) (la_seq (SKEL f) (la_rcall D)))
      )" by simp


lemma monadic_nfoldli_refine_aux':
  assumes c_ref: "\<And>s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s) 
    (c s) 
    (\<Gamma> * hn_ctxt Rs s' s) 
    (pure bool_rel)
    (c' s')"
  assumes f_ref: "\<And>x x' s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rl x' x * hn_ctxt Rs s' s)
    (f x s)
    (\<Gamma> * hn_ctxt Rl x' x * hn_invalid s' s) Rs
    (f' x' s')"

  shows "hn_refine 
    (\<Gamma> * hn_list Rl l' l * hn_ctxt Rs s' s) 
    (imp_nfoldli l c f s) 
    (\<Gamma> * hn_list Rl l' l * hn_invalid s' s) Rs
    (monadic_nfoldli l' c' f' s')"

  apply (induct p\<equiv>Rl l' l 
    arbitrary: s s'
    rule: hn_list_aux.induct)

  apply simp
  apply (rule hn_refine_cons_post)
  apply (rule hn_refine_frame[OF hnr_RETURN_pass])
  apply (tactic {* Sepref_Frame.frame_tac @{context} 1 *})
  apply (simp add: hn_ctxt_def ent_true_drop)

  apply (simp only: imp_nfoldli_simps monadic_nfoldli_simp)
  apply (rule hnr_bind)
  apply (rule hn_refine_frame[OF c_ref])
  apply (tactic {* Sepref_Frame.frame_tac @{context} 1 *})

  apply (rule hnr_If)
  apply (tactic {* Sepref_Frame.frame_tac @{context} 1 *})
  apply (rule hnr_bind)
  apply (rule hn_refine_frame[OF f_ref])
  apply (simp add: assn_aci)
  apply (fr_rot_rhs 1)
  apply (fr_rot 2)
  apply (rule fr_refl)
  apply (rule fr_refl)
  apply (rule fr_refl)
  apply (rule ent_refl)

  apply (rule hn_refine_frame)
  apply rprems

  apply (simp add: assn_aci)
  apply (fr_rot_rhs 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
  apply (rule ent_refl | rule fr_refl | fr_rot 1)
 
  apply (tactic {* Sepref_Frame.frame_tac @{context} 1 *})

  apply (rule hn_refine_frame[OF hnr_RETURN_pass])
  apply (tactic {* Sepref_Frame.frame_tac @{context} 1 *})

  apply (simp add: assn_assoc)
  apply (tactic {* Sepref_Frame.merge_tac @{context} 1 *})
  apply (simp only: sup.idem, rule ent_refl)
  apply simp
  apply solve_entails
  apply (rule, sep_auto)
  apply (rule, sep_auto)
  done



lemma hn_monadic_nfoldli_rl'[sepref_comb_rules]:
  assumes "INDEP Rk" "INDEP R\<sigma>"
  assumes FR: "P \<Longrightarrow>\<^sub>A \<Gamma> * hn_list Rk s' s * hn_ctxt R\<sigma> \<sigma>' \<sigma>"
  assumes c_ref: "\<And>\<sigma> \<sigma>'. hn_refine 
    (\<Gamma> * hn_ctxt R\<sigma> \<sigma>' \<sigma>) 
    (c \<sigma>) 
    (\<Gamma>c \<sigma>' \<sigma>) 
    (pure bool_rel) 
    (c' \<sigma>')"
  assumes C_FR: 
    "\<And>\<sigma>' \<sigma>. TERM monadic_nfoldli \<Longrightarrow> 
      \<Gamma>c \<sigma>' \<sigma> \<Longrightarrow>\<^sub>A \<Gamma> * hn_ctxt R\<sigma> \<sigma>' \<sigma>"

  assumes f_ref: "\<And>x' x \<sigma>' \<sigma>. hn_refine 
    (\<Gamma> * hn_ctxt Rk x' x * hn_ctxt R\<sigma> \<sigma>' \<sigma>)
    (f x \<sigma>)
    (\<Gamma>f x' x \<sigma>' \<sigma>) R\<sigma>
    (f' x' \<sigma>')"
  assumes F_FR: "\<And>x' x \<sigma>' \<sigma>. TERM monadic_nfoldli \<Longrightarrow> \<Gamma>f x' x \<sigma>' \<sigma> \<Longrightarrow>\<^sub>A 
    \<Gamma> * hn_ctxt Rk x' x * hn_ctxt Pf\<sigma> \<sigma>' \<sigma>"

  shows "hn_refine 
    P 
    (imp_nfoldli s c f \<sigma>) 
    (\<Gamma> * hn_list Rk s' s * hn_invalid \<sigma>' \<sigma>)
    R\<sigma>
    ((monadic_nfoldli)
      $(LIN_ANNOT s' a)$(\<lambda>\<^sub>2\<sigma>'. c' \<sigma>')$(\<lambda>\<^sub>2x' \<sigma>'. f' x' \<sigma>')$(\<sigma>'\<^sup>L)
    )"
  unfolding APP_def PROTECT2_def LIN_ANNOT_def PR_CONST_def
  apply (rule hn_refine_cons_pre[OF FR])
  apply (rule hn_refine_cons[rotated])
  apply (rule monadic_nfoldli_refine_aux')
  apply (rule hn_refine_cons_post)
  apply (rule c_ref)
  apply (rule ent_trans[OF C_FR[OF TERMI]])
  apply (rule ent_refl)

  apply (rule hn_refine_cons_post)
  apply (rule f_ref)
  apply (rule ent_trans[OF F_FR[OF TERMI]])
  apply (tactic {* Sepref_Frame.frame_tac @{context} 1*})
  apply (rule ent_refl)
  apply (rule ent_refl)
  apply (rule ent_refl)
  done


  (* TODO: Move *)
  lemma lsr_finite[simp, intro]: "(l,s)\<in>\<langle>R\<rangle>list_set_rel \<Longrightarrow> finite s"
    by (auto simp: list_set_rel_def br_def)



  (* TODO: Move *)
  definition [simp]: "op_empty_ls \<equiv> {}"
  sepref_register op_empty_ls
  lemmas [sepref_import_param] = list_set_autoref_empty[folded op_empty_ls_def]

  thm list_set_autoref_insert[sepref_import_param, to_hfref, to_hnr]

  definition ls_ins_dj_imp :: "_\<Rightarrow>_\<Rightarrow>_ Heap" where [sepref_opt_simps]: "ls_ins_dj_imp x l \<equiv> return (x#l)"
  definition [simp]: "op_set_ins_dj \<equiv> Set.insert"

  lemma ls_ins_dj_rule[sepref_fr_rules]: 
    "(uncurry (ls_ins_dj_imp), uncurry (RETURN oo Set.insert)) 
      \<in> [\<lambda>(x,s). SIDE_PRECOND (x\<notin>s)]\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure (\<langle>R\<rangle>list_set_rel))\<^sup>k \<rightarrow> pure (\<langle>R\<rangle>list_set_rel)"
    apply rule
    apply rule
    (* TODO: Much too low-level reasoning *)
    apply (sep_auto simp: pure_def ls_ins_dj_imp_def intro: list_set_autoref_insert_dj[simplified])
    done

  lemma ls_op_ins_dj_rule[sepref_fr_rules]: 
    "(uncurry (ls_ins_dj_imp), uncurry (RETURN oo op_set_ins_dj)) 
      \<in> [\<lambda>(x,s). SIDE_PRECOND (x\<notin>s)]\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure (\<langle>R\<rangle>list_set_rel))\<^sup>k \<rightarrow> pure (\<langle>R\<rangle>list_set_rel)"
    using ls_ins_dj_rule
    by simp

  (* TODO: This messes up code generation with some odd error msg! Why?  
  (* TODO: Move to imperative-HOL. Or at least to imp-hol-add *)
  context begin
    setup_lifting type_definition_integer 
  
    lift_definition integer_encode :: "integer \<Rightarrow> nat" is int_encode .
  
    lemma integer_encode_eq: "integer_encode x = integer_encode y \<longleftrightarrow> x = y"
      apply transfer
      by (rule inj_int_encode [THEN inj_eq])

    lifting_update integer.lifting
    lifting_forget integer.lifting
  end  

  instance integer :: countable
    by (rule countable_classI [of integer_encode]) (simp add: integer_encode_eq)

  instance integer :: heap ..
  *)

  lemma int_of_integer_less_iff: "int_of_integer x < int_of_integer y \<longleftrightarrow> x<y"
    by (simp add: less_integer_def)

  lemma nat_of_integer_less_iff: "x\<ge>0 \<Longrightarrow> y\<ge>0 \<Longrightarrow> nat_of_integer x < nat_of_integer y \<longleftrightarrow> x<y"
    unfolding nat_of_integer.rep_eq
    by (auto simp: int_of_integer_less_iff nat_less_eq_zless int_of_integer_less_iff[of 0, simplified])
    
  (*(* TODO: Move *)
  lemma param_integer[param]:
    "(0, 0::integer) \<in> Id"
    "(1, 1::integer) \<in> Id"
    "(numeral n::integer,numeral n::integer) \<in> Id"
    "(op <, op <::integer \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
    "(op \<le>, op \<le>::integer \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
    "(op =, op =::integer \<Rightarrow> _) \<in> Id \<rightarrow> Id \<rightarrow> Id"
    "(op +::integer\<Rightarrow>_,op +)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op -::integer\<Rightarrow>_,op -)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op *::integer\<Rightarrow>_,op * )\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op div::integer\<Rightarrow>_,op div)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    "(op mod::integer\<Rightarrow>_,op mod)\<in>Id\<rightarrow>Id\<rightarrow>Id"
    by auto
  
  lemmas [sepref_import_param] = param_integer  
  
  lemmas [id_rules] = 
    itypeI[Pure.of 0 "TYPE (integer)"]
  *)  

end
