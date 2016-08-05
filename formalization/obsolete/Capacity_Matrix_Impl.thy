*** Obsolete, Now in IICF ***
section \<open>Capacity Matrix by Fixed-Size Array\<close>
xxtheory Capacity_Matrix_Impl
imports 
  Fofu_Impl_Base   
  Graph
begin
  (*
  *)




  type_synonym 'a amtx = "nat\<times>nat \<Rightarrow> 'a"
  type_synonym 'a mtx = "'a Heap.array"

  typedecl 'a i_mtx

  definition amtx_new_op :: "'a amtx \<Rightarrow> 'a amtx" where [simp]: "amtx_new_op c \<equiv> c"
  definition amtx_get_op :: "'a amtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a" where [simp]: "amtx_get_op c e \<equiv> (c e)"
  definition amtx_set_op :: "'a amtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a \<Rightarrow> 'a amtx" where [simp]: "amtx_set_op c e v \<equiv> (c(e:=v))"

  sepref_register amtx_new_op "'a amtx \<Rightarrow> 'a i_mtx"
  sepref_register amtx_get_op "'a i_mtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a"
  sepref_register amtx_set_op "'a i_mtx \<Rightarrow> nat\<times>nat \<Rightarrow> 'a \<Rightarrow> 'a i_mtx"

  lemma pat_amtx_get: "c$e\<equiv>amtx_get_op$c$e" by simp
  lemma pat_amtx_set: "fun_upd$c$e$v\<equiv>amtx_set_op$c$e$v" by simp

  lemmas amtx_pats = pat_amtx_get pat_amtx_set

  definition "is_mtx N c mtx \<equiv> \<exists>\<^sub>Al. mtx \<mapsto>\<^sub>a l * \<up>( 
      length l = N*N 
    \<and> (\<forall>i<N. \<forall>j<N. l!(i*N+j) = c (i,j))
    \<and> (\<forall>i j. (i\<ge>N \<or> j\<ge>N) \<longrightarrow> c (i,j) = 0))"

  lemma is_mtx_precise[constraint_rules]: "precise (is_mtx N)"
    apply rule
    unfolding is_mtx_def
    apply clarsimp
    apply prec_extract_eqs
    apply (rule ext)
    apply (rename_tac x)
    apply (case_tac x; simp)
    apply (rename_tac i j)
    apply (case_tac "i<N"; case_tac "j<N"; simp)
    done
    

  definition "mtx_new N c \<equiv> do {
    Array.make (N*N) (\<lambda>i. c (i div N, i mod N))
  }"

  definition "mtx_get N mtx e \<equiv> Array.nth mtx (fst e * N + snd e)"
  definition "mtx_set N mtx e v \<equiv> Array.upd (fst e * N + snd e) v mtx"

  lemma mtx_idx_valid[simp]: "\<lbrakk>i < (N::nat); j < N\<rbrakk> \<Longrightarrow> i * N + j < N * N"
  proof -
    assume a1: "i < N"
    assume a2: "j < N"
    have "\<forall>n na. \<exists>nb. \<not> na < n \<or> Suc (na + nb) = n"
      using less_imp_Suc_add by blast
    hence "0 < N"
      using a2 by blast
    thus ?thesis
      using a2 a1 by (metis (no_types) ab_semigroup_add_class.add.commute ab_semigroup_mult_class.mult.commute add.left_neutral div_if mod_div_equality mod_lemma mult_0_right)
  qed

  lemma mtx_index_unique[simp]: "\<lbrakk>i<(N::nat); j<N; i'<N; j'<N\<rbrakk> \<Longrightarrow> i*N+j = i'*N+j' \<longleftrightarrow> i=i' \<and> j=j'"
    by (metis ab_semigroup_add_class.add.commute add_diff_cancel_right' div_if div_mult_self3 gr0I not_less0)

  lemma mtx_new_rl[sep_heap_rules]: "Graph.V c \<subseteq> {0..<N} \<Longrightarrow> <emp> mtx_new N c <is_mtx N c>"
    by (sep_auto simp: mtx_new_def is_mtx_def Graph.V_def Graph.E_def)

  lemma mtx_get_rl[sep_heap_rules]: "\<lbrakk>i<N; j<N \<rbrakk> \<Longrightarrow> <is_mtx N c mtx> mtx_get N mtx (i,j) <\<lambda>r. is_mtx N c mtx * \<up>(r = c (i,j))>"
    by (sep_auto simp: mtx_get_def is_mtx_def)
    
  lemma mtx_set_rl[sep_heap_rules]: "\<lbrakk>i<N; j<N \<rbrakk> 
    \<Longrightarrow> <is_mtx N c mtx> mtx_set N mtx (i,j) v <\<lambda>r. is_mtx N (c((i,j) := v)) r>"
    by (sep_auto simp: mtx_set_def is_mtx_def nth_list_update)
        
  lemma mtx_new_fr_rl[sepref_fr_rules]: 
    "(mtx_new N, RETURN o amtx_new_op) \<in> [\<lambda>c. Graph.V c \<subseteq> {0..<N}]\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id))\<^sup>k \<rightarrow> is_mtx N"  
    apply rule apply rule
    apply (sep_auto simp: pure_def)
    done

  lemma [sepref_fr_rules]: 
    "CONSTRAINT IS_PURE_ID R \<Longrightarrow> (uncurry (mtx_get N), uncurry (RETURN oo amtx_get_op)) \<in> [\<lambda>(_,(i,j)). i<N \<and> j<N]\<^sub>a (is_mtx N)\<^sup>k *\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel))\<^sup>k \<rightarrow> R"
    apply rule apply rule
    apply (sep_auto simp: pure_def IS_PURE_ID_def)
    done
    
  lemma [sepref_fr_rules]: "CONSTRAINT IS_PURE_ID R \<Longrightarrow> (uncurry2 (mtx_set N), uncurry2 (RETURN ooo amtx_set_op)) 
    \<in> [\<lambda>((_,(i,j)),_). i<N \<and> j<N]\<^sub>a (is_mtx N)\<^sup>d *\<^sub>a (pure (nat_rel \<times>\<^sub>r nat_rel))\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow> is_mtx N"
    apply rule apply rule
    apply (sep_auto simp: pure_def hn_ctxt_def IS_PURE_ID_def)
    done

end
