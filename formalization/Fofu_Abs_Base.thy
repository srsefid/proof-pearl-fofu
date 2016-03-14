theory Fofu_Abs_Base
imports Complex_Main Misc
begin  
  (* TODO: Miscellaneous General Stuff *)
  lemma remove_subset: "x\<in>S \<Longrightarrow> S-{x} \<subset> S" by auto

  lemma fun_neq_ext_iff: "m\<noteq>m' \<longleftrightarrow> (\<exists>x. m x \<noteq> m' x)" by auto  


  (* TODO: Move to Misc *)
  lemma length_Suc_rev_conv: "length xs = Suc n \<longleftrightarrow> (\<exists>ys y. xs=ys@[y] \<and> length ys = n)"
    by (cases xs rule: rev_cases) auto


  lemma zero_comp_diff_simps[simp]: 
    "(0::'a::linordered_idom) \<le> a - b \<longleftrightarrow> b \<le> a" 
    "(0::'a::linordered_idom) < a - b \<longleftrightarrow> b < a" 
    by auto

  (* TODO: Move: Misc, or even HOL/Finite_set *)  
  lemma card_inverse[simp]: "card (R\<inverse>) = card R"
  proof -
    have "finite (R\<inverse>) \<longleftrightarrow> finite R" by auto
    have [simp]: "\<And>R. prod.swap`R = R\<inverse>" by auto
    {
      assume "\<not>finite R"
      hence ?thesis
        by auto
    } moreover {
      assume "finite R"
      with card_image_le[of R prod.swap] card_image_le[of "R\<inverse>" prod.swap]
      have ?thesis by auto
    } ultimately show ?thesis by blast
  qed  


  (* TODO: Elaborate and move to Misc, or HOL *)
  text \<open>Map update at multiple keys\<close>
  definition "map_mmupd m K v k \<equiv> if k\<in>K then Some v else m k"
  lemma map_mmupd_empty[simp]: "map_mmupd m {} v = m"
    by (auto simp: map_mmupd_def)

  lemma mmupd_in_upd[simp]: "k\<in>K \<Longrightarrow> map_mmupd m K v k = Some v"
    by (auto simp: map_mmupd_def)

  lemma mmupd_notin_upd[simp]: "k\<notin>K \<Longrightarrow> map_mmupd m K v k = m k"
    by (auto simp: map_mmupd_def)

  lemma map_mmupdE:
    assumes "map_mmupd m K v k = Some x"
    obtains "k\<notin>K" "m k = Some x"
          | "k\<in>K" "x=v"
    using assms by (auto simp: map_mmupd_def split: split_if_asm)      

  lemma dom_mmupd[simp]: "dom (map_mmupd m K v) = dom m \<union> K"  
    by (auto simp: map_mmupd_def split: split_if_asm)      

  lemma le_map_mmupd_not_dom[simp, intro!]: "m \<subseteq>\<^sub>m map_mmupd m (K-dom m) v" 
    by (auto simp: map_le_def)

  lemma map_mmupd_update_less: "K\<subseteq>K' \<Longrightarrow> map_mmupd m (K - dom m) v \<subseteq>\<^sub>m map_mmupd m (K'-dom m) v"
    by (auto simp: map_le_def map_mmupd_def)

  (* TODO: Move *)
  text \<open>Lexicographic measure, assuming upper bound for second component\<close>
  lemma mlex_fst_decrI:
    fixes a a' b b' N :: nat
    assumes "a<a'"
    assumes "b<N" "b'<N"
    shows "a*N + b < a'*N + b'"
  proof -  
    have "a*N + b + 1 \<le> a*N + N" using \<open>b<N\<close> by linarith 
    also have "\<dots> \<le> a'*N" using \<open>a<a'\<close>
      by (metis Suc_leI ab_semigroup_add_class.add.commute 
        ab_semigroup_mult_class.mult.commute mult_Suc_right mult_le_mono2) 
    also have "\<dots> \<le> a'*N + b'" by auto
    finally show ?thesis by auto
  qed      
    
  lemma mlex_leI:
    fixes a a' b b' N :: nat
    assumes "a\<le>a'"
    assumes "b\<le>b'"
    shows "a*N + b \<le> a'*N + b'"
    using assms
    by (auto intro!: add_mono)
      
  lemma mlex_snd_decrI:
    fixes a a' b b' N :: nat
    assumes "a=a'"
    assumes "b<b'"
    shows "a*N + b < a'*N + b'"
    using assms
    by (auto)

  lemma mlex_bound:  
    fixes a b :: nat
    assumes "a<A"
    assumes "b<N"
    shows "a*N + b < A*N"
    using assms
    using mlex_fst_decrI by fastforce


  (* TODO: Move to Misc, close to finite_psupset, theme: termination orderings *)
  definition "less_than_bool \<equiv> {(a,b). a<(b::bool)}"
  lemma wf_less_than_bool[simp, intro!]: "wf (less_than_bool)"
    unfolding less_than_bool_def
    by (auto simp: wf_def)
  lemma less_than_bool_iff[simp]:
    "(x,y)\<in>less_than_bool \<longleftrightarrow> x=False \<and> y=True"  
    by (auto simp: less_than_bool_def)

  definition "greater_bounded N \<equiv> inv_image less_than (\<lambda>x. N-x)" 
  lemma wf_greater_bounded[simp, intro!]: "wf (greater_bounded N)" by (auto simp: greater_bounded_def)

  lemma greater_bounded_Suc_iff[simp]: "(Suc x,x)\<in>greater_bounded N \<longleftrightarrow> Suc x \<le> N"
    by (auto simp: greater_bounded_def)







end