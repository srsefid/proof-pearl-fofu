theory Fofu_Abs_Base
imports Complex_Main
begin  

  context
  begin
    definition "isDisjoint s \<equiv> \<forall> x y. x \<in> s \<and> y \<in> s \<and> x \<noteq> y \<longrightarrow> x \<inter> y = {}"
  end
  
  locale setExt
  begin
    definition toList :: "'a set \<Rightarrow> 'a list" where
      "toList s \<equiv> (SOME l. distinct l \<and> set l = s)"
      
    lemma set_toList: "finite s \<Longrightarrow> set (toList s) = s"
      unfolding toList_def
      by (metis (mono_tags, lifting) distinct_remdups finite_list set_remdups someI_ex)
      
    lemma toList_Nil: "finite s \<Longrightarrow> toList s = [] \<Longrightarrow> s = {}"
      unfolding toList_def
      by (metis empty_set set_toList toList_def)
      
    lemma finite_fun_set_1: "finite F \<Longrightarrow> finite A \<Longrightarrow> finite {f a |f a. f \<in> F \<and> a \<in> A}"
      (is "_ _ \<Longrightarrow> _ _ \<Longrightarrow> finite ?SFA")
      proof -
        assume asm1: "finite F"
        assume asm2: "finite A"
        have "\<forall>f. finite {f a | a. a \<in> A}" using asm2 by auto
        then have "finite (\<Union>f\<in>F. {f a | a. a \<in> A})" using asm1 by auto
        moreover have "?SFA = (\<Union>f\<in>F. {f a | a. a \<in> A})" by auto
        ultimately show ?thesis by auto
      qed
          
    lemma finite_fun_set_2: "finite A \<Longrightarrow> finite B \<Longrightarrow> finite {f m n | m n. m \<in> A \<and> n \<in> B}"
      (is "_ _ \<Longrightarrow> _ _ \<Longrightarrow> finite ?OS")
      proof -
        assume asm1: "finite A"
        assume asm2: "finite B"
        have "finite {f a | a. a \<in> A }" (is "finite ?SFA") using asm1 by auto
        then have "finite {g b | g b. g \<in> ?SFA \<and> b \<in> B}" (is "finite ?AS")
          using finite_fun_set_1[of ?SFA B] asm2 by auto
        moreover have "?OS = ?AS" by auto
        ultimately show ?thesis by auto
      qed
  end
  
  locale setsumExt
  begin
    lemma singleton: "(\<Sum>y \<in> {x}. f y) = f x" 
      by (metis add_0_right empty_iff finite.emptyI setsum.empty setsum.insert)
      
    lemma decomp_1: "finite A \<Longrightarrow> a \<notin> A \<Longrightarrow> (\<Sum>x \<in> (A \<union> {a}). f x) = f a + (\<Sum>x \<in> A. f x)"
      proof -
        assume asm1: "finite A"
        assume asm2: "a \<notin> A"
        have "{a} \<inter> A = {} \<and> finite {a}" using asm2 by blast
        then have "(\<Sum>x \<in> (A \<union> {a}). f x) = (\<Sum>x \<in> {a}. f x) + (\<Sum>x \<in> A. f x)"
          using setsum.union_disjoint[of "{a}" "A" f] asm1 by auto
        moreover have "(\<Sum>x \<in> {a}. f x) = f a" by (metis (mono_tags) add.commute empty_iff
            finite.emptyI monoid_add_class.add.left_neutral setsum.empty setsum.insert)
        ultimately show ?thesis by auto
      qed
      
    lemma decomp_2: "finite s \<Longrightarrow> finite {g y a | y a. p y a} \<Longrightarrow>
      (\<forall>x y a b. x \<noteq> y \<longrightarrow> g x a \<noteq> g y b) \<Longrightarrow> (\<Sum>x \<in> {g y a | y a. y \<in> s \<and> p y a}. f x) =
      (\<Sum>y \<in> s. (\<Sum>x \<in> {g y a | a. p y a}. f x))"
      proof -
        assume asm1: "finite s"
        assume asm2: "finite {g y a | y a. p y a}"
        assume asm3: "(\<forall>x y a b. x \<noteq> y \<longrightarrow> g x a \<noteq> g y b)"
        {
          fix l
          have "distinct l \<Longrightarrow> finite (set l) \<Longrightarrow> finite {g y a | y a. p y a}
            \<Longrightarrow> (\<forall>x y a b. x \<noteq> y \<longrightarrow> g x a \<noteq> g y b) \<Longrightarrow> 
            (\<Sum>x \<in> {g y a | y a. y \<in> (set l) \<and> p y a}. f x) =
            (\<Sum>y \<in> (set l). (\<Sum>x \<in> {g y a | a. p y a}. f x))"
            proof (induction l)
              case Nil
                thus ?case by auto
            next
              case (Cons e es)
                let ?BSET = "\<lambda>A. {g y a | y a. y \<in> A \<and> p y a}"
                let ?SSUM = "\<lambda>S. (\<Sum>x \<in> S. f x)"
                {
                  note f = setsum.union_disjoint[of "?BSET {e}" "?BSET (set es)" f]
                  {
                    note f = finite_subset[of _ "{g y a | y a. p y a}"]
                    have f1: "?BSET {e} \<subseteq> {g y a | y a. p y a}" by auto
                    then have "finite (?BSET {e})" using f[OF f1 Cons.prems(3)] by blast
                  } note f1 = this
                  {
                    note f = finite_subset[of _ "{g y a | y a. p y a}"]
                    have f1: "?BSET (set es) \<subseteq> {g y a | y a. p y a}" by auto
                    then have "finite (?BSET (set es))" using f[OF f1 Cons.prems(3)] by blast
                  } note f2 = this
                  have f3: "?BSET {e} \<inter> ?BSET (set es) = {}"
                    proof (rule ccontr)
                      assume "\<not> ?BSET {e} \<inter> ?BSET (set es) = {}"
                      then obtain y1 a1 y2 a2 where obt1: "(g y1 a1) = (g y2 a2) \<and> 
                        y1 \<in> {e} \<and> y2 \<in> (set es)" by blast
                      then have "y1 = y2" using Cons.prems(4) by auto
                      then have "\<not> distinct (e # es)" using obt1 by auto
                      thus "False" using Cons.prems(1) by auto 
                    qed
                  have f4: "?BSET (set (e # es)) = ?BSET {e} \<union> ?BSET (set es)" by auto
                  have "?BSET (set (e # es)) = {g y a |y a. y \<in> {e} \<and> p y a} \<union>
                    {g y a |y a. y \<in> set es \<and> p y a}" using Cons.prems(1) by auto 
                  then have "?SSUM (?BSET (set (e # es))) =  
                    ?SSUM (?BSET {e}) + ?SSUM (?BSET (set es))" 
                    using  f[OF f1 f2 f3] using Cons.prems(1) by auto
                } note fct1 = this
                {
                  have f1: "distinct es" using Cons.prems(1) by auto
                  have f2: "finite (set es)" using Cons.prems(2) by auto
                  have "?SSUM (?BSET (set es)) = (\<Sum>y\<in> (set es). (\<Sum>x\<in> {g y a | a. p y a}. f x))"
                    using Cons.IH[OF f1 f2 Cons.prems(3) Cons.prems(4)] by blast
                } note fct2 = this
                have "?SSUM (?BSET {e}) = (\<Sum>y\<in> {e}.(\<Sum>x\<in> {g y a | a. p y a}. f x))" by auto
                show ?case using fct1 fct2 Cons.prems(1) Cons.prems(2) by auto
            qed
        } note fct = this[of "setExt.toList s"]
        let ?L = "setExt.toList s"
        have f1: "distinct ?L" using setExt.toList_def
          by (metis (mono_tags, lifting) asm1 finite_distinct_list some_eq_ex)
        have f2: "finite (set ?L)" unfolding setExt.toList_def by auto
        show ?thesis 
          using fct[OF f1 f2 asm2 asm3] using asm1 setExt.set_toList[of s] by auto
      qed      
      
    lemma decomp_3: "finite A \<Longrightarrow> (\<forall>x y a b. a \<noteq> b \<longrightarrow> g x a \<noteq> g y b) \<Longrightarrow>
      (\<Sum>e \<in> {g x y |y. y \<in> A}. f e) = (\<Sum>e \<in> {y |y. y \<in> A}. f (g x e))"
      proof (induction "card A" arbitrary: A)
        case (0)
          thus ?case by auto
      next
        case (Suc c)
          let ?S_L = "\<lambda>s. {g x y |y. y \<in> s}"
          let ?S_R = "\<lambda>s. {y |y. y \<in> s}"
          let ?SUM_L = "\<lambda>s. (\<Sum>e \<in> s. f e)"
          let ?SUM_R = "\<lambda>s. (\<Sum>e \<in> s. f (g x e))"
          obtain a as where obt: "A = {a} \<union> as \<and> a \<notin> as"
            using Suc.hyps by (metis card_eq_SucD insert_is_Un)
          {
            {
              have f1: "finite (?S_L {a})" by auto
              have f2: "finite (?S_L as)" using Suc.prems(1) obt by auto
              have f3: "?S_L {a} \<inter> ?S_L as = {}"
                proof (rule ccontr)
                  assume "\<not> ?S_L {a} \<inter> ?S_L as = {}"
                  then obtain y1 y2 where s_obt:  "g x y1 = g x y2 \<and> g x y1 \<in> ?S_L {a} \<and> y1 \<in> {a} \<and>
                    g x y2 \<in> ?S_L as \<and> y2 \<in> as" by auto
                  then have "y1 = y2" using Suc.prems(2) by auto
                  then have "a \<in> as" using s_obt by auto
                  thus "False" using obt by auto
                qed
                
              note setsum.union_disjoint[OF f1 f2 f3]
            }
            note this
            moreover have "?S_L ({a} \<union> as) = ?S_L {a} \<union> ?S_L as" using obt by auto  
            ultimately have 
              "?SUM_L (?S_L A) = ?SUM_L (?S_L {a}) + ?SUM_L (?S_L as)" using obt by auto
          }
          moreover {
            have "?SUM_L (?S_L {a}) = ?SUM_R (?S_R {a})" by auto
          } 
          moreover {          
            have f1: "c = card as" using Suc.prems(1) Suc.hyps(2) obt
              by (metis card_0_eq card_Suc_eq diff_Suc_Suc diff_zero finite_insert insert_is_Un)
            have f2: "finite as" using Suc.prems(1) obt by auto
            
            note Suc.hyps(1)[OF f1 f2 Suc.prems(2)]
          }
          moreover {
            {
              have f1: "finite (?S_R {a})" by auto
              have f2: "finite (?S_R as)" using Suc.prems(1) obt by auto
              have f3: "?S_R {a} \<inter> ?S_R as = {}" using obt by auto
              
              note setsum.union_disjoint[OF f1 f2 f3]
            }
            note this[of "\<lambda>e. f (g x e)"]
            moreover have "?S_R {a} \<union> ?S_R as = ?S_R A" using obt by auto
            ultimately have "?SUM_R (?S_R {a}) + ?SUM_R (?S_R as) = ?SUM_R (?S_R A)" by auto
          } 
          ultimately show ?case by auto
      qed
    
    lemma decomp_4: "finite s \<Longrightarrow> \<forall>x \<in> s. f x = a \<Longrightarrow> (\<Sum>x \<in> s. f x) = (\<Sum>y \<in> {n. n < (card s)}. a)"
      proof (induction "card s" arbitrary: s)
        case 0
          thus ?case by auto
      next
        case (Suc c)
          let ?SUM_L = "\<lambda>s. (\<Sum>e \<in> s. f e)"
          obtain b bs where obt: "s = {b} \<union> bs \<and> b \<notin> bs"
            using Suc.hyps by (metis card_eq_SucD insert_is_Un)
          {
            {
              have f1: "finite {b}" by auto
              have f2: "finite bs" using Suc.prems(1) obt by auto
              have f3: "{b} \<inter> bs = {}" using obt by auto
              
              note setsum.union_disjoint[OF f1 f2 f3]
            }
            note this[of f]
            moreover have "{b} \<union> bs = s" using obt by auto  
            ultimately have "?SUM_L s = ?SUM_L {b} + ?SUM_L bs" using obt by auto
          }
          moreover have "?SUM_L {b} = a" using obt Suc.prems(2) by auto
          moreover {
            have f1: "c = card bs" using Suc.prems(1) Suc.hyps(2) obt
              by (metis card_0_eq card_Suc_eq diff_Suc_Suc diff_zero finite_insert insert_is_Un)
            have f2: "finite bs" using Suc.prems(1) obt by auto
            have f3: " \<forall>x \<in> bs. f x = a" using obt Suc.prems(2) by auto
            note Suc.hyps(1)[OF f1 f2 f3]
            
            then have "setsum f bs = (\<Sum>y\<in>{n. n < c}. a)" using f1 by simp
          }
          ultimately have "?SUM_L s = a + (\<Sum>y\<in>{n. n < c}. a)" by auto
          moreover {
            have "{c} \<union> {n. n < c} = {n. n < c + 1}" by auto
            then have "(\<Sum>x\<in>{c} \<union> {n. n < c}. a) = (\<Sum>x\<in>{n. n < c + 1}. a)" by simp
            moreover {
              have f1: "finite {c}" by simp
              have f2: "finite {n. n < c}" by simp
              have f3: "{c} \<inter> {n. n < c} = {}" by simp
              
              note setsum.union_disjoint[OF f1 f2 f3]
              note this[of "\<lambda>x. a"]
            }
            moreover have "(\<Sum>x\<in>{c}. a) = a" by simp
            ultimately have "a + (\<Sum>x\<in>{n. n < c}. a) = (\<Sum>x\<in>{n. n < c + 1}. a)" by simp
          }
          ultimately show ?case using Suc.hyps(2) by auto 
      qed
   end





  (* TODO: Miscellaneous General Stuff *)
  lemma remove_subset[simp]: "x\<in>S \<Longrightarrow> S-{x} \<subset> S" by auto

  lemma fun_neq_ext_iff: "m\<noteq>m' \<longleftrightarrow> (\<exists>x. m x \<noteq> m' x)" by auto  


  (* TODO: Move to Misc *)
  lemma length_Suc_rev_conv: "length xs = Suc n \<longleftrightarrow> (\<exists>ys y. xs=ys@[y] \<and> length ys = n)"
    by (cases xs rule: rev_cases) auto



  (* TODO: Move: Misc, or even HOL/Finite_set *)  
  lemma (in -) card_inverse[simp]: "card (R\<inverse>) = card R"
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

  (* TODO: Move *)
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








end