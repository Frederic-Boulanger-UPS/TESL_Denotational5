theory TeslDenotationalExtensions
imports TeslDenotationalRelations
        TeslDenotationalStuttering

begin

definition ImpliesNot :: \<open>('\<AA>,'b)\<H> \<Rightarrow> ('\<AA>,'c)\<H> \<Rightarrow> ('\<AA>::orderedrank) runs\<close> (infixl "implies not" 55)
  where \<open>(H\<^sub>1 implies not H\<^sub>2) = {r. \<forall>n. ticks H\<^sub>1 (hamlet r n) \<longrightarrow> \<not>ticks H\<^sub>2 (hamlet r n)}\<close>

definition Precedes :: \<open>('\<AA>,'b)\<H> \<Rightarrow> ('\<AA>,'c)\<H> \<Rightarrow> ('\<AA>::orderedrank) runs\<close> (infixl "\<lessapprox>" 55)
  where \<open>(H\<^sub>1 \<lessapprox> H\<^sub>2) = {r. \<forall>n. tick_count H\<^sub>1 (hamlet r) n \<le> tick_count H\<^sub>2 (hamlet r) n}\<close>


lemma card0:\<open>card {i::nat. i = 0 \<and> P i} = card {i::nat. i = 0 \<and> P 0}\<close>
proof -
  have \<open>{i::nat. i = 0 \<and> P i} = (if P 0 then {0} else {})\<close> by (rule Collect_conv_if)
  thus ?thesis by simp
qed

lemma card_suc:\<open>card {i. i \<le> (Suc n) \<and> P i} = card {i. i \<le> n \<and> P i} + card {i. i = (Suc n) \<and> P i}\<close>
proof -
  have \<open>{i. i \<le> n \<and> P i} \<inter> {i. i = (Suc n) \<and> P i} = {}\<close> by auto
  moreover have \<open>{i. i \<le> n \<and> P i} \<union> {i. i = (Suc n) \<and> P i} = {i. i \<le> (Suc n) \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i \<le> n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = (Suc n) \<and> P i}\<close> by simp
  ultimately show ?thesis using card_Un_disjoint[of \<open>{i. i \<le> n \<and> P i}\<close> \<open>{i. i = Suc n \<and> P i}\<close>] by simp
qed

lemma if_equal_equal:
  assumes \<open>A \<noteq> B\<close>
      and \<open>(if P then A else B) = (if Q then A else B)\<close>
    shows \<open>P = Q\<close>
using assms by presburger

lemma ileq0:\<open>(card {i::nat. i \<le> 0 \<and> P i} = card {i::nat. i \<le> 0 \<and> Q i}) = (P 0 = Q 0)\<close>
proof
  { assume \<open>card {i. i \<le> 0 \<and> P i} = card {i. i \<le> 0 \<and> Q i}\<close>
    hence \<open>card {i. i = 0 \<and> P i} = card {i. i = 0 \<and> Q i}\<close> by auto
    hence \<open>card {i::nat. i = 0 \<and> P 0} = card {i::nat. i = 0 \<and> Q 0}\<close> using card0[symmetric] by simp
    hence \<open>(if P 0 then 1 else 0) = (if Q 0 then 1 else 0)\<close> by auto
    from if_equal_equal[OF one_neq_zero this] show \<open>P 0 = Q 0\<close> .
  }
  { assume \<open>P 0 = Q 0\<close>
    hence \<open>card {i::nat. i = 0 \<and> P 0} = card {i::nat. i = 0 \<and> Q 0}\<close> by auto
    hence \<open>card {i::nat. i = 0 \<and> P i} = card {i::nat. i = 0 \<and> Q i}\<close> using card0 by simp
    thus \<open>card {i::nat. i \<le> 0 \<and> P i} = card {i::nat. i \<le> 0 \<and> Q i}\<close> by simp
  }
qed

lemma tick_count_suc:\<open>tick_count C h (Suc n) = (if ticks C (h (Suc n)) then Suc (tick_count C h n) else tick_count C h n)\<close>
by (simp add: tick_count_is_fun)

text \<open>
  Clocks that always have the same tick count tick at the same instants.
\<close>
lemma same_tickcount_same_ticks:
  assumes \<open>\<forall>m. tick_count H\<^sub>1 (hamlet r) m = tick_count H\<^sub>2 (hamlet r) m\<close>
  shows \<open>ticks H\<^sub>1 (hamlet r n) = ticks H\<^sub>2 (hamlet r n)\<close>
proof (cases n)
  case 0
    from assms have \<open>tick_count H\<^sub>1 (hamlet r) 0 = tick_count H\<^sub>2 (hamlet r) 0\<close> by simp
    hence \<open>card {i. i \<le> 0 \<and> ticks H\<^sub>1 (hamlet r i)} = card {i. i \<le> 0 \<and> ticks H\<^sub>2 (hamlet r i)}\<close>
      unfolding tick_count_def .
    with ileq0 and 0 show ?thesis by simp
next
  case (Suc n)
    from tick_count_suc have 
      \<open>tick_count H\<^sub>1 (hamlet r) (Suc n) = (if ticks H\<^sub>1 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>1 (hamlet r) n) else tick_count H\<^sub>1 (hamlet r) n)\<close> .
    moreover from tick_count_suc have 
      \<open>tick_count H\<^sub>2 (hamlet r) (Suc n) = (if ticks H\<^sub>2 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>2 (hamlet r) n) else tick_count H\<^sub>2 (hamlet r) n)\<close> .
    ultimately have \<open>(if ticks H\<^sub>1 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>1 (hamlet r) n) else tick_count H\<^sub>1 (hamlet r) n)
                    = (if ticks H\<^sub>2 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>2 (hamlet r) n) else tick_count H\<^sub>2 (hamlet r) n)\<close> using assms by simp
    also have \<open>... = (if ticks H\<^sub>2 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>1 (hamlet r) n) else tick_count H\<^sub>1 (hamlet r) n)\<close> using assms by simp
    finally have \<open>(if ticks H\<^sub>1 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>1 (hamlet r) n) else tick_count H\<^sub>1 (hamlet r) n)
                = (if ticks H\<^sub>2 (hamlet r (Suc n)) then Suc (tick_count H\<^sub>1 (hamlet r) n) else tick_count H\<^sub>1 (hamlet r) n)\<close> .
  from if_equal_equal[OF n_not_Suc_n[symmetric] this] show ?thesis using Suc by simp
qed

text \<open>
  If two clocks precede one another, they tick at the same instants.
\<close>

lemma prec_prec_sameticks:
  assumes \<open>r \<in> H\<^sub>1 \<lessapprox> H\<^sub>2\<close>
      and \<open>r \<in> H\<^sub>2 \<lessapprox> H\<^sub>1\<close>
    shows \<open>ticks H\<^sub>1 (hamlet r n) = ticks H\<^sub>2 (hamlet r n)\<close>
  using assms unfolding Precedes_def
  by (simp add: same_tickcount_same_ticks dual_order.antisym)

text \<open>
  The never ticking clock can be build using implies and implies not.
\<close>
lemma \<open>(a implies b) \<otimes> (a implies not b) = {r. \<forall>n. \<not>ticks a (hamlet r n)}\<close>
proof
  { fix w assume \<open>w \<in> a implies b \<otimes> (a implies not b)\<close>
    hence \<open>w \<in> {r. \<forall>n. ticks a (hamlet r n) \<longrightarrow> ticks b (hamlet r n)}
             \<inter> {r. \<forall>n. ticks a (hamlet r n) \<longrightarrow> \<not>ticks b (hamlet r n)}\<close>
      unfolding TeslComp_def Implies_def ImpliesNot_def .
    hence \<open>w \<in> {r. \<forall>n. ticks a (hamlet r n) \<longrightarrow> (ticks b (hamlet r n) \<and> \<not>ticks b (hamlet r n))}\<close> by auto
    hence \<open>w \<in> {r. \<forall>n. \<not>ticks a (hamlet r n)}\<close> by simp
  } thus \<open>a implies b \<otimes> (a implies not b) \<subseteq> {r. \<forall>n. \<not> ticks a (hamlet r n)}\<close> ..
  { fix w::\<open>'a run\<close> assume \<open>w \<in> {r. \<forall>n. \<not>ticks a (hamlet r n)}\<close>
    hence \<open>w \<in> {r. \<forall>n. ticks a (hamlet r n) \<longrightarrow> False}\<close> by simp
    hence \<open>w \<in> {r. \<forall>n. ticks a (hamlet r n) \<longrightarrow> (ticks b (hamlet r n) \<and> \<not>ticks b (hamlet r n))}\<close> by simp
    hence \<open>w \<in> (a implies b) \<otimes> (a implies not b)\<close> unfolding TeslComp_def Implies_def ImpliesNot_def by simp
  } thus \<open>{r. \<forall>n. \<not> ticks a (hamlet r n)} \<subseteq> a implies b \<otimes> (a implies not b)\<close> ..
qed

text \<open>
  A simpler definition of never.
\<close>
definition never
  where \<open>never a = a implies not a\<close>

lemma \<open>never a = {r. \<forall>n. \<not>ticks a (hamlet r n)}\<close>
proof -
  from never_def have \<open>never a = a implies not a\<close> .
  also from ImpliesNot_def have \<open>... = {r. \<forall>n. ticks a (hamlet r n) \<longrightarrow> \<not>ticks a (hamlet r n)}\<close> .
  also have \<open>... = {r. \<forall>n. \<not>ticks a (hamlet r n)}\<close> by simp
  finally show ?thesis .
qed

text \<open>
  Implies not implications are preserved by dilation.
\<close>
lemma impliesnot_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> (a implies not b)\<close>
    shows \<open>r \<in> (a implies not b)\<close>
  by (smt ImpliesNot_def assms is_subrun_def mem_Collect_eq ticks_imp_ticks_subk ticks_sub)

text \<open>
  Precedence relations are preserved by dilation.
\<close>
lemma dil_tick_count:
  assumes \<open>dilating f sub r\<close>
      and \<open>\<forall>n. tick_count a (hamlet r) (f n) \<le> tick_count b (hamlet r) (f n)\<close>
    shows \<open>tick_count a (hamlet r) n \<le> tick_count b (hamlet r) n\<close>
proof (induction n)
  case 0
  then show ?case using assms dilating_def dilating_fun_def
    by (smt Collect_cong empty_dilated_prefix le_neq_trans order_refl tick_count_def zero_order(2))
next
  case (Suc n)
  then show ?case using assms   
    by (smt tick_count_suc ticks_imp_ticks_subk)
qed

lemma precedes_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> (a \<lessapprox> b)\<close>
    shows \<open>r \<in> (a \<lessapprox> b)\<close>
proof -
  from assms(1) is_subrun_def obtain f where dil:\<open>dilating f sub r\<close> by blast
  from assms(2) Precedes_def have \<open>sub \<in> {r. \<forall>n. tick_count a (hamlet r) n \<le> tick_count b (hamlet r) n}\<close> by blast
  hence \<open>r \<in> {r. \<forall>n. tick_count a (hamlet r) (f n) \<le> tick_count b (hamlet r) (f n)}\<close> by (simp add: tick_count_sub[OF dil])
  hence \<open>\<forall>n. tick_count a (hamlet r) (f n) \<le> tick_count b (hamlet r) (f n)\<close> ..
  from dil_tick_count[OF dil this] show ?thesis using Precedes_def by blast
qed

end
