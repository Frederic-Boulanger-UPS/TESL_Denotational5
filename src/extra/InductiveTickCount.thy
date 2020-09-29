theory InductiveTickCount

imports "../TeslDenotationalOperators"

begin

text {*
  inductive predicate for tick_count
*}
inductive tick_count_is :: "('a, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat \<Rightarrow> bool"
where
  "\<not>ticks clk (hmt 0) \<Longrightarrow> tick_count_is clk hmt 0 0"
| "ticks clk (hmt 0) \<Longrightarrow> tick_count_is clk hmt 0 1"
| "\<lbrakk>tick_count_is clk hmt k n; \<not>ticks clk (hmt (Suc k))\<rbrakk> \<Longrightarrow> tick_count_is clk hmt (Suc k) n"
| "\<lbrakk>tick_count_is clk hmt k n; ticks clk (hmt (Suc k))\<rbrakk> \<Longrightarrow> tick_count_is clk hmt (Suc k) (Suc n)"

inductive_cases tick_count_00[elim!]:"tick_count_is clk hmt 0 0"
inductive_cases tick_count_01[elim!]:"tick_count_is clk hmt 0 1"
inductive_cases tick_count_sn[elim!]:"tick_count_is clk hmt (Suc k) n"
inductive_cases tick_count_ss[elim!]:"tick_count_is clk hmt (Suc k) (Suc n)"
thm tick_count_ss

text {*
  Soundness of the definition of the tick_count_is predicate and the tick_count_fun function.
*}
lemma tick_count_cons: "tick_count_is clk hmt k (tick_count_fun clk hmt k)"
proof (induction k)
  case 0 thus ?case
    by (metis tick_count_fun.simps(1) tick_count_is.simps)
next
  case (Suc k') thus ?case
    by (simp add: tick_count_is.intros(3) tick_count_is.intros(4) tick_count_is_fun)
qed

text {*
  Proof that the tick_count_is predicate behaves as a function.
*}
lemma tick_count_ind_is_fun: "\<lbrakk>tick_count_is clk hmt k n; tick_count_is clk hmt k n'\<rbrakk> \<Longrightarrow> n = n'"
proof (induction k arbitrary: n n')
  case 0 print_facts
    note k0 = this
    show ?case
    proof (cases n)
      case 0 thus ?thesis using k0
        by (metis less_Suc_eq_0_disj less_numeral_extra(3) tick_count_is.simps)
    next
      case Suc thus ?thesis using k0
        by (metis nat.distinct(1) tick_count_is.simps)
    qed
next
  case (Suc k')
    show ?case
    proof (cases "ticks clk (hmt (Suc k'))")
      case True
        hence "\<exists>m. (n = Suc m) \<and> tick_count_is clk hmt k' m" using Suc by auto
        from this obtain m where hm:"(n = Suc m) \<and> tick_count_is clk hmt k' m" by blast
        from True have "\<exists>m'. (n' = Suc m') \<and> tick_count_is clk hmt k' m'" using Suc by auto
        from this obtain m' where hm':"(n' = Suc m') \<and> tick_count_is clk hmt k' m'" by blast
        with hm hm' have "m = m'" using Suc.IH by simp
        thus ?thesis using hm hm' by simp
    next
      case False thus ?thesis using Suc.IH Suc.prems by blast
    qed
qed

text {*
  Proof of the equivalence of the inductive and the functional definitions of tick_count.
*}
lemma tick_count_eq: "tick_count_is clk hmt k n = (tick_count clk hmt k = n)"
using tick_count_cons tick_count_ind_is_fun by (metis tick_count_is_fun)


end
