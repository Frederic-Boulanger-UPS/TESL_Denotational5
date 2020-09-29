theory TeslDenotationalOperators

imports TeslDenotationalCore NatStrongInduct

begin
text \<open>
  We define here operators on the semantic domain of TESL that will be used to define
  the semantics of the relations between clocks.
\<close>

text \<open>
  Tell whether a clock ticks in an event.
\<close>
definition ticks :: \<open>('a::orderedrank, 'b)\<H> \<Rightarrow> event \<Rightarrow> bool\<close>
where     \<open>ticks clk evt \<equiv> (let n = (index clk) in if n < length evt then evt ! n else False)\<close> 

text \<open>
  When no tick occurs, no clock ticks.
\<close>
lemma not_tick_occurs:
  assumes \<open>\<not>tick_occurs (h n)\<close>
    shows \<open>\<not>ticks c (h n)\<close>
proof -
  from assms have \<open>\<forall>i. i < length (h n) \<longrightarrow> (h n)!i = False\<close>
    using nth_mem tick_occurs_def by blast
  thus ?thesis unfolding ticks_def by auto
qed

text \<open>
  A clock can tick in an event only if its index is in the range of the event.
\<close>
lemma ticks_idx:
  \<open>ticks c evt \<Longrightarrow> (index c) < length evt\<close>
proof -
  assume h:\<open>ticks c evt\<close>
  { assume \<open>\<not>((index c < length evt))\<close>
    hence \<open>\<not>ticks c evt\<close> unfolding ticks_def by simp
    with h have False by simp
  }
  thus ?thesis by blast
qed

text \<open>
  When a clock ticks in an event, there is True at the index of the clock in that event.
\<close>
lemma ticks_ham:\<open>ticks c evt \<Longrightarrow> evt!(index c)\<close>
proof -
  assume h:\<open>ticks c evt\<close>
  have \<open>index c < length evt\<close> using ticks_idx[OF h] .
  with h show ?thesis unfolding ticks_def by simp
qed

text \<open>
  When either a or b ticks, there is a tick.
  Notice that since clocks a and b may not have the same type, this lemma is not so easy
  to prove automatically.
\<close>
lemma either_ticks_tick_occurs:
  assumes \<open>ticks a evt \<or> ticks b evt\<close>
  shows   \<open>tick_occurs evt\<close>
proof -
  from assms show ?thesis
  proof
    { assume \<open>ticks a evt\<close>
      from ticks_idx[OF this] ticks_ham[OF this] tick_occurs_def nth_mem show ?thesis by blast
    }
    { assume \<open>ticks b evt\<close>
      from ticks_idx[OF this] ticks_ham[OF this] tick_occurs_def nth_mem show ?thesis by blast
    }
  qed
qed

text \<open>
  For any nat, there exists a clock with that index.
\<close>
lemma clock_exists_idx:\<open>\<exists>c::('a::orderedrank, 'b)\<H>. (index c) = k\<close>
proof -
  have \<open>\<exists>f::'a\<Rightarrow>'b. True\<close> by simp
  from this obtain f::\<open>'a\<Rightarrow>'b\<close> where True by blast
  have \<open>index (f, k) = k\<close> by simp
  thus ?thesis by simp
qed

text \<open>
  A tick occurs in an event iff there is a clock that ticks in that event.
\<close>
lemma one_tick_occurs:\<open>(\<exists>c::('a::orderedrank, 'b)\<H>. ticks c i) = tick_occurs i\<close>
proof
  { assume \<open>\<exists>c::('a::orderedrank, 'b)\<H>. ticks c i\<close>
    from this obtain c::\<open>('a::orderedrank, 'b)\<H>\<close> where cprop:\<open>ticks c i\<close> by blast
    from ticks_idx[OF this] have idx:\<open>index c < length i\<close> .
    with cprop have \<open>i!(index c)\<close> unfolding ticks_def by simp
    with idx have \<open>\<exists>x \<in> set i. x\<close> using nth_mem by blast
  } thus \<open>\<exists>c::('a::orderedrank, 'b)\<H>. ticks c i \<Longrightarrow> tick_occurs i\<close> unfolding tick_occurs_def .
next
  { assume \<open>tick_occurs i\<close>
    from this obtain x where \<open>x \<in> set i \<and> x\<close> unfolding tick_occurs_def by blast
    hence \<open>\<exists>k. k < length i \<and> i!k\<close> by (auto simp add: in_set_conv_nth)
    from this obtain k where \<open>k < length i \<and> i!k\<close> by blast
    hence \<open>\<exists>c::('a::orderedrank, 'b)\<H>. ticks c i\<close>
      unfolding ticks_def using clock_exists_idx by auto
  } thus \<open>tick_occurs i \<Longrightarrow> \<exists>c::('a::orderedrank, 'b)\<H>. ticks c i\<close> .
qed

text \<open>
  Instant of the first tick of a clock:
  first_tick c h = Some k if c ticked for the first time at k in hamlet h
                   None if c does not tick in hamlet k
\<close>
definition first_tick :: \<open>('a::orderedrank, 'b)\<H> \<Rightarrow> hamlet \<rightharpoonup> nat\<close>
where
  \<open>first_tick clk hmt = (if (\<exists>k. ticks clk (hmt k))
                         then Some (LEAST k. ticks clk (hmt k))
                         else None)\<close>

text \<open>
  If a clock has a first tick, it ticks at some instant.
\<close>
lemma first_tick_ticks:
  assumes \<open>first_tick c h \<noteq> None\<close>
  shows   \<open>\<exists>t. ticks c (h t)\<close>
proof -
  {
    assume \<open>\<nexists>t. ticks c (h t)\<close>
    with first_tick_def[of \<open>c\<close> \<open>h\<close>] have \<open>first_tick c h = None\<close> by simp
    with assms have False by simp
  }
  thus ?thesis by blast
qed

text \<open>
  If a clock has no first tick, it never ticks.
\<close>
lemma no_first_tick_no_tick:
  assumes \<open>first_tick c h = None\<close>
  shows   \<open>\<nexists>k. ticks c (h k)\<close>
proof -
  {
    assume \<open>\<exists>k. ticks c (h k)\<close>
    hence \<open>first_tick c h \<noteq> None\<close> unfolding first_tick_def by simp
    with assms have False by simp
  }
  thus ?thesis by blast
qed

text \<open>
  A non empty set of nats has a least element.
\<close>
lemma Least_nat_ex:
  \<open>(n::nat) \<in> S \<Longrightarrow> \<exists>x \<in> S. (\<forall>y \<in> S. x \<le> y)\<close>
by (induction n rule: nat_less_induct, insert not_le_imp_less, blast)


text \<open>
  tick_count c h n = number of ticks of clock c in hamlet h upto instant n
\<close>
definition tick_count :: \<open>('a::orderedrank, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat\<close>
where
  \<open>tick_count c h n = card {i. i \<le> n \<and> ticks c (h i)}\<close>

text \<open>
  Another definition as a function.
\<close>
fun tick_count_fun :: \<open>('a::orderedrank, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat\<close>
where
  \<open>tick_count_fun clk hmt 0 = (if ticks clk (hmt 0) then 1 else 0)\<close>
| \<open>tick_count_fun clk hmt (Suc k) = (if ticks clk (hmt (Suc k))
                                     then Suc (tick_count_fun clk hmt k)
                                     else tick_count_fun clk hmt k)\<close>
text \<open>
  A singleton of nat can be defined with a weaker property.
\<close>
lemma nat_sing_prop:
  \<open>{i::nat. i = k \<and> P(i)} = {i::nat. i = k \<and> P(k)}\<close>
by auto

text \<open>
  The set definition and the function definition of tick_count are equivalent.
\<close>
lemma tick_count_is_fun[code]:\<open>tick_count c h n = tick_count_fun c h n\<close>
proof (induction n)
  case 0
    have \<open>tick_count c h 0 = card {i. i \<le> 0 \<and> ticks c (h i)}\<close>
      by (simp add: tick_count_def)
    also have \<open>... = card {i::nat. i = 0 \<and> ticks c (h 0)}\<close>
      using le_zero_eq nat_sing_prop[of \<open>0\<close> \<open>\<lambda>i. ticks c (h i)\<close>] by simp
    also have \<open>... = (if ticks c (h 0) then 1 else 0)\<close> by simp
    also have \<open>... = tick_count_fun c h 0\<close> by simp
    finally show ?case .
next
  case (Suc k)
    show ?case
    proof (cases \<open>ticks c (h (Suc k))\<close>)
      case True
        hence \<open>{i. i \<le> Suc k \<and> ticks c (h i)} = insert (Suc k) {i. i \<le> k \<and> ticks c (h i)}\<close>
          by auto
        hence \<open>tick_count c h (Suc k) = Suc (tick_count c h k)\<close>
          by (simp add: tick_count_def)
        with Suc.IH have \<open>tick_count c h (Suc k) = Suc (tick_count_fun c h k)\<close> by simp
        thus ?thesis by (simp add: True)
    next
      case False
        hence \<open>{i. i \<le> Suc k \<and> ticks c (h i)} = {i. i \<le> k \<and> ticks c (h i)}\<close>
          using le_Suc_eq by auto
        hence \<open>tick_count c h (Suc k) = tick_count c h k\<close> by (simp add: tick_count_def)
        thus ?thesis using Suc.IH by (simp add: False)
    qed
qed

text \<open>
  Number of ticks of a clock in the interval ]m, n]
\<close>
definition tick_count_between ::\<open>('a::orderedrank, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> instant \<Rightarrow> nat\<close>
where \<open>tick_count_between c h m n \<equiv> card {p. m < p \<and> p \<le> n \<and> ticks c (h p)}\<close>

text \<open>
  The tick count between m and n is the difference of the tick counts at n and m.
\<close>
lemma count_diff:
  assumes \<open>n \<ge> m\<close>
  shows   \<open>tick_count_between c h m n = (tick_count c h n) - (tick_count c h m)\<close>
proof -
  have finite:\<open>finite {p. p \<le> m \<and> ticks c (h p)}\<close> by simp
  have incl:\<open>{p. p \<le> m \<and> ticks c (h p)} \<subseteq> {p. p \<le> n \<and> ticks c (h p)}\<close> using assms by auto
  have \<open>{p. m < p \<and> p \<le> n \<and> ticks c (h p)} =
        {p. p \<le> n \<and> ticks c (h p)} - {p. p \<le> m \<and> ticks c (h p)}\<close> by auto
  with card_Diff_subset[OF finite incl] have
    \<open>card {p. m < p \<and> p \<le> n \<and> ticks c (h p)} =
     card {p. p \<le> n \<and> ticks c (h p)} - card {p. p \<le> m \<and> ticks c (h p)}\<close>
    by simp
  thus ?thesis unfolding tick_count_def tick_count_between_def .
qed

lemma count_fun_diff:
  assumes \<open>n \<ge> m\<close>
  shows   \<open>tick_count_between c h m n = (tick_count_fun c h n) - (tick_count_fun c h m)\<close>
using count_diff[of \<open>m\<close> \<open>n\<close> \<open>c\<close> \<open>h\<close>, OF assms] tick_count_is_fun[of \<open>c\<close> \<open>h\<close>] by simp

text \<open>
  There are no ticks in an empty interval.
\<close>
lemma count_null:
  assumes \<open>n \<le> m\<close>
  shows   \<open>tick_count_between c h m n = 0\<close>
proof -
  from assms have \<open>{p. m < p \<and> p \<le> n} = {}\<close> by auto
  thus ?thesis unfolding tick_count_between_def by auto
qed

text \<open>
  filter s k rs rk x tells whether the filter which skips s ticks, then keep k ticks,
  then repeatedly skips rs ticks and keeps rk ticks is active after x ticks.

  For instance, the filter \texttt{1 2 (1 1)* } is active:
  \begin{itemize}
    \item for x = 2 and 3
    \item for any odd x starting from 5
  \end{itemize}

  Some ASCII art explaining how filter works:
  \begin{verbatim}
  --+--+--+--+--+--+--+--+--+--+--+-- ...
  -- --+--+-- --+-- --+-- --+-- --+-- ...
    1  2  3  4  5  6  7  8  9  10 11  ...
  \end{verbatim}
\<close>
definition filter
where
  \<open>filter s k rs rk x \<equiv> (s < x \<and> x \<le> s + k)
                       \<or> ((x > s+k) \<and> (rk > 0) \<and> ((x - (s+k+1)) mod (rs + rk) \<ge> rs))\<close>

text \<open>
  first_tick_since c h from now = there is a tick on clock c now in hamlet h,
                                  and there was no tick on c in the interval [from, now[ of h. 
\<close>
definition first_tick_since :: \<open>('\<AA>::orderedrank,'a)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> instant \<Rightarrow> bool\<close>
where
  \<open>first_tick_since c h from now \<equiv> ticks c (h now)
                                 \<and> (now \<ge> from)
                                 \<and> (\<forall>t. (from \<le> t \<and> t < now) \<longrightarrow> \<not>ticks c (h t))\<close>

text \<open>
  has_ticked_since c h from now = there was at least a tick on clock c
                                  in the interval [from , now] of hamlet h.
\<close>
definition has_ticked_since :: \<open>('\<AA>::orderedrank,'a)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> instant \<Rightarrow> bool\<close>
where
  \<open>has_ticked_since c h from now \<equiv> (\<exists>t. from \<le> t \<and> t \<le> now \<and> ticks c (h t))\<close>

text \<open>
  An item in an interval belongs to either split parts of the interval.
\<close>
lemma interval_split:
  assumes \<open>(a::nat) \<le> m \<and> m \<le> b\<close>
    shows \<open>(a \<le> t \<and> t \<le> b) = ((a \<le> t \<and> t \<le> m) \<or> (m \<le> t \<and> t \<le> b))\<close>
using assms by linarith

text \<open>
  A tick in an interval belongs to either split parts of the interval.
\<close>
lemma has_ticked_since_split:
  assumes \<open>from \<le> interm \<and> interm \<le> now\<close>
    shows \<open>has_ticked_since c h from now
         = (has_ticked_since c h from interm \<or> has_ticked_since c h interm now)\<close>
unfolding has_ticked_since_def using interval_split[OF assms] by auto

text \<open>
  If a clock ticks at the beginning of an interval, it ticks in this interval.
\<close>
lemma has_ticked_since_from:
  assumes \<open>ticks c (h fr)\<close>
  and     \<open>fr \<le> now\<close>
  shows   \<open>has_ticked_since c h fr now\<close>
using assms unfolding has_ticked_since_def by blast

text \<open>
  If a clock ticks at the end of an interval, it ticks in this interval.
\<close>
lemma has_ticked_since_now:
  assumes \<open>ticks c (h now)\<close>
  and     \<open>fr \<le> now\<close>
  shows   \<open>has_ticked_since c h fr now\<close>
using assms unfolding has_ticked_since_def by blast

text \<open>
  Corollaries of the previous two lemmas.
\<close>
lemma has_ticked_since_from_idem:
  assumes \<open>fr \<le> now\<close>
  shows   \<open>has_ticked_since c h fr now = (ticks c (h fr) \<or> has_ticked_since c h fr now)\<close>
using assms has_ticked_since_from by blast

lemma has_ticked_since_now_idem:
  assumes \<open>fr \<le> now\<close>
  shows   \<open>has_ticked_since c h fr now = (ticks c (h now) \<or> has_ticked_since c h fr now)\<close>
using assms has_ticked_since_now by blast

text \<open>
  If a clock has ticked in [n0, n], the interval cannot be empty.
\<close>
lemma ht_not_empty:
  assumes \<open>has_ticked_since c h n\<^sub>0 n\<close>
    shows \<open>n\<^sub>0 \<le> n\<close>
using assms has_ticked_since_def le_trans by blast

text \<open>
  A clock has necessarily ticked in [from , now] if it ticks for the first time in [from, now]
\<close>
lemma first_tick_has_ticked:
  assumes \<open>first_tick_since c h from now\<close>
  shows   \<open>has_ticked_since c h from now\<close>
proof -
  from assms(1) have \<open>ticks c (h now) \<and> (now \<ge> from)\<close>
    using first_tick_since_def by blast
  thus ?thesis using has_ticked_since_def by blast
qed

text \<open>
  have_both_ticked a b h n = clocks a and b have both ticked at instant n in hamlet h.
  This means that either a has ticked before and b has just ticked at n, or b has ticked before
  and a has just ticked at n.
  Each time both clocks have ticked, they must tick again both in order to consider that
  they have both ticked later.

  Example:
  \begin{verbatim}
                     a --*-----*--*--*----------*--
                     b -----*--*-------*--*--*-----
  have both ticked a b -----*--*-------*--------*--
  \end{verbatim}
\<close>
text \<open>
  A definition of the condition of have_both_ticked:
\<close>
definition has_first_since ::\<open>('a::orderedrank, 'b)\<H>
                           \<Rightarrow> ('a, 'c)\<H>
                           \<Rightarrow> hamlet \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>
where
  \<open>has_first_since a b h n\<^sub>0 n \<equiv> has_ticked_since a h n\<^sub>0 n \<and> first_tick_since b h n\<^sub>0 n\<close>

text \<open>
  This condition implies that both clock have ticked since n0.
\<close>
lemma hft_ht:
  assumes \<open>has_first_since a b h n\<^sub>0 n\<close>
    shows \<open>has_ticked_since a h n\<^sub>0 n \<and> has_ticked_since b h n\<^sub>0 n\<close>
using assms first_tick_has_ticked has_first_since_def by blast

text \<open>
  Inductive definition of have_both_ticked:
\<close>
inductive have_both_ticked ::\<open>('\<AA>::orderedrank,'a)\<H> \<Rightarrow> ('\<AA>,'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> bool\<close>
where
  \<comment> \<open> First ticks since origin \<close>
  \<open>has_first_since a b h 0 n \<Longrightarrow> have_both_ticked a b h n\<close>
| \<open>has_first_since b a h 0 n \<Longrightarrow> have_both_ticked a b h n\<close>
  \<comment> \<open> Induction \<close>
| \<open>\<lbrakk>have_both_ticked a b h n\<^sub>0; has_first_since a b h (Suc n\<^sub>0) n\<rbrakk> \<Longrightarrow> have_both_ticked a b h n\<close>
| \<open>\<lbrakk>have_both_ticked a b h n\<^sub>0; has_first_since b a h (Suc n\<^sub>0) n\<rbrakk> \<Longrightarrow> have_both_ticked a b h n\<close>

inductive_cases hbt0: \<open>have_both_ticked a b h 0\<close>
thm hbt0
inductive_cases hbtn: \<open>have_both_ticked a b h n\<close>
thm hbtn

text \<open>
  A disjunctive form of the inductive case for have_both_ticked a b h 0.
\<close>
lemma hbt0':
  assumes \<open>have_both_ticked a b h 0\<close>
  shows   \<open>has_first_since a b h 0 0 \<or> has_first_since b a h 0 0\<close>
proof -
    from hbt0[OF assms] consider
      (a) \<open>has_ticked_since a h 0 0 \<and> first_tick_since b h 0 0\<close>
    | (b) \<open>has_ticked_since b h 0 0 \<and> first_tick_since a h 0 0\<close>
    | (c) \<open>\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since a b h (Suc n\<^sub>0) 0\<close>
    | (d) \<open>\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since b a h (Suc n\<^sub>0) 0\<close>
    using has_first_since_def[of \<open>a\<close> \<open>b\<close> \<open>h\<close> \<open>0\<close> \<open>0\<close>]
          has_first_since_def[of \<open>b\<close> \<open>a\<close> \<open>h\<close> \<open>0\<close> \<open>0\<close>] by blast
    hence \<open>has_first_since a b h 0 0 \<or> has_first_since b a h 0 0\<close>
    proof cases
      case a thus ?thesis by (simp add: has_first_since_def)
    next
      case b thus ?thesis by (simp add: has_first_since_def)
    next
      case c
        from this obtain n\<^sub>0 where \<open>has_first_since a b h (Suc n\<^sub>0) 0\<close> by auto
        hence \<open>0 \<ge> Suc n\<^sub>0\<close> using first_tick_since_def has_first_since_def by blast
        hence False by simp
        thus ?thesis ..
    next
      case d
        from this obtain n\<^sub>0 where \<open>has_first_since b a h (Suc n\<^sub>0) 0\<close> by auto
        hence \<open>0 \<ge> Suc n\<^sub>0\<close> using first_tick_since_def has_first_since_def by blast
        hence False by simp
        thus ?thesis ..
    qed
    thus ?thesis .
qed

text \<open>
  Disjunctive form of the inductive case "have_both_ticked a b h n"
\<close>
lemma btn_btn0:
  assumes \<open>have_both_ticked a b h n\<close>
    shows \<open>has_first_since a b h 0 n
         \<or> has_first_since b a h 0 n
         \<or> (\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0
              \<and> (has_first_since a b h (Suc n\<^sub>0) n \<or> has_first_since b a h (Suc n\<^sub>0) n))\<close>
using hbtn[OF assms] by auto

text \<open>
  Same lemma, but with distributed existential quantification.
\<close>
lemma btn_btn0':
  assumes \<open>have_both_ticked a b h n\<close>
    shows \<open>has_first_since a b h 0 n
         \<or> has_first_since b a h 0 n
         \<or> (\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since a b h (Suc n\<^sub>0) n)
         \<or> (\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since b a h (Suc n\<^sub>0) n)\<close>
using hbtn[OF assms] by auto

text \<open>
  This lemma is in fact an equivalence.
\<close>
lemma hbt_disj:\<open>have_both_ticked a b h n =
                has_first_since a b h 0 n
                 \<or> has_first_since b a h 0 n
                 \<or> (\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since a b h (Suc n\<^sub>0) n)
                 \<or> (\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since b a h (Suc n\<^sub>0) n)\<close>
using btn_btn0' have_both_ticked.intros by blast

text \<open>
  have_both_ticked is commutative on clocks.
\<close>
lemma hbt_commutes: \<open>have_both_ticked a b h n \<Longrightarrow> have_both_ticked b a h n\<close>
proof (induction n rule: nat_strong_induct)
  case 0 thus ?case using hbt0' have_both_ticked.intros(1,2) by blast
next
  case (Suc k)
    assume \<open>have_both_ticked a b h (Suc k)\<close>
    from btn_btn0'[OF this] consider
      (a) \<open>has_first_since a b h 0 (Suc k)\<close>
    | (b) \<open>has_first_since b a h 0 (Suc k)\<close>
    | (c) \<open>\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since a b h (Suc n\<^sub>0) (Suc k)\<close>
    | (d) \<open>\<exists>n\<^sub>0. have_both_ticked a b h n\<^sub>0 \<and> has_first_since b a h (Suc n\<^sub>0) (Suc k)\<close>
    by blast
    thus ?case
    proof cases
      case a thus ?thesis by (rule have_both_ticked.intros(2))
    next
      case b thus ?thesis by (rule have_both_ticked.intros(1))
    next
      case c
      from this obtain n\<^sub>0 where
        hbt:\<open>have_both_ticked a b h n\<^sub>0\<close> and hfs:\<open>has_first_since a b h (Suc n\<^sub>0) (Suc k)\<close> by blast
      from hfs have \<open>Suc n\<^sub>0 \<le> Suc k\<close> using ht_not_empty hft_ht by blast
      hence \<open>n\<^sub>0 \<le> k\<close> using Suc_le_mono by simp 
      with Suc.IH hbt have \<open>have_both_ticked b a h n\<^sub>0\<close> by simp
      from have_both_ticked.intros(4)[OF this hfs] show ?thesis .
    next
      case d
      from this obtain n\<^sub>0 where
        hbt:\<open>have_both_ticked a b h n\<^sub>0\<close> and hfs:\<open>has_first_since b a h (Suc n\<^sub>0) (Suc k)\<close> by blast
      from hfs have \<open>Suc n\<^sub>0 \<le> Suc k\<close> using ht_not_empty hft_ht by blast
      hence \<open>n\<^sub>0 \<le> k\<close> using Suc_le_mono by simp
      with Suc.IH hbt have \<open>have_both_ticked b a h n\<^sub>0\<close> by simp
      from have_both_ticked.intros(3)[OF this hfs] show ?thesis .
    qed
qed

text \<open>
  If both clocks have ticked at instant 0, each clock ticks at 0
\<close>
lemma bt0_bt0:
  assumes \<open>have_both_ticked a b h 0\<close>
  shows   \<open>ticks a (h 0) \<and> ticks b (h 0)\<close>
using hbt0[OF assms]
by (auto simp add:first_tick_since_def has_ticked_since_def has_first_since_def)

text \<open>
  If a clock has ticked in [n1, n], it also has ticked at n since an earlier instant.
\<close>
lemma has_ticked_since_earlier:
  assumes \<open>has_ticked_since a h n\<^sub>1 n\<close>
      and \<open>n\<^sub>1 \<ge> n\<^sub>0\<close>
    shows \<open>has_ticked_since a h n\<^sub>0 n\<close>
proof -
  from assms(1) have \<open>(\<exists>t. n\<^sub>1 \<le> t \<and> t \<le> n \<and> ticks a (h t))\<close> unfolding has_ticked_since_def .
  with assms(2) have \<open>(\<exists>t. n\<^sub>0 \<le> t \<and> t \<le> n \<and> ticks a (h t))\<close> using le_trans by blast
  thus ?thesis unfolding has_ticked_since_def .
qed

text \<open>
  If a clock has ticked in [n0, n], it also has ticked at a later instant since n0.
\<close>
lemma has_ticked_since_later:
  assumes \<open>has_ticked_since a h n\<^sub>0 n\<close>
      and \<open>n' \<ge> n\<close>
    shows \<open>has_ticked_since a h n\<^sub>0 n'\<close>
proof -
  from assms(1) have \<open>(\<exists>t. n\<^sub>0 \<le> t \<and> t \<le> n \<and> ticks a (h t))\<close> unfolding has_ticked_since_def .
  with assms(2) have \<open>(\<exists>t. n\<^sub>0 \<le> t \<and> t \<le> n' \<and> ticks a (h t))\<close> using le_trans by blast
  thus ?thesis unfolding has_ticked_since_def .
qed


text \<open>
  When two clocks have both ticked at instant n, at least one of them ticks at instant n.
\<close>
lemma hbt_t:
  assumes \<open>have_both_ticked a b h n\<close>
    shows \<open>ticks a (h n) \<or> ticks b (h n)\<close>
using btn_btn0[OF assms] unfolding has_first_since_def first_tick_since_def by blast

text \<open>
  When two clocks have both ticked at instant n, the first one has ticked since instant 0.
\<close>
lemma hbt_hta:
  assumes \<open>have_both_ticked a b h n\<close>
    shows \<open>has_ticked_since a h 0 n\<close>
using btn_btn0[OF assms] unfolding has_first_since_def
                         using first_tick_has_ticked[of \<open>a\<close> \<open>h\<close> _ \<open>n\<close>] 
                               has_ticked_since_earlier[of \<open>a\<close> \<open>h\<close> _ \<open>n\<close> \<open>0\<close>]
                               le0
by blast

text \<open>
  When two clocks have both ticked at instant n, the second one has ticked since instant 0.
\<close>
lemma hbt_htb:
  assumes \<open>have_both_ticked a b h n\<close>
    shows \<open>has_ticked_since b h 0 n\<close>
using btn_btn0[OF assms] unfolding has_first_since_def
                         using first_tick_has_ticked[of \<open>b\<close> \<open>h\<close> _ \<open>n\<close>] 
                               has_ticked_since_earlier[of \<open>b\<close> \<open>h\<close> _ \<open>n\<close> \<open>0\<close>]
                               le0
by blast

text \<open>
  When a clock has ticked in [n0, n], it cannot have its first tick since n0 at n+1.
\<close>
lemma ht_nft:
  assumes \<open>has_ticked_since a h n\<^sub>0 n\<close>
    shows \<open>\<not>first_tick_since a h n\<^sub>0 (Suc n)\<close>
proof
  assume h:\<open>first_tick_since a h n\<^sub>0 (Suc n)\<close>
  hence \<open>\<forall>t. (n\<^sub>0 \<le> t \<and> t \<le> n) \<longrightarrow> \<not>ticks a (h t)\<close>
    by (simp add: first_tick_since_def)
  moreover from assms have \<open>\<exists>t. n\<^sub>0 \<le> t \<and> t \<le> n \<and> ticks a (h t)\<close>
    by (simp add: has_ticked_since_def)
  ultimately show False by blast
qed

text \<open>
  If two clocks have both ticked at n0, and then later at n, each of these clocks
  has necessarily ticked in ]n0, n].
  This theorem shows that when the inductive introduction rules of have_both_ticked
  are used, n0 is necessarily the latest instant which satisfies the introduction rule.
\<close>

lemma hbt_hts:\<open>\<lbrakk>have_both_ticked a b h n; have_both_ticked a b h n\<^sub>0; n > n\<^sub>0 \<rbrakk>
            \<Longrightarrow> has_ticked_since a h (Suc n\<^sub>0) n \<and> has_ticked_since b h (Suc n\<^sub>0) n\<close>
proof (induction n arbitrary: n\<^sub>0 rule: nat_strong_induct)
  case 0 thus ?case by simp
next
  case (Suc k)
    from Suc.prems(1) and btn_btn0 have
      *:\<open>\<exists>m. has_first_since a b h 0 (Suc k)
           \<or> has_first_since b a h 0 (Suc k)
           \<or> (have_both_ticked a b h m \<and>
               (has_first_since a b h (Suc m) (Suc k) \<or> has_first_since b a h (Suc m) (Suc k))
             )\<close> by blast
    let ?S = \<open>{m. have_both_ticked a b h m
               \<and> (has_first_since a b h (Suc m) (Suc k) \<or> has_first_since b a h (Suc m) (Suc k))}\<close>
    from Suc.prems(2,3) have \<open>\<not>first_tick_since b h 0 (Suc k)\<close>
      using has_ticked_since_later hbt_htb ht_nft less_Suc_eq_le by blast
    moreover from Suc.prems(2,3) have \<open>\<not>first_tick_since a h 0 (Suc k)\<close>
      using has_ticked_since_later hbt_hta ht_nft less_Suc_eq_le by blast
    moreover have \<open>\<not>has_first_since b a h 0 (Suc k)\<close>
      by (simp add: calculation(2) has_first_since_def)
    moreover have \<open>\<not>has_first_since a b h 0 (Suc k)\<close>
      by (simp add: calculation(1) has_first_since_def)
    ultimately have s_not_empty:\<open>?S \<noteq> {}\<close> using * by simp
    have \<open>has_ticked_since a h (Suc n\<^sub>0) (Suc k) \<and> has_ticked_since b h (Suc n\<^sub>0) (Suc k)\<close>
    proof (cases \<open>\<forall>m \<in> ?S. m < n\<^sub>0\<close>)
      case True \<comment> \<open> Impossible case \<close>
        with True Suc.prems Suc.IH have
          mht:\<open>\<forall>m\<in>?S. has_ticked_since a h (Suc m) n\<^sub>0 \<and> has_ticked_since b h (Suc m) n\<^sub>0\<close> by simp
        have nft:
          \<open>\<forall>m \<in> ?S. \<not>first_tick_since a h (Suc m) (Suc k) \<and> \<not>first_tick_since b h (Suc m) (Suc k)\<close>
        proof -
          { fix m assume mS:\<open>m \<in> ?S\<close>
            with mht have \<open>has_ticked_since a h (Suc m) n\<^sub>0\<close> by simp
            with Suc.prems(3) have \<open>has_ticked_since a h (Suc m) k\<close>
              by (simp add:has_ticked_since_later)
            hence \<open>\<not>first_tick_since a h (Suc m) (Suc k)\<close> by (rule ht_nft)
            moreover from mS mht have \<open>has_ticked_since b h (Suc m) n\<^sub>0\<close> by simp
            with Suc.prems(3) have \<open>has_ticked_since b h (Suc m) k\<close>
              by (simp add:has_ticked_since_later)
            hence \<open>\<not>first_tick_since b h (Suc m) (Suc k)\<close> by (rule ht_nft)
            ultimately have
              \<open>\<not>first_tick_since a h (Suc m) (Suc k) \<and> \<not>first_tick_since b h (Suc m) (Suc k)\<close>
            by simp
          }
          thus ?thesis ..
        qed

        have False
        proof -
          { fix m assume mS:\<open>m\<in>?S\<close>
            with nft have
              \<open>\<not>first_tick_since a h (Suc m) (Suc k) \<and> \<not>first_tick_since b h (Suc m) (Suc k)\<close>
            by blast
            moreover from mS have
              \<open>have_both_ticked a b h m \<and>
              (has_first_since a b h (Suc m) (Suc k)
                \<or> has_first_since b a h (Suc m) (Suc k))\<close> by simp
            hence
              \<open>first_tick_since a h (Suc m) (Suc k) \<or> first_tick_since b h (Suc m) (Suc k)\<close>
            unfolding has_first_since_def by auto
            ultimately have False by simp
          }
          with s_not_empty show ?thesis by blast
        qed 
        thus ?thesis ..
    next
      case False
        hence \<open>\<exists>m \<in> ?S. m\<ge>n\<^sub>0\<close> by auto
        from this obtain m where mprop:\<open>m\<in>?S \<and> m \<ge>n\<^sub>0\<close> by blast
        hence \<open>has_first_since a b h (Suc m) (Suc k)
             \<or> has_first_since b a h (Suc m) (Suc k)\<close> by simp
        with hft_ht[of \<open>a\<close> \<open>b\<close> \<open>h\<close> \<open>Suc m\<close> \<open>Suc k\<close>]
             hft_ht[of \<open>b\<close> \<open>a\<close> \<open>h\<close> \<open>Suc m\<close> \<open>Suc k\<close>] have
          \<open>(has_ticked_since a h (Suc m) (Suc k) \<and> has_ticked_since b h (Suc m) (Suc k))
         \<or> (has_ticked_since b h (Suc m) (Suc k) \<and> has_ticked_since a h (Suc m) (Suc k))\<close>
        by blast
        hence \<open>has_ticked_since a h (Suc m) (Suc k) \<and> has_ticked_since b h (Suc m) (Suc k)\<close>
          by blast
        hence htsa:\<open>has_ticked_since a h (Suc m) (Suc k)\<close> 
        and   htsb:\<open>has_ticked_since b h (Suc m) (Suc k)\<close> by simp+
        from mprop have \<open>n\<^sub>0 \<le> m\<close> by simp
        hence \<open>Suc n\<^sub>0 \<le> Suc m\<close> by simp
        from has_ticked_since_earlier[OF htsa this]
             has_ticked_since_earlier[OF htsb this] show ?thesis ..
    qed
    with Suc.IH show ?case by simp
qed

(* Same proof with the less practical nat_less_induct induction rule *)
lemma \<open>\<lbrakk>have_both_ticked a b h n; have_both_ticked a b h n\<^sub>0; n > n\<^sub>0 \<rbrakk>
    \<Longrightarrow> has_ticked_since a h (Suc n\<^sub>0) n \<and> has_ticked_since b h (Suc n\<^sub>0) n\<close>
proof (induction n arbitrary: n\<^sub>0 rule: nat_less_induct)
  case (1 n) print_facts
    from "1.prems"(3) have \<open>0 < n\<close> by simp
    hence \<open>\<exists>n\<^sub>1. Suc n\<^sub>1 = n\<close> by presburger
    from this obtain n\<^sub>1 where n1prop:\<open>Suc n\<^sub>1 = n\<close> by blast
    with "1.prems"(3) have n1prop':\<open>n\<^sub>0 \<le> n\<^sub>1\<close> by simp
    from "1.prems"(1) and btn_btn0 have
      *:\<open>\<exists>m. has_first_since a b h 0 n
           \<or> has_first_since b a h 0 n
           \<or> (have_both_ticked a b h m \<and>
               (has_first_since a b h (Suc m) n \<or> has_first_since b a h (Suc m) n)
             )\<close> by blast
    let ?S = \<open>{m. have_both_ticked a b h m
               \<and> (has_first_since a b h (Suc m) n \<or> has_first_since b a h (Suc m) n)}\<close>
    from ht_nft[OF has_ticked_since_later[OF hbt_htb[OF "1.prems"(2)] n1prop']]
      have \<open>\<not>first_tick_since b h 0 n\<close> using n1prop by simp
    moreover from ht_nft[OF has_ticked_since_later[OF hbt_hta[OF "1.prems"(2)] n1prop']]
      have \<open>\<not>first_tick_since a h 0 n\<close> using n1prop by simp
    moreover have \<open>\<not>has_first_since a b h 0 n\<close> by (simp add: calculation(1) has_first_since_def)
    moreover have \<open>\<not>has_first_since b a h 0 n\<close> by (simp add: calculation(2) has_first_since_def)
    ultimately have s_not_empty:\<open>?S \<noteq> {}\<close> using * by simp
    have \<open>has_ticked_since a h (Suc n\<^sub>0) n \<and> has_ticked_since b h (Suc n\<^sub>0) n\<close>
    proof (cases \<open>\<forall>m \<in> ?S. m < n\<^sub>0\<close>)
      case True \<comment> \<open> Impossible case \<close>
        with True "1.prems" "1.IH" have
          mht:\<open>\<forall>m\<in>?S. has_ticked_since a h (Suc m) n\<^sub>0 \<and> has_ticked_since b h (Suc m) n\<^sub>0\<close> by simp
        have
          nft:\<open>\<forall>m \<in> ?S. \<not>first_tick_since a h (Suc m) n \<and> \<not>first_tick_since b h (Suc m) n\<close>
        proof -
          { fix m assume mS:\<open>m \<in> ?S\<close>
            with mht have \<open>has_ticked_since a h (Suc m) n\<^sub>0\<close> by simp
            \<comment> \<open> This part is awkward because of the form of the induction rule 
               which gives P n instead of P (Suc n) \<close>
            with "1.prems"(3) have \<open>has_ticked_since a h (Suc m) (n - 1)\<close>
              by (simp add:has_ticked_since_later)
            hence \<open>\<not>first_tick_since a h (Suc m) n\<close> using ht_nft "1.prems"(3) by fastforce
            moreover from mS mht have \<open>has_ticked_since b h (Suc m) n\<^sub>0\<close> by simp
            with "1.prems"(3) have \<open>has_ticked_since b h (Suc m) (n - 1)\<close>
              by (simp add:has_ticked_since_later)
            hence \<open>\<not>first_tick_since b h (Suc m) n\<close> using ht_nft "1.prems"(3) by fastforce
            ultimately have \<open>\<not>first_tick_since a h (Suc m) n \<and> \<not>first_tick_since b h (Suc m) n\<close>
              by simp
          }
          thus ?thesis ..
        qed
        have False
        proof -
          { fix m assume mS:\<open>m\<in>?S\<close>
            with nft have \<open>\<not>first_tick_since a h (Suc m) n \<and> \<not>first_tick_since b h (Suc m) n\<close>
              by blast
            moreover from mS have
              \<open>have_both_ticked a b h m \<and>
              (has_first_since a b h (Suc m) n
                \<or> has_first_since b a h (Suc m) n)\<close> by simp
            hence
              \<open>first_tick_since a h (Suc m) n \<or> first_tick_since b h (Suc m) n\<close>
            unfolding has_first_since_def by auto
            ultimately have False by simp
          }
          with s_not_empty show ?thesis by blast
        qed 
        thus ?thesis ..
    next
      case False
        hence \<open>\<exists>m \<in> ?S. m\<ge>n\<^sub>0\<close> by auto
        from this obtain m where mprop:\<open>m\<in>?S \<and> m \<ge>n\<^sub>0\<close> by blast
        hence \<open>has_first_since a b h (Suc m) n \<or> has_first_since b a h (Suc m) n\<close> by simp
        with hft_ht[of \<open>a\<close> \<open>b\<close> \<open>h\<close> \<open>Suc m\<close> \<open>n\<close>]
             hft_ht[of \<open>b\<close> \<open>a\<close> \<open>h\<close> \<open>Suc m\<close> \<open>n\<close>] have
          \<open>(has_ticked_since a h (Suc m) n \<and> has_ticked_since b h (Suc m) n)
         \<or> (has_ticked_since b h (Suc m) n \<and> has_ticked_since a h (Suc m) n)\<close>
        by blast
        hence \<open>has_ticked_since a h (Suc m) n \<and> has_ticked_since b h (Suc m) n\<close> by blast
        hence htsa:\<open>has_ticked_since a h (Suc m) n\<close> 
        and   htsb:\<open>has_ticked_since b h (Suc m) n\<close> by simp+
        from mprop have \<open>n\<^sub>0 \<le> m\<close> by simp
        hence \<open>Suc n\<^sub>0 \<le> Suc m\<close> by simp
        from has_ticked_since_earlier[OF htsa this]
             has_ticked_since_earlier[OF htsb this] show ?thesis ..
    qed
    with "1.IH" show ?case by simp
qed

text \<open>
  Two useful corollaries of the previous theorem:
  When two clocks have both ticked at an instant, they cannot both tick again
  unless each of them ticks after this instant.
\<close>
corollary nhtsa:
  assumes \<open>have_both_ticked a b h n\<^sub>0\<close>
      and \<open>n > n\<^sub>0\<close>
      and \<open>\<not>has_ticked_since a h (Suc n\<^sub>0) n\<close>
    shows \<open>\<not>have_both_ticked a b h n\<close>
using assms hbt_hts by blast

corollary nhtsb:
  assumes \<open>have_both_ticked a b h n\<^sub>0\<close>
      and \<open>n > n\<^sub>0\<close>
      and \<open>\<not>has_ticked_since b h (Suc n\<^sub>0) n\<close>
    shows \<open>\<not>have_both_ticked a b h n\<close>
using assms hbt_hts by blast

text \<open>
  between a b h n
  Tell at instant n whether we are still waiting for a tick on b
  since the last tick of a on hamlet h.
\<close>
definition between :: \<open>('\<AA>::orderedrank,'a)\<H> \<Rightarrow> ('\<AA>,'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> bool\<close>
where
  \<open>between a b h n \<equiv> (\<exists>m < n. (ticks a (h m) \<and> (\<forall>k. m \<le> k \<and> k < n \<longrightarrow> \<not>ticks b (h k))))\<close>

text \<open>
  Same, defined as a function.
\<close>
fun between_fun :: \<open>('\<AA>::orderedrank,'a)\<H> \<Rightarrow> ('\<AA>,'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> bool\<close>
where
  \<open>between_fun a b h 0 = False\<close>
| \<open>between_fun a b h (Suc n) = (\<not>ticks b (h n) \<and> (between_fun a b h n \<or> ticks a (h n)))\<close>

text \<open>
  Same, defined as an inductive predicate.
\<close>
inductive between_ind :: \<open>('\<AA>::orderedrank,'a)\<H> \<Rightarrow> ('\<AA>,'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> bool\<close>
where
  \<open>\<lbrakk>between_ind a b h n; \<not>ticks b (h n)\<rbrakk> \<Longrightarrow> between_ind a b h (Suc n)\<close>
| \<open>\<lbrakk>ticks a (h n); \<not>ticks b (h n)\<rbrakk> \<Longrightarrow> between_ind a b h (Suc n)\<close>

inductive_cases btwn[elim!]:\<open>between_ind a b h (Suc n)\<close>

text \<open>
  The function and the inductive predicate are equivalent.
\<close>
lemma between_ind_is_fun:\<open>between_ind a b h n = between_fun a b h n\<close>
proof (induction n)
  case 0 thus ?case
    using between_fun.simps(1) between_ind.cases by blast
next
  case (Suc k) thus ?case
    using between_ind.intros(1,2) between_fun.simps(2) by blast
qed

text \<open>
  The definition and the inductive predicate are equivalent.
\<close>
lemma between_is_ind:\<open>between a b h n = between_ind a b h n\<close>
proof (induction n rule: nat_strong_induct)
  case 0
    have \<open>between a b h 0 = False\<close> by (simp add: between_def)
    moreover have \<open>between_ind a b h 0 = False\<close> using between_ind.cases by blast
    ultimately show ?case by simp
next
  case (Suc p)
    show ?case
    proof
      assume \<open>between a b h (Suc p)\<close>
      hence \<open>\<exists>m < Suc p. (ticks a (h m) \<and> (\<forall>k. m \<le> k \<and> k < Suc p \<longrightarrow> \<not>ticks b (h k)))\<close>
        by (simp add: between_def)
      from this obtain m where
        mprop:\<open>m < Suc p \<and> (ticks a (h m) \<and> (\<forall>k. m \<le> k \<and> k < Suc p \<longrightarrow> \<not>ticks b (h k)))\<close>
      by blast
      hence ntb:\<open>\<not>ticks b (h p)\<close> by simp
      show \<open>between_ind a b h (Suc p)\<close>
      proof (cases \<open>m = p\<close>)
        case True
          hence \<open>ticks a (h p)\<close> using mprop by blast
          with ntb show ?thesis using between_ind.intros(2) by blast
      next
        case False
          hence \<open>m < p\<close> using mprop by simp
          hence \<open>between a b h p\<close> unfolding between_def using mprop by auto
          hence \<open>between_ind a b h p\<close> using Suc.IH by simp
          with ntb show ?thesis using between_ind.intros(1) by blast
      qed
  next
      assume \<open>between_ind a b h (Suc p)\<close>
      hence \<open>\<not>ticks b (h p) \<and> (between_ind a b h p \<or> ticks a (h p))\<close> by auto
      hence *:\<open>\<not>ticks b (h p) \<and> (between a b h p \<or> ticks a (h p))\<close> using Suc.IH by simp
      thus \<open>between a b h (Suc p)\<close>
      proof (cases \<open>ticks a (h p)\<close>)
        case True thus \<open>between a b h (Suc p)\<close> unfolding between_def
                        using * le_less_Suc_eq by auto
      next
        case False 
        with * have \<open>between a b h p\<close> by simp
        moreover from * have \<open>\<not> ticks b (h p)\<close> by simp
        ultimately show \<open>between a b h (Suc p)\<close> unfolding between_def using less_Suc_eq by auto
      qed
  qed
qed

text \<open>
  The definition and the function are equivalent.
\<close>
lemma between_is_fun[code]:
  \<open>between a b h n = between_fun a b h n\<close>
proof (induction n rule: nat_strong_induct)
  case 0 thus ?case using between_def between_fun.simps(1) by blast
next
  case (Suc p)
    from between_fun.simps(2) Suc.IH
      have \<open>between_fun a b h (Suc p) = (\<not>ticks b (h p) \<and> (between a b h p \<or> ticks a (h p)))\<close>
        by simp
    also have \<open>... = between a b h (Suc p)\<close>
    proof (cases \<open>ticks b (h p)\<close>)
      case True thus ?thesis unfolding between_def using less_Suc_eq_le by blast
    next
      case False thus ?thesis unfolding between_def using less_Suc_eq by auto
    qed
    finally show ?case ..
qed

end
