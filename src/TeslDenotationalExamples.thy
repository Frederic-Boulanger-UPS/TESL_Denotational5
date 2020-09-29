theory TeslDenotationalExamples

imports TeslDenotationalRelations

begin

term \<open>\<top> \<otimes> ((fst,0) implies (snd,1))\<close>

typ \<open>'c::semiring\<close>

text\<open> An example with a non-homogeneous semantic universe
 The accessors for the clocks must be defined according to the number of clocks in the spec
   - the ith clock is accessed by fst\<circ>snd^i if it is not the last clock in the spec
   - the ith clock is accessed by snd^i if it is the last one in the spec
\<close>
abbreviation \<open>C\<^sub>1 \<equiv> (fst,0::nat)\<close>
abbreviation \<open>C\<^sub>2 \<equiv> (fst o snd,1::nat)\<close>         \<comment> \<open> second clock of more than two clocks \<close>
abbreviation \<open>C\<^sub>2\<^sub>l \<equiv> (snd,1::nat)\<close>              \<comment> \<open> second of two clocks \<close>
abbreviation \<open>C\<^sub>3 \<equiv> (fst \<circ> snd o snd,2::nat)\<close>   \<comment> \<open> Third clock of more than three clocks \<close>
abbreviation \<open>C\<^sub>3\<^sub>l \<equiv> (snd o snd,2::nat)\<close>        \<comment> \<open> Third clock of three clocks \<close>
abbreviation \<open>C\<^sub>4 \<equiv> (fst \<circ> snd \<circ> snd o snd,3::nat)\<close>
abbreviation \<open>C\<^sub>4\<^sub>l \<equiv> (snd \<circ> snd o snd,3::nat)\<close>


term \<open>C\<^sub>1 implies C\<^sub>2\<close>
term \<open>(C\<^sub>1 implies C\<^sub>2 ) \<otimes> (C\<^sub>1 sporadic (3::int)) \<otimes> (C\<^sub>2 sporadic (2::real))  \<otimes> (C\<^sub>3\<^sub>l sporadic ((2::nat,X)))\<close>


text\<open> An example with a homogeneous semantic universe and a tag-relation on real numbers ... \<close> 

term \<open>\<top> \<otimes> (C\<^sub>1 implies C\<^sub>2\<^sub>l)
        \<otimes> (C\<^sub>1 sporadic (3::real)) 
        \<otimes> (C\<^sub>2\<^sub>l sporadic (2))
        \<otimes> (tag relation C\<^sub>1 = 2 * C\<^sub>2\<^sub>l + 0)\<close>

text \<open>
  Show that 1 1 1 1 1 1 ...
            2 2 2 2 2 2 ...
            T F F F F F ...
  is a valid run for \<^theory_text>\<open>(D\<^sub>1 implies D\<^sub>2) \<otimes> (tag relation D\<^sub>2 = (2, 0) D\<^sub>1)\<close>
\<close>
abbreviation spec1 where \<open>spec1 \<equiv> (C\<^sub>1 implies C\<^sub>2\<^sub>l) \<otimes> (tag relation C\<^sub>2\<^sub>l = (2, 0) C\<^sub>1)\<close>
abbreviation time1::\<open>nat \<Rightarrow> int \<times> int\<close> where \<open>time1 \<equiv> \<lambda>n. (1, 2)\<close>
abbreviation hamlet1::\<open>nat \<Rightarrow> bool list\<close> where \<open>hamlet1 == (\<lambda>n. [False, False])(0:=[True, True])\<close>
abbreviation run1 where \<open>run1 \<equiv> Abs_run (time1, hamlet1)\<close>

lemma run_rep1:\<open>run_rep_prop time1 hamlet1\<close>
unfolding run_rep_prop_def by (simp add: monoI rank_int_def rank_prod_def)

term \<open>fst\<^sub>r\<^sub>u\<^sub>n run1\<close>
term \<open>fst\<^sub>r\<^sub>u\<^sub>n ` spec1\<close>

lemma \<open>run1 \<in> spec1\<close>
proof -
  \<comment> \<open> Implication \<close>
  have \<open>hamlet run1 = hamlet1\<close> using run_rep1 by (simp add: Abs_run_inverse hamlet_def)
  moreover have \<open>\<forall>n. ticks C\<^sub>1 (hamlet1 n) \<longrightarrow> ticks C\<^sub>2\<^sub>l (hamlet1 n)\<close> unfolding ticks_def by simp
  ultimately have imp:\<open>run1 \<in> (C\<^sub>1 implies C\<^sub>2\<^sub>l)\<close> unfolding Implies_def by simp
  \<comment> \<open> Tag relation \<close>
  have \<open>time run1 = time1\<close> using run_rep1  by (simp add: Abs_run_inverse time_def)
  moreover have \<open>mono time1\<close> by (simp add: monoI)
  moreover have \<open>(\<forall>n. (timep C\<^sub>2\<^sub>l (time1 n), timep C\<^sub>1 (time1 n)) \<in> {(m::int, n::int). m = 2 * n + 0 \<or> n = (m - 0) div 2})\<close> by simp
  ultimately have tagrel:\<open>run1 \<in> (tag relation C\<^sub>2\<^sub>l = (2, 0) C\<^sub>1)\<close> unfolding TagRelation_def AffineTagRelation\<^sub>i\<^sub>n\<^sub>t.simps time_def by simp
  \<comment> \<open> Final result \<close>
  from imp and tagrel show ?thesis using TeslComp_def by blast
qed

\<comment> \<open> A spec with a more complex time function \<close>
abbreviation \<open>spec2 \<equiv> (C\<^sub>1 implies C\<^sub>2\<^sub>l) \<otimes> (tag relation C\<^sub>2\<^sub>l = (2, 0) C\<^sub>1)\<close>
abbreviation \<open>time2 \<equiv> \<lambda>n::nat. (int n, int 2*n)\<close>
abbreviation \<open>hamlet2 \<equiv> (\<lambda>n::nat. [False, False])(0:=[True, True])\<close>
abbreviation \<open>run2 \<equiv> Abs_run (time2, hamlet2)\<close>

lemma mono_time2:\<open>mono time2\<close>
proof -
  {
    fix m n::nat
    assume \<open>m \<le> n\<close>
    hence \<open>(int m, int 2*m) \<le> (int n, int 2*n)\<close> by (simp add: less_eq_prod_def)
    hence \<open>time2 m \<le> time2 n\<close> .
  }
  thus ?thesis by (rule monoI)
qed

lemma run_rep2:\<open>run_rep_prop time2 hamlet2\<close>
unfolding run_rep_prop_def using mono_time2 by (simp add: rank_int_def rank_prod_def)

lemma \<open>run2 \<in> spec2\<close>
proof -
  \<comment> \<open> Implication \<close>
  have \<open>hamlet run2 = hamlet2\<close> using run_rep2 by (simp add: Abs_run_inverse hamlet_def)
  moreover have \<open>\<forall>n. ticks C\<^sub>1 (hamlet2 n) \<longrightarrow> ticks C\<^sub>2\<^sub>l (hamlet2 n)\<close> unfolding ticks_def by simp
  ultimately have imp:\<open>run2 \<in> (C\<^sub>1 implies C\<^sub>2\<^sub>l)\<close> unfolding Implies_def by simp
  \<comment> \<open> Tag relation \<close>
  have \<open>time run2 = time2\<close> using run_rep2 by (simp add: Abs_run_inverse time_def)
  moreover have \<open>(\<forall>n. (timep C\<^sub>2\<^sub>l (time2 n), timep C\<^sub>1 (time2 n)) \<in> {(m::int, n::int). m = 2 * n + 0 \<or> n = (m - 0) div 2})\<close> by simp
  ultimately have tagrel:\<open>run2 \<in> (tag relation C\<^sub>2\<^sub>l = (2, 0) C\<^sub>1)\<close> unfolding TagRelation_def AffineTagRelation\<^sub>i\<^sub>n\<^sub>t.simps time_def using mono_time2 by simp
  \<comment> \<open> Final result \<close>
  from imp and tagrel show ?thesis using TeslComp_def by blast
qed

\<comment> \<open> A spec with a timed delay \<close>
abbreviation \<open>spec3 \<equiv> (C\<^sub>1 implies C\<^sub>2\<^sub>l) \<otimes> (tag relation C\<^sub>2\<^sub>l = (2, 0) C\<^sub>1) \<otimes> (C\<^sub>1 time-delayed by 2 on C\<^sub>1 implies C\<^sub>2\<^sub>l)\<close>
abbreviation \<open>hamlet3 \<equiv> (\<lambda>n::nat. [False, False])(0:=[True, True],2:=[False,True])\<close>
abbreviation \<open>run3 \<equiv> Abs_run (time2, hamlet3)\<close>

lemma run_rep3:\<open>run_rep_prop time2 hamlet3\<close>
using mono_time2 by (simp add: rank_int_def rank_prod_def run_rep_prop_def)

lemma \<open>run3 \<in> spec3\<close>
proof -
  \<comment> \<open> Implication \<close>
  have ham:\<open>hamlet run3 = hamlet3\<close> using run_rep3 by (simp add: Abs_run_inverse hamlet_def)
  moreover have \<open>\<forall>n. ticks C\<^sub>1 (hamlet3 n) \<longrightarrow> ticks C\<^sub>2\<^sub>l (hamlet3 n)\<close> unfolding ticks_def by simp
  ultimately have imp:\<open>run3 \<in> (C\<^sub>1 implies C\<^sub>2\<^sub>l)\<close> unfolding Implies_def by simp
  \<comment> \<open> Tag relation \<close>
  have tim:\<open>time run3 = time2\<close> using run_rep3 by (simp add: Abs_run_inverse time_def)
  moreover have \<open>(\<forall>n. (timep C\<^sub>2\<^sub>l (time2 n), timep C\<^sub>1 (time2 n)) \<in> {(m::int, n::int). m = 2 * n + 0 \<or> n = (m - 0) div 2})\<close> by simp
  ultimately have tagrel:\<open>run3 \<in> (tag relation C\<^sub>2\<^sub>l = (2, 0) C\<^sub>1)\<close> unfolding TagRelation_def AffineTagRelation\<^sub>i\<^sub>n\<^sub>t.simps time_def using mono_time2 by simp
  \<comment> \<open> Time delay \<close>
  have c1ticks0:\<open>\<forall>n. ticks C\<^sub>1 (hamlet3 n) \<longrightarrow> n = 0\<close> unfolding ticks_def by simp
  have \<open>\<forall>n. ticks C\<^sub>1 (hamlet3 n) \<longrightarrow> (\<exists>m. m > n \<and> ticks C\<^sub>2\<^sub>l (hamlet3 m)  \<and> timep C\<^sub>1 (time2 m) = timep C\<^sub>1 (time2 n) + 2)\<close>
  proof -
    {
      fix n
      assume h:\<open>ticks C\<^sub>1 (hamlet3 n)\<close>
      have \<open>\<exists>m. m > n \<and> ticks C\<^sub>2\<^sub>l (hamlet3 m) \<and> timep C\<^sub>1 (time2 m) = timep C\<^sub>1 (time2 n) + 2\<close>
      proof -
        from h c1ticks0 have \<open>n = 0\<close> unfolding ticks_def by simp
        moreover have \<open>timep C\<^sub>1 (time2 0) = 0\<close> by simp
        moreover have \<open>ticks C\<^sub>2\<^sub>l (hamlet3 (n+2))\<close> unfolding ticks_def using `n = 0` by simp
        moreover have \<open>timep C\<^sub>1 (time2 (n + 2)) = timep C\<^sub>1 (time2 0) + 2\<close> using `n = 0` by simp
        moreover have \<open>n < n+2\<close> by simp
        ultimately have \<open>(n+2) > n \<and> ticks C\<^sub>2\<^sub>l (hamlet3 (n + 2)) \<and> timep C\<^sub>1 (time2 (n + 2)) = timep C\<^sub>1 (time2 n) + 2\<close> by simp
        thus ?thesis by blast
      qed
    }
    thus ?thesis by blast
  qed
  with tim ham mono_time2 have tdelay:\<open>run3 \<in> (C\<^sub>1 time-delayed by 2 on C\<^sub>1 implies C\<^sub>2\<^sub>l)\<close> unfolding TimeDelayed_def time_def hamlet_def by simp
  with imp tagrel show ?thesis using TeslComp_def by blast
qed

\<comment> \<open> A spec with a delay \<close>
abbreviation \<open>spec4 \<equiv> (tag relation C\<^sub>2 = (1, 0) C\<^sub>1) \<otimes> (tag relation C\<^sub>3\<^sub>l = (1, 0) C\<^sub>1) \<otimes> (C\<^sub>1 delayed by 2 on C\<^sub>2 implies C\<^sub>3\<^sub>l)\<close>
abbreviation \<open>hamlet4 \<equiv> (\<lambda>n::nat. [False, False, False])(0:=[True, False, False],1:=[False, True, False], 2:=[False,True,True])\<close>
abbreviation \<open>time4 \<equiv> \<lambda>n::nat. (int n, int n, int n)\<close>
abbreviation \<open>run4 \<equiv> Abs_run (time4, hamlet4)\<close>

lemma mono_time4: \<open>mono time4\<close>
proof -
  {
    fix m n::nat
    assume \<open>m \<le> n\<close>
    hence \<open>(int m, int m, int m) \<le> (int n, int n, int n)\<close> by (simp add: less_eq_prod_def)
    hence \<open>time4 m \<le> time4 n\<close> .
  }
  thus ?thesis by (rule monoI)
qed

lemma run_rep4:\<open>run_rep_prop time4 hamlet4\<close>
using mono_time4 by (simp add: rank_int_def rank_prod_def run_rep_prop_def)

lemma ham4c1:
  assumes \<open>ticks C\<^sub>1 (hamlet4 n)\<close>
  shows \<open>n = 0\<close>
proof -
  from assms have *:\<open>(hamlet4 n)!0\<close> by (simp add:ticks_def)
  have \<open>(hamlet4 0)!0\<close> by simp
  moreover have \<open>\<not> ((hamlet4 1)!0)\<close> by simp
  moreover have \<open>\<not> ((hamlet4 2)!0)\<close> by simp
  moreover have \<open>n\<noteq>0 \<and> n\<noteq>1 \<and> n\<noteq>2 \<Longrightarrow> \<not> ((hamlet4 n)!0)\<close> by simp
  ultimately have \<open>(hamlet4 n)!0 \<Longrightarrow> n = 0\<close> by blast
  with * show ?thesis by simp
qed

lemma 02:\<open>(0 < (p::nat) \<and> p \<le> 2) = (p = 1 \<or> p = 2)\<close> by auto
    
lemma T02:\<open>((0 < p \<and> p \<le> 2) \<and> ticks C\<^sub>2 (hamlet4 p)) = ((p = 1 \<or> p = 2) \<and> (ticks C\<^sub>2 (hamlet4 p)))\<close>
proof -
  have \<open>ticks C\<^sub>2 (hamlet4 1)\<close> by (simp add:ticks_def)
  moreover have \<open>ticks C\<^sub>2 (hamlet4 2)\<close> by (simp add:ticks_def)
  ultimately show ?thesis using 02 by metis
qed

lemma \<open>run4 \<in> spec4\<close>
proof -
  \<comment> \<open> Tag relations \<close>
  have tim:\<open>time run4 = time4\<close> using run_rep4 by (simp add: Abs_run_inverse time_def)
  moreover have \<open>(\<forall>n. (timep C\<^sub>2 (time4 n), timep C\<^sub>1 (time4 n)) \<in> {(m::int, n::int). m = 1 * n + 0 \<or> n = (m - 0) div 1})\<close> by simp
  ultimately have tagrel1:\<open>run4 \<in> (tag relation C\<^sub>2 = (1, 0) C\<^sub>1)\<close> unfolding TagRelation_def AffineTagRelation\<^sub>i\<^sub>n\<^sub>t.simps time_def using mono_time4 by simp
  from tim have \<open>(\<forall>n. (timep C\<^sub>3\<^sub>l (time4 n), timep C\<^sub>1 (time4 n)) \<in> {(m::int, n::int). m = 1 * n + 0 \<or> n = (m - 0) div 1})\<close> by simp
  with tim have tagrel2:\<open>run4 \<in> (tag relation C\<^sub>3\<^sub>l = (1, 0) C\<^sub>1)\<close> unfolding TagRelation_def AffineTagRelation\<^sub>i\<^sub>n\<^sub>t.simps time_def using mono_time4 by simp
  \<comment> \<open> Delayed implication \<close>
  have ham:\<open>hamlet run4 = hamlet4\<close> using run_rep4 by (simp add: Abs_run_inverse hamlet_def)
  have \<open>\<forall>n. ticks C\<^sub>1 (hamlet4 n) \<longrightarrow> (\<exists>n\<^sub>f\<^sub>i\<^sub>r\<^sub>e > n. ticks C\<^sub>3\<^sub>l (hamlet4 n\<^sub>f\<^sub>i\<^sub>r\<^sub>e) \<and> 
                                                 card {p. n < p \<and> p \<le> n\<^sub>f\<^sub>i\<^sub>r\<^sub>e \<and> 
                                                 ticks C\<^sub>2 (hamlet4 p)} = 2)\<close>
  proof -
    { fix n assume \<open>ticks C\<^sub>1 (hamlet4 n)\<close>
      hence n0:\<open>n=0\<close> using ham4c1 by simp
      have t:\<open>ticks C\<^sub>3\<^sub>l (hamlet4 2)\<close> by (simp add:ticks_def)
      have \<open>ticks C\<^sub>2 (hamlet4 1)\<close> by (simp add:ticks_def)
      moreover have \<open>ticks C\<^sub>2 (hamlet4 2)\<close> by (simp add:ticks_def)
      ultimately have \<open>{p. (p=1 \<or> p = 2) \<and> ticks C\<^sub>2 (hamlet4 p)} = {1, 2}\<close> by auto
      with T02 have *:\<open>{p. 0 < p \<and> p \<le> 2 \<and> ticks C\<^sub>2 (hamlet4 p)} = {1, 2}\<close> using arg_cong by blast
      from arg_cong[OF this, of \<open>card\<close>] have \<open>card {p. 0 < p \<and> p \<le> 2 \<and> ticks C\<^sub>2 (hamlet4 p)} = card {(1::nat), 2}\<close> .
      also have \<open>... = 2\<close> by simp
      finally have \<open>card {p. 0 < p \<and> p \<le> 2 \<and> ticks C\<^sub>2 (hamlet4 p)} = 2\<close> by simp
      with t have \<open>2 > n \<and> ticks C\<^sub>3\<^sub>l (hamlet4 2) \<and> card {p. 0 < p \<and> p \<le> 2 \<and> ticks C\<^sub>2 (hamlet4 p)} = 2\<close> using n0 by simp
    }
    thus ?thesis by (metis (no_types, lifting) Collect_cong ham4c1)
  qed
  with tim ham have delay:\<open>run4 \<in> (C\<^sub>1 delayed by 2 on C\<^sub>2 implies C\<^sub>3\<^sub>l)\<close> unfolding Delayed_def using time_def by (simp add:tick_count_between_def)
  from tagrel1 tagrel2 delay show ?thesis using TeslComp_def by blast
qed

term \<open>Least (\<lambda>X. X>(3::int))\<close>
term \<open>x mod y\<close>

term Max

abbreviation \<open>C5\<^sub>1::(nat\<times>nat, nat)\<H> \<equiv> (fst, 0::nat)\<close>
abbreviation \<open>C5\<^sub>2::(nat\<times>nat, nat)\<H> \<equiv> (snd,1::nat)\<close>              \<comment> \<open> second of two clocks \<close>

abbreviation \<open>spec5::(nat\<times>nat) run set \<equiv> (C5\<^sub>1 filtered by 1, 2 (1, 1)* implies C5\<^sub>2)\<close>
abbreviation \<open>hamlet5 \<equiv> (\<lambda>n::nat. [False, False])(0:=[True, False],1:=[True, True], 2:=[True,True], 3:=[True,False], 4:=[True,True], 5:=[True,False])\<close>
abbreviation \<open>time5 \<equiv> \<lambda>n::nat. (n, n)\<close>
abbreviation \<open>run5 \<equiv> Abs_run (time5, hamlet5)\<close>

lemma run_rep5:\<open>run_rep_prop time5 hamlet5\<close>
unfolding run_rep_prop_def
proof
  show \<open>mono time5\<close> unfolding mono_def by (simp add: less_eq_prod_def)
  have \<open>\<forall>n. rank (time5 n) = 2\<close> using rank_nat_def by (simp add: rank_prod_def)
  moreover have \<open>\<forall>n. length (hamlet5 n) = 2\<close> by simp
  ultimately show \<open>\<forall>n. rank (time5 n) = length (hamlet5 n)\<close> by simp
qed

lemma c1ticks6:
  assumes \<open>n < 6\<close>
  shows   \<open>ticks C5\<^sub>1 (hamlet5 n)\<close>
proof -
  have \<open>ticks C5\<^sub>1 (hamlet5 0)\<close> unfolding ticks_def by simp
  moreover have \<open>ticks C5\<^sub>1 (hamlet5 1)\<close> unfolding ticks_def by simp
  moreover have \<open>ticks C5\<^sub>1 (hamlet5 2)\<close> unfolding ticks_def by simp
  moreover have \<open>ticks C5\<^sub>1 (hamlet5 3)\<close> unfolding ticks_def by simp
  moreover have \<open>ticks C5\<^sub>1 (hamlet5 4)\<close> unfolding ticks_def by simp
  moreover have \<open>ticks C5\<^sub>1 (hamlet5 5)\<close> unfolding ticks_def by simp
  ultimately show ?thesis using assms by auto
qed

lemma c1notick6:
  assumes \<open>n \<ge> 6\<close>
  shows   \<open>\<not>ticks C5\<^sub>1 (hamlet5 n)\<close>
unfolding ticks_def using assms by simp

lemma n_lt_6:
  assumes \<open>(n::nat) < 6\<close>
  shows   \<open>n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5\<close>
using assms by auto

declare [[show_sorts]]

lemma c1cnt6is:
  assumes \<open>n < 6\<close>
  shows   \<open>tick_count C5\<^sub>1 hamlet5 n = (Suc n)\<close>
proof -
  from c1ticks6 assms have \<open>\<forall>i \<le> n. ticks C5\<^sub>1 (hamlet5 i)\<close> using le_less_trans by blast
  hence \<open>{i. i \<le> n \<and> ticks C5\<^sub>1 (hamlet5 i)} = {i. i \<le> n}\<close> by blast
  moreover have \<open>card {i. i \<le> n} = Suc n\<close> by simp
  ultimately show ?thesis unfolding tick_count_def by auto
qed

lemma c1cnt6:
  assumes \<open>n < 6\<close>
  shows   \<open>tick_count_fun C5\<^sub>1 hamlet5 n = Suc n\<close>
using c1cnt6is tick_count_is_fun using assms by (simp add: tick_count_is_fun)

lemma c1filt_ok:
  assumes \<open>n < 6\<close>
  shows   \<open>filter 1 2 1 1 (tick_count C5\<^sub>1 hamlet5 n) \<longrightarrow> ticks C5\<^sub>2 (hamlet5 n)\<close> (is \<open>?P n\<close>) 
proof -
  have \<open>?P 0\<close> unfolding filter_def ticks_def by eval
  moreover have \<open>?P 1\<close> unfolding filter_def ticks_def by simp
  moreover have \<open>?P 2\<close> unfolding filter_def ticks_def by simp
  moreover have \<open>?P 3\<close> unfolding filter_def ticks_def by eval
  moreover have \<open>?P 4\<close> unfolding filter_def ticks_def by eval
  moreover have \<open>?P 5\<close> unfolding filter_def ticks_def by eval
  ultimately show ?thesis using assms n_lt_6 by blast
qed

\<^cancel>\<open>
value \<open>ticks C\<^sub>1 (hamlet5 1)\<close>
value \<open>tick_count C\<^sub>1 hamlet5 1\<close>
value \<open>filter 1 2 1 1 (tick_count C\<^sub>1 hamlet5 1)\<close>
value \<open>ticks C\<^sub>2\<^sub>l (hamlet5 1)\<close>
\<close>

lemma \<open>run5 \<in> spec5\<close>
proof -
  \<comment> \<open> Filtered implication \<close>
  have ham:\<open>hamlet run5 = hamlet5\<close> using run_rep5 by (simp add: Abs_run_inverse hamlet_def)
  have \<open>\<forall>n. ticks C5\<^sub>1 (hamlet5 n) \<and> filter 1 2 1 1 (tick_count C5\<^sub>1 hamlet5 n) \<longrightarrow> ticks C5\<^sub>2 (hamlet5 n)\<close>
  proof -
    { fix n
      have \<open>ticks C5\<^sub>1 (hamlet5 n) \<and> filter 1 2 1 1 (tick_count C5\<^sub>1 hamlet5 n) \<longrightarrow> ticks C5\<^sub>2 (hamlet5 n)\<close>
      proof (cases \<open>n < 6\<close>)
        case True thus ?thesis using c1filt_ok filter_def by blast
      next
        case False thus ?thesis using c1notick6 by auto
      qed
    }
    thus ?thesis ..
  qed
  with ham show ?thesis unfolding Filtered_def by simp
qed

text \<open>
  Example specification for the await implication.
\<close>
abbreviation \<open>C6\<^sub>1::(nat\<times>nat\<times>nat, nat)\<H> \<equiv> (fst, 0::nat)\<close>
abbreviation \<open>C6\<^sub>2::(nat\<times>nat\<times>nat, nat)\<H> \<equiv> (fst \<circ> snd,1::nat)\<close>              \<comment> \<open> second of three clocks \<close>
abbreviation \<open>C6\<^sub>3::(nat\<times>nat\<times>nat, nat)\<H> \<equiv> (snd \<circ> snd,2::nat)\<close>              \<comment> \<open> third of three clocks \<close>

abbreviation \<open>spec6 \<equiv> (await C6\<^sub>1, C6\<^sub>2 implies C6\<^sub>3)\<close>
abbreviation \<open>hamlet6 \<equiv> (\<lambda>n::nat. [False, False, False])(0:=[True, False, False],1:=[False, True, True], 2:=[True,True,True], 3:=[False,True,False], 4:=[True,False,True])\<close>
abbreviation \<open>time6 \<equiv> \<lambda>n::nat. (n, n, n)\<close>
abbreviation \<open>run6 \<equiv> Abs_run (time6, hamlet6)\<close>

lemma run_rep6:\<open>run_rep_prop time6 hamlet6\<close>
unfolding run_rep_prop_def by (simp add: less_eq_prod_def monoI rank_nat_def rank_prod_def)

lemma n_lt_5:
  assumes \<open>(n::nat) < 5\<close>
  shows   \<open>n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4\<close>
using assms by auto

text \<open>
  Show that the await implication holds for all instants n < 5
\<close>
lemma awaitc1c2_ok:
  assumes \<open>n < 5\<close>
  shows   \<open>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 n \<longrightarrow> ticks C6\<^sub>3 (hamlet6 n)\<close> (is \<open>?P n\<close>) 
proof -
  \<comment> \<open> Proof at instant 0 \<close>
  have nc2_0:\<open>\<not>ticks C6\<^sub>2 (hamlet6 0)\<close> unfolding ticks_def by simp
  hence 0:\<open>?P 0\<close> using bt0_bt0 by blast
  \<comment> \<open> Proof at instant 1 \<close>
  have \<open>ticks C6\<^sub>1 (hamlet6 0)\<close> unfolding ticks_def by simp
  moreover have \<open>(0::nat) < 1\<close> by simp
  moreover have \<open>(1::nat) \<le> 1\<close> by simp
  ultimately have 11:\<open>has_ticked_since C6\<^sub>1 hamlet6 0 1\<close> unfolding has_ticked_since_def by blast
  have \<open>ticks C6\<^sub>2 (hamlet6 1)\<close> unfolding ticks_def by simp
  with nc2_0 have \<open>first_tick_since C6\<^sub>2 hamlet6 0 1\<close> unfolding first_tick_since_def by simp
  with 11 have \<open>has_first_since C6\<^sub>1 C6\<^sub>2 hamlet6 0 1\<close> by (simp add: has_first_since_def)
  hence hbt1:\<open>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 1\<close> using have_both_ticked.intros(1) by simp
  moreover have \<open>ticks C6\<^sub>3 (hamlet6 1)\<close> unfolding ticks_def by simp
  ultimately have 1:\<open>?P 1\<close> by blast
  \<comment> \<open> Proof at instant 2 \<close>
  have \<open>ticks C6\<^sub>1 (hamlet6 2)\<close> unfolding ticks_def by simp
  moreover have \<open>(Suc 1) \<le> 2\<close> by simp
  ultimately have hts12:\<open>has_ticked_since C6\<^sub>1 hamlet6 (Suc 1) 2\<close> unfolding has_ticked_since_def by blast
  have \<open>ticks C6\<^sub>2 (hamlet6 2)\<close> unfolding ticks_def by simp 
  hence \<open>first_tick_since C6\<^sub>2 hamlet6 (Suc 1) 2\<close> unfolding first_tick_since_def by auto
  with hts12 have \<open>has_first_since C6\<^sub>1 C6\<^sub>2 hamlet6 (Suc 1) 2\<close> by (simp add: has_first_since_def)
  from have_both_ticked.intros(3)[OF hbt1 this] have hbt2:\<open>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 2\<close> .
  moreover have \<open>ticks C6\<^sub>3 (hamlet6 2)\<close> unfolding ticks_def by simp
  ultimately have 2:\<open>?P 2\<close> by blast
  \<comment> \<open> Proof at instant 3 \<close>
  have \<open>\<not>ticks C6\<^sub>1 (hamlet6 3)\<close> unfolding ticks_def by simp
  hence nht13:\<open>\<not>has_ticked_since C6\<^sub>1 hamlet6 (Suc 2) 3\<close> unfolding has_ticked_since_def by auto
  with nhtsa[OF hbt2, of 3] have \<open>\<not>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 3\<close> by auto
  hence 3:\<open>?P 3\<close> by blast
  \<comment> \<open> Proof at instant 4 \<close>
  have \<open>ticks C6\<^sub>2 (hamlet6 3)\<close> by (simp add: ticks_def)
  moreover have \<open>(Suc 2) \<le> 3\<close> by simp
  moreover have \<open>(3::nat) \<le> 4\<close> by simp
  ultimately have hts24:\<open>has_ticked_since C6\<^sub>2 hamlet6 (Suc 2) 4\<close> using has_ticked_since_def by blast
  have \<open>ticks C6\<^sub>1 (hamlet6 4)\<close> by (simp add:ticks_def)
  moreover have \<open>\<not>ticks C6\<^sub>1 (hamlet6 (Suc 2))\<close> by (simp add:ticks_def)
  ultimately have fts24:\<open>first_tick_since C6\<^sub>1 hamlet6 (Suc 2) 4\<close> unfolding first_tick_since_def by auto
  with hbt2 hts24 have \<open>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 4\<close> using have_both_ticked.intros(4)
    using has_first_since_def by blast
  moreover have \<open>ticks C6\<^sub>3 (hamlet6 4)\<close> by (simp add:ticks_def)
  ultimately have 4:\<open>?P 4\<close> by blast
  \<comment> \<open> Conclusion \<close>
  from 0 1 2 3 4 show ?thesis using n_lt_5[OF assms] by blast
qed

text \<open>
  Show that C1 and C2 do not both tick after instant 5.
\<close>
lemma c1notick5:
  assumes \<open>n \<ge> 5\<close>
    shows \<open>\<not>ticks C6\<^sub>1 (hamlet6 n)\<close>
unfolding ticks_def using assms by simp

lemma c2notick5:
  assumes \<open>n \<ge> 5\<close>
    shows \<open>\<not>ticks C6\<^sub>2 (hamlet6 n)\<close>
unfolding ticks_def using assms by simp

lemma nohbt125:
  assumes \<open>n \<ge> 5\<close>
    shows \<open>\<not>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 n\<close>
using c1notick5 c2notick5 assms hbt_t by blast

text \<open>
  Finally, show that the run satisfies the specification.
\<close>
lemma \<open>run6 \<in> spec6\<close>
proof -
  \<comment> \<open>Await implication\<close>
  have ham:\<open>hamlet run6 = hamlet6\<close> using run_rep6 by (simp add: Abs_run_inverse hamlet_def)
  have \<open>\<forall>n. have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 n \<longrightarrow> ticks C6\<^sub>3 (hamlet6 n)\<close>
  proof -
    { fix n
      have \<open>have_both_ticked C6\<^sub>1 C6\<^sub>2 hamlet6 n \<longrightarrow> ticks C6\<^sub>3 (hamlet6 n)\<close>
      proof (cases \<open>n < 5\<close>)
        case True thus ?thesis using awaitc1c2_ok by blast
      next
        case False
          hence \<open>n \<ge> 5\<close> by simp
          from nohbt125[OF this] show ?thesis by blast 
      qed
    }
    thus ?thesis ..
  qed
  with ham show ?thesis unfolding Await_def by simp
qed

abbreviation \<open>spec7 \<equiv> (C\<^sub>1 sustained from C\<^sub>2 to C\<^sub>3 implies C\<^sub>4\<^sub>l)\<close>
abbreviation \<open>hamlet7 \<equiv> (\<lambda>n::nat. [False, False, False, False])
  (0:=[True, False, False, False],
   1:=[True, True,  False, False],
   2:=[True, False, False, True],
   3:=[True, False, True,  True],
   4:=[True, False, False, False])\<close>
abbreviation \<open>time7 \<equiv> \<lambda>n::nat. (n, n, n, n)\<close>
abbreviation \<open>run7 \<equiv> Abs_run (time7, hamlet7)\<close>

lemma run_rep7:\<open>run_rep_prop time7 hamlet7\<close>
unfolding run_rep_prop_def by (simp add: less_eq_prod_def monoI rank_nat_def rank_prod_def)

lemma \<open>run7 \<in> spec7\<close>
proof -
  have ham:\<open>hamlet run7 = hamlet7\<close> using run_rep7 by (simp add: Abs_run_inverse hamlet_def)
  have \<open>\<forall>n. between C\<^sub>2 C\<^sub>3 hamlet7 n \<and> ticks C\<^sub>1 (hamlet7 n) \<longrightarrow> ticks C\<^sub>4\<^sub>l (hamlet7 n)\<close>(is \<open>\<forall>n. ?P n\<close>)
  proof -
    { fix n::nat
      have \<open>?P n\<close>
      proof (cases \<open>n < 5\<close>)
        case True
          have nb0:\<open>\<not>between C\<^sub>2 C\<^sub>3 hamlet7 0\<close> using between_def by blast
          hence 0:\<open>?P 0\<close> by auto
          have \<open>\<not>ticks C\<^sub>2 (hamlet7 0)\<close> unfolding ticks_def by simp
          with nb0 have \<open>\<not>between C\<^sub>2 C\<^sub>3 hamlet7 (Suc 0)\<close> using between_def by blast
          hence nb1:\<open>\<not>between C\<^sub>2 C\<^sub>3 hamlet7 1\<close> by simp
          hence 1:\<open>?P 1\<close> by blast
          have \<open>ticks C\<^sub>2 (hamlet7 1)\<close> unfolding ticks_def by simp
          moreover have \<open>\<not>ticks C\<^sub>3 (hamlet7 1)\<close> unfolding ticks_def by simp
          ultimately have \<open>between C\<^sub>2 C\<^sub>3 hamlet7 (Suc 1)\<close> using between_is_ind between_ind.intros(2) by blast
          hence bt2:\<open>between C\<^sub>2 C\<^sub>3 hamlet7 2\<close> using Num.Suc_1 by metis \<comment> \<open> ??? \<close>
          have \<open>ticks C\<^sub>4\<^sub>l (hamlet7 2)\<close> unfolding ticks_def by simp
          hence 2:\<open>?P 2\<close> by blast
          have \<open>\<not>ticks C\<^sub>3 (hamlet7 2)\<close> unfolding ticks_def by simp
          with bt2 have \<open>between C\<^sub>2 C\<^sub>3 hamlet7 (Suc 2)\<close> using between_is_ind between_ind.intros(1) by blast
          hence bt3:\<open>between C\<^sub>2 C\<^sub>3 hamlet7 3\<close> by simp
          have \<open>ticks C\<^sub>4\<^sub>l (hamlet7 3)\<close> unfolding ticks_def by simp
          hence 3:\<open>?P 3\<close> by blast
          have \<open>ticks C\<^sub>3 (hamlet7 3)\<close> unfolding ticks_def by simp
          hence \<open>\<not>between C\<^sub>2 C\<^sub>3 hamlet7 (Suc 3)\<close> using between_is_ind between_ind.intros(2) by blast
          hence \<open>\<not>between C\<^sub>2 C\<^sub>3 hamlet7 4\<close> by simp
          hence 4:\<open>?P 4\<close> by blast
          from 0 1 2 3 4 n_lt_5[OF True] show ?thesis by blast
      next
        case False
          hence \<open>\<not>ticks C\<^sub>1 (hamlet7 n)\<close> unfolding ticks_def by simp
          thus ?thesis by auto
      qed
    }
    thus ?thesis ..
  qed
  thus ?thesis unfolding SustainFromTo_def using ham by simp
qed

end
