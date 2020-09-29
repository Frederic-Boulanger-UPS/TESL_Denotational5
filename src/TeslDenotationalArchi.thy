theory TeslDenotationalArchi

imports TeslDenotationalRelations

begin
section \<open>
  Preservation of the TESL operators by architectural composition
\<close>

text \<open>
  The tick_occurs operator is preserved in a product of runs.
\<close>
lemma tick_occurs_prod:\<open>tick_occurs (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)
                      = (tick_occurs (hamlet r\<^sub>1 n) \<or> tick_occurs (hamlet r\<^sub>2 n))\<close>
unfolding tick_occurs_def hamlet_prod_hamlet by auto

lemma tick_occurs_prod1[intro]:\<open>tick_occurs (hamlet r\<^sub>1 n) \<Longrightarrow> tick_occurs (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
using tick_occurs_prod[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close> \<open>n\<close>] by simp

lemma tick_occurs_prod2[intro]:\<open>tick_occurs (hamlet r\<^sub>2 n) \<Longrightarrow> tick_occurs (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
using tick_occurs_prod[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close> \<open>n\<close>] by simp

lemma tick_occurs_prode[elim]:
  \<open>tick_occurs (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n) \<Longrightarrow> (tick_occurs (hamlet r\<^sub>1 n) \<or> tick_occurs (hamlet r\<^sub>2 n))\<close>
using tick_occurs_prod[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close> \<open>n\<close>] by simp

text \<open>
  The tick_occurs operator is preserved by projection.
\<close>
lemma tick_occurs_proj:
  \<open>tick_occurs (hamlet r n) = (  tick_occurs (hamlet (fst\<^sub>r\<^sub>u\<^sub>n r) n)
                               \<or> tick_occurs (hamlet (snd\<^sub>r\<^sub>u\<^sub>n r) n))\<close>
using tick_occurs_prod[of \<open>fst\<^sub>r\<^sub>u\<^sub>n r\<close> \<open>snd\<^sub>r\<^sub>u\<^sub>n r\<close> \<open>n\<close>]
      hamlet_fst_hamlet[of \<open>r\<close>]
      hamlet_snd_hamlet[of \<open>r\<close>]
      hamlet_prod_hamlet[of \<open>fst\<^sub>r\<^sub>u\<^sub>n r\<close> \<open>snd\<^sub>r\<^sub>u\<^sub>n r\<close>]
by auto

lemma tick_occurs_proj1[intro]:
  \<open>tick_occurs (hamlet (fst\<^sub>r\<^sub>u\<^sub>n r) n) \<Longrightarrow> tick_occurs (hamlet r n)\<close>
using tick_occurs_proj[of \<open>r\<close> \<open>n\<close>] by simp

lemma tick_occurs_proj2[intro]:
  \<open>tick_occurs (hamlet (snd\<^sub>r\<^sub>u\<^sub>n r) n) \<Longrightarrow> tick_occurs (hamlet r n)\<close>
using tick_occurs_proj[of \<open>r\<close> \<open>n\<close>] by simp

lemma tick_occurs_proje[elim]:
  \<open>tick_occurs (hamlet r n) \<Longrightarrow> (  tick_occurs (hamlet (fst\<^sub>r\<^sub>u\<^sub>n r) n)
                                 \<or> tick_occurs (hamlet (snd\<^sub>r\<^sub>u\<^sub>n r) n))\<close>
using tick_occurs_proj[of \<open>r\<close> \<open>n\<close>] by simp

text \<open>
  Shifting a clock from a run to a product of runs.
  Third argument ('b run) is here just for typing the result...
  shift1 just changes the type of the clock,
  shift2 also offsets its time and hamlet components.
\<close>
definition shift\<^sub>1::\<open>('a, 'c)\<H> \<Rightarrow> ('a::orderedrank run) \<Rightarrow> ('b::orderedrank run) \<Rightarrow> ('a\<times>'b, 'c)\<H>\<close>
where \<open>shift\<^sub>1 c r r' \<equiv> ((timep c) \<circ> fst, index c)\<close>

definition shift\<^sub>2::\<open>('b, 'c)\<H> \<Rightarrow> ('a::orderedrank run) \<Rightarrow> ('b::orderedrank run) \<Rightarrow> ('a\<times>'b, 'c)\<H>\<close>
where \<open>shift\<^sub>2 c r r' \<equiv> ((timep c) \<circ> snd, (index c) + rank r)\<close>

text \<open>
  Some basic properties of shifting.
\<close>
lemma time_shift\<^sub>1:\<open>(timep c) (time r\<^sub>1 n) = (timep (shift\<^sub>1 c r\<^sub>1 r\<^sub>2)) (time (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
by (simp add: shift\<^sub>1_def time_prod_time)

lemma time_shift\<^sub>2:\<open>(timep c) (time r\<^sub>2 n) = (timep (shift\<^sub>2 c r\<^sub>1 r\<^sub>2)) (time (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
by (simp add: shift\<^sub>2_def time_prod_time)

text \<open>
  Here, with have a condition to ensure that clock c is within the rank of r1.
\<close>
lemma hamlet_shift\<^sub>1:
  assumes \<open>index c < rank r\<^sub>1\<close>
  shows   \<open>(hamlet r\<^sub>1 n)!(index c) = (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2))\<close>
proof -
  have \<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2))
        = ((hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))!(index c)\<close>
    by (simp add: hamlet_prod_hamlet shift\<^sub>1_def)
  moreover have \<open>length (hamlet r\<^sub>1 n) = rank r\<^sub>1\<close> by (simp add: rank_any_hamlet)
  ultimately have \<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2))
        = (hamlet r\<^sub>1 n)!(index c)\<close> by (simp add: assms nth_append)
  thus ?thesis ..
qed

lemma hamlet_shift\<^sub>2:
  \<open>(hamlet r\<^sub>2 n)!(index c) = (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2))\<close>
proof -
  have \<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2))
        = ((hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))!((index c) + (rank r\<^sub>1))\<close>
  by (simp add: hamlet_prod_hamlet shift\<^sub>2_def)
  moreover have \<open>length (hamlet r\<^sub>1 n) = rank r\<^sub>1\<close> by (simp add: rank_any_hamlet)
  ultimately have \<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2))
        = (hamlet r\<^sub>2 n)!(index c)\<close> by (simp add: nth_append)
  thus ?thesis ..
qed

text \<open>
  The ticks operator is preserved in a product of runs.
\<close>
lemma ticks_shift1_shift:\<open>ticks c (hamlet r\<^sub>1 n) \<Longrightarrow> ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
proof -
  assume h:\<open>ticks c (hamlet r\<^sub>1 n)\<close>
  from h have idx:\<open>(index c) < length (hamlet r\<^sub>1 n)\<close> using ticks_idx by blast 
  from h have ham:\<open>(hamlet r\<^sub>1 n)!(index c)\<close> by (simp add: ticks_ham)
  from idx have *:\<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < length (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
    unfolding shift\<^sub>1_def by (simp add: hamlet_prod_hamlet)
  from idx have \<open>index c < rank r\<^sub>1\<close> by (simp add: rank_any_hamlet)
  from hamlet_shift\<^sub>1[OF this, of \<open>n\<close> \<open>r\<^sub>2\<close>] ham have \<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2))\<close>
    by simp
  thus ?thesis unfolding ticks_def by (simp add: *)
qed

lemma ticks_shift1_unshift:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n) \<Longrightarrow> ticks c (hamlet r\<^sub>1 n)\<close>
proof -
  assume h:\<open>ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
  from ticks_ham[OF h]
    have ham:\<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2))\<close>
    by simp
  from assms have idx:\<open>index c < rank r\<^sub>1\<close> unfolding shift\<^sub>1_def by simp
  from hamlet_shift\<^sub>1[OF this, of \<open>n\<close> \<open>r\<^sub>2\<close>] ham have \<open>(hamlet r\<^sub>1 n)!(index c)\<close>
    by simp
  thus ?thesis unfolding ticks_def by (simp add: rank_any_hamlet idx)
qed

lemma ticks_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>ticks c (hamlet r\<^sub>1 n) = ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
using assms ticks_shift1_shift ticks_shift1_unshift by blast

lemma ticks_shift2_shift:\<open>ticks c (hamlet r\<^sub>2 n) \<Longrightarrow> ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
proof -
  assume h:\<open>ticks c (hamlet r\<^sub>2 n)\<close>
  from ticks_idx[OF h] have idx:\<open>(index c) < length (hamlet r\<^sub>2 n)\<close> .
  from ticks_ham[OF h] have ham:\<open>(hamlet r\<^sub>2 n)!(index c)\<close> .
  from idx have *:\<open>index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) < length (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
    unfolding shift\<^sub>2_def by (simp add: hamlet_prod_hamlet rank_any_hamlet)
  from hamlet_shift\<^sub>2[of \<open>r\<^sub>2\<close> \<open>n\<close> \<open>c\<close>] ham have \<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2))\<close>
    by simp
  thus ?thesis unfolding ticks_def by (simp add: *)
qed

lemma ticks_shift2_unshift:
  \<open>ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n) \<Longrightarrow> ticks c (hamlet r\<^sub>2 n)\<close>
proof -
  assume h:\<open>ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
  from ticks_idx[OF h]
    have \<open>index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) < rank (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> by (simp add: rank_any_hamlet)
    hence idx:\<open>index c < rank r\<^sub>2\<close> by (simp add: run_prod_rank shift\<^sub>2_def)
  from ticks_ham[OF h]
    have ham:\<open>(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index (shift\<^sub>2 c r\<^sub>1 r\<^sub>2))\<close>
    by simp
  from hamlet_shift\<^sub>2[of \<open>r\<^sub>2\<close> \<open>n\<close> \<open>c\<close> \<open>r\<^sub>1\<close>] ham have \<open>(hamlet r\<^sub>2 n)!(index c)\<close>
    by simp
  thus ?thesis unfolding ticks_def by (simp add: idx rank_any_hamlet)
qed

lemma ticks_shift2:\<open>ticks c (hamlet r\<^sub>2 n) = ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)\<close>
using ticks_shift2_shift ticks_shift2_unshift by blast

text \<open>
  The set of instants when a clock ticks is preserved by architectural composition.
\<close>
lemma tick_set_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>{k. ticks c (hamlet r\<^sub>1 k)} = {k. ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) k)}\<close>
using ticks_shift1[OF assms] by blast

lemma tick_set_shift2:
  \<open>{k. ticks c (hamlet r\<^sub>2 k)} = {k. ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) k)}\<close>
using ticks_shift2 by blast

text \<open>
  The instant of the first tick of a clock is preserved by architectural composition.
\<close>
lemma Least_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  and     \<open>\<exists>k. ticks c (hamlet r\<^sub>1 k)\<close>
  shows   \<open>(LEAST k. k \<in> {t. ticks c (hamlet r\<^sub>1 t)})
         = (LEAST k. k \<in> {t. ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) t)})\<close>
          (is \<open>(LEAST k. k \<in> ?R) = (LEAST k. k \<in> ?P)\<close>)
proof -
  from tick_set_shift1[OF assms(1)] have \<open>?R = ?P\<close> by simp
  thus ?thesis using assms(2) by auto
qed

lemma Least_shift2:
  assumes \<open>\<exists>k. ticks c (hamlet r\<^sub>2 k)\<close>
  shows   \<open>(LEAST k. k \<in> {t. ticks c (hamlet r\<^sub>2 t)})
         = (LEAST k. k \<in> {t. ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) t)})\<close>
          (is \<open>(LEAST k. k \<in> ?R) = (LEAST k. k \<in> ?P)\<close>)
proof -
  from tick_set_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> \<open>r\<^sub>1\<close>] have \<open>?R = ?P\<close> by simp
  thus ?thesis by auto
qed

lemma first_tick_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>first_tick c (hamlet r\<^sub>1) = first_tick (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2))\<close>
proof (cases \<open>\<exists>k. ticks c (hamlet r\<^sub>1 k)\<close>)
  case False
    hence *:\<open>first_tick c (hamlet r\<^sub>1) = None\<close> unfolding first_tick_def by simp
    from False ticks_shift1[OF assms]
      have \<open>\<nexists>k. ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) k)\<close> by blast
    hence **:\<open>first_tick (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) = None\<close>
      unfolding first_tick_def by simp
    from * show ?thesis by (simp add: **)
next
  case True
    with ticks_shift1[OF assms] have *:\<open>\<exists>k. ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) k)\<close> by blast
    from True have \<open>first_tick c (hamlet r\<^sub>1) = Some (LEAST k. ticks c (hamlet r\<^sub>1 k))\<close>
      unfolding first_tick_def by simp
    also from Least_shift1[OF assms True]
      have \<open>... =  Some (LEAST k. k \<in> {t. ticks (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) t)})\<close>
      by (simp add: True)
    finally show ?thesis unfolding first_tick_def by (simp add: True *) 
qed

lemma first_tick_shift2:
  shows   \<open>first_tick c (hamlet r\<^sub>2) = first_tick (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2))\<close>
proof (cases \<open>\<exists>k. ticks c (hamlet r\<^sub>2 k)\<close>)
  case False
    hence *:\<open>first_tick c (hamlet r\<^sub>2) = None\<close> unfolding first_tick_def by simp
    from False ticks_shift2
      have \<open>\<nexists>k. ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) k)\<close> by blast
    hence **:\<open>first_tick (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) = None\<close>
      unfolding first_tick_def by simp
    from * show ?thesis by (simp add: **)
next
  case True
    with ticks_shift2 have *:\<open>\<exists>k. ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) k)\<close> by blast
    from True have \<open>first_tick c (hamlet r\<^sub>2) = Some (LEAST k. ticks c (hamlet r\<^sub>2 k))\<close>
      unfolding first_tick_def by simp
    also from Least_shift2[OF True, of \<open>r\<^sub>1\<close>]
      have \<open>... =  Some (LEAST k. k \<in> {t. ticks (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) t)})\<close>
      by (simp add: True)
    finally show ?thesis unfolding first_tick_def by (simp add: True *) 
qed

text \<open>
  tick_count operator
\<close>
lemma tick_count_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>tick_count c (hamlet r\<^sub>1) n = tick_count (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<close>
using ticks_shift1[OF assms] unfolding tick_count_def by simp

lemma tick_count_shift2:
  shows   \<open>tick_count c (hamlet r\<^sub>2) n = tick_count (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<close>
using ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] unfolding tick_count_def by simp

text \<open>
  tick_count_between operator
\<close>
lemma tick_count_between_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>tick_count_between c (hamlet r\<^sub>1) m n
           = tick_count_between (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) m n\<close>
using ticks_shift1[OF assms] unfolding tick_count_between_def by simp

lemma tick_count_between_shift2:
  shows   \<open>tick_count_between c (hamlet r\<^sub>2) m n
          = tick_count_between (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) m n\<close>
using ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] unfolding tick_count_between_def by simp

text \<open>
  first_tick_since operator
\<close>
lemma first_tick_since_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>first_tick_since c (hamlet r\<^sub>1) r n
          = first_tick_since (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) r n\<close>
using ticks_shift1[OF assms] unfolding first_tick_since_def by simp

lemma first_tick_since_shift2:
  shows \<open>first_tick_since c (hamlet r\<^sub>2) r n
        = first_tick_since (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) r n\<close>
using ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] unfolding first_tick_since_def by simp

text \<open>
  has_ticked_since operator
\<close>
lemma has_ticked_since_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>has_ticked_since c (hamlet r\<^sub>1) r n
          = has_ticked_since (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) r n\<close>
using ticks_shift1[OF assms] unfolding has_ticked_since_def by simp

lemma has_ticked_since_shift2:
  shows \<open>has_ticked_since c (hamlet r\<^sub>2) r n
        = has_ticked_since (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) r n\<close>
using ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] unfolding has_ticked_since_def by simp

text \<open>
  has_first_since operator
\<close>
lemma has_first_since_shift11:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>has_first_since a b (hamlet r\<^sub>1) n\<^sub>0 n
          = has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0 n\<close>
unfolding has_first_since_def
using first_tick_since_shift1[OF assms(1)] first_tick_since_shift1[OF assms(2)]
      has_ticked_since_shift1[OF assms(1)] has_ticked_since_shift1[OF assms(2)] by blast

lemma has_first_since_shift22:
  \<open>has_first_since (a::('b::orderedrank, 'c)\<H>) (b::('b, 'd)\<H>) (hamlet r\<^sub>2) n\<^sub>0 n
  = has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0 n\<close>
unfolding has_first_since_def
using first_tick_since_shift2 first_tick_since_shift2
      has_ticked_since_shift2 has_ticked_since_shift2 by blast

text \<open>
  have_both_ticked operator
\<close>
lemma have_both_ticked_shift11:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>have_both_ticked a b (hamlet r\<^sub>1) n
           = have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<close>
          (is \<open>?H n = ?HS n\<close>)
proof (induction n rule: nat_strong_induct)
  case 0 show ?case
    proof
      { assume \<open>?H 0\<close>
        from  hbt0'[OF this]
          have \<open>has_first_since a b (hamlet r\<^sub>1) 0 0 \<or> has_first_since b a (hamlet r\<^sub>1) 0 0\<close> .
        hence \<open>has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0
             \<or> has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0\<close>
         using has_first_since_shift11[OF assms]
               has_first_since_shift11[OF assms(2) assms(1)] by blast
        hence \<open>?HS 0\<close> using  have_both_ticked.intros by blast
      } thus \<open>?H 0 \<Longrightarrow> ?HS 0\<close> .
    next
      { assume \<open>?HS 0\<close>
        from  hbt0'[OF this]
          have \<open>has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0
              \<or> has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0\<close> .
        hence \<open>has_first_since a b (hamlet r\<^sub>1) 0 0 \<or> has_first_since b a (hamlet r\<^sub>1) 0 0\<close>
         using has_first_since_shift11[OF assms]
               has_first_since_shift11[OF assms(2) assms(1)] by blast
        hence \<open>?H 0\<close> using  have_both_ticked.intros by blast
      } thus \<open>?HS 0 \<Longrightarrow> ?H 0\<close> .
    qed
next
  case (Suc p) show ?case
  proof
    { assume h:\<open>?H (Suc p)\<close>
      from this consider
        (a) \<open>has_first_since a b (hamlet r\<^sub>1) 0 (Suc p)\<close>
      | (b) \<open>has_first_since b a (hamlet r\<^sub>1) 0 (Suc p)\<close>
      | (c) \<open>\<exists>n\<^sub>0. have_both_ticked a b (hamlet r\<^sub>1) n\<^sub>0 \<and> has_first_since a b (hamlet r\<^sub>1) (Suc n\<^sub>0) (Suc p)\<close>
      | (d) \<open>\<exists>n\<^sub>0. have_both_ticked a b (hamlet r\<^sub>1) n\<^sub>0 \<and> has_first_since b a (hamlet r\<^sub>1) (Suc n\<^sub>0) (Suc p)\<close>
      using btn_btn0'[OF h] by blast
      thus \<open>?HS (Suc p)\<close>
      proof cases
        case a thus ?thesis using
          has_first_since_shift11[OF assms, of \<open>0\<close> \<open>Suc p\<close>]
          have_both_ticked.simps[of \<open>shift\<^sub>1 a r\<^sub>1 r\<^sub>2\<close> \<open>shift\<^sub>1 b r\<^sub>1 r\<^sub>2\<close> \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> \<open>Suc p\<close>]
        by simp
      next
        case b thus ?thesis using
          has_first_since_shift11[OF assms(2) assms(1), of \<open>0\<close> \<open>Suc p\<close>]
          have_both_ticked.simps[of \<open>shift\<^sub>1 a r\<^sub>1 r\<^sub>2\<close> \<open>shift\<^sub>1 b r\<^sub>1 r\<^sub>2\<close> \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> \<open>Suc p\<close>]
        by simp
      next
        case c
        from this obtain n\<^sub>0 where 
          n0prop:\<open>have_both_ticked a b (hamlet r\<^sub>1) n\<^sub>0 \<and> has_first_since a b (hamlet r\<^sub>1) (Suc n\<^sub>0) (Suc p)\<close>
          by blast
        hence \<open>has_ticked_since a (hamlet r\<^sub>1) (Suc n\<^sub>0) (Suc p)\<close> using has_first_since_def by blast
        hence \<open>n\<^sub>0 \<le> p\<close> using ht_not_empty by blast
        with Suc.IH n0prop have
          \<open>have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0\<close> by simp
        moreover from n0prop have
          \<open>has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
          using has_first_since_shift11[OF assms] by blast
        ultimately show ?thesis using have_both_ticked.intros(3) by blast
      next
        case d
        from this obtain n\<^sub>0 where 
          n0prop:\<open>have_both_ticked a b (hamlet r\<^sub>1) n\<^sub>0 \<and> has_first_since b a (hamlet r\<^sub>1) (Suc n\<^sub>0) (Suc p)\<close>
          by blast
        hence \<open>has_ticked_since b (hamlet r\<^sub>1) (Suc n\<^sub>0) (Suc p)\<close> using has_first_since_def by blast
        hence \<open>n\<^sub>0 \<le> p\<close> using ht_not_empty by blast
        with Suc.IH n0prop have
          \<open>have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0\<close> by simp
        moreover from n0prop have
          \<open>has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
          using has_first_since_shift11[OF assms(2) assms(1)] by blast
        ultimately show ?thesis using have_both_ticked.intros(4) by blast
      qed
    }
  next
    { assume h:\<open>?HS (Suc p)\<close>
      from this consider
        (a) \<open>has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 (Suc p)\<close>
      | (b) \<open>has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 (Suc p)\<close>
      | (c) \<open>\<exists>n\<^sub>0. have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
               \<and> has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
      | (d) \<open>\<exists>n\<^sub>0. have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
               \<and> has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
      using btn_btn0'[OF h] by blast
      thus \<open>?H (Suc p)\<close>
      proof cases
        case a thus ?thesis
          using has_first_since_shift11[OF assms, of \<open>0\<close> \<open>Suc p\<close>] have_both_ticked.intros(1) by simp
      next
        case b thus ?thesis
          using has_first_since_shift11[OF assms(2) assms(1), of \<open>0\<close> \<open>Suc p\<close>]
                    have_both_ticked.simps[of \<open>a\<close> \<open>b\<close> \<open>hamlet r\<^sub>1\<close> \<open>Suc p\<close>] by simp
      next
        case c
          from this obtain n\<^sub>0 where n0prop:
            \<open>have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
           \<and> has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            by blast
          hence \<open>has_first_since (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            by simp
          hence \<open>n\<^sub>0 \<le> p\<close> using ht_not_empty hft_ht by blast
          with Suc.IH n0prop have \<open>have_both_ticked a b (hamlet r\<^sub>1) n\<^sub>0\<close> by simp
          with n0prop show ?thesis
            using have_both_ticked.intros(3) has_first_since_shift11[OF assms] by blast
      next
        case d
          from this obtain n\<^sub>0 where n0prop:
            \<open>have_both_ticked (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
           \<and> has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            by blast
          hence \<open>has_first_since (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            by simp
          hence \<open>n\<^sub>0 \<le> p\<close> using ht_not_empty hft_ht by blast
          with Suc.IH n0prop have \<open>have_both_ticked a b (hamlet r\<^sub>1) n\<^sub>0\<close> by simp
          with n0prop show ?thesis
            using have_both_ticked.intros(4) has_first_since_shift11[OF assms(2) assms(1)] by blast
      qed
    }
  qed
qed

lemma have_both_ticked_shift22:
   \<open>have_both_ticked a b (hamlet r\<^sub>2) n
    = have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<close>
   (is \<open>?H n = ?HS n\<close>)
proof (induction n rule: nat_strong_induct)
  case 0 show ?case
    proof
      { assume \<open>?H 0\<close>
        from  hbt0'[OF this]
          have \<open>has_first_since a b (hamlet r\<^sub>2) 0 0 \<or> has_first_since b a (hamlet r\<^sub>2) 0 0\<close> .
        hence \<open>has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0
             \<or> has_first_since (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0\<close>
         using has_first_since_shift22[of \<open>a\<close> \<open>b\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>0\<close> \<open>r\<^sub>1\<close>]
               has_first_since_shift22[of \<open>b\<close> \<open>a\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>0\<close> \<open>r\<^sub>1\<close>] by simp
        hence \<open>?HS 0\<close> using  have_both_ticked.intros by blast
      } thus \<open>?H 0 \<Longrightarrow> ?HS 0\<close> .
    next
      { assume \<open>?HS 0\<close>
        from  hbt0'[OF this]
          have \<open>has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0
              \<or> has_first_since (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 0\<close> .
          hence \<open>has_first_since a b (hamlet r\<^sub>2) 0 0
           \<or> has_first_since b a (hamlet r\<^sub>2) 0 0\<close> using
            has_first_since_shift22[of \<open>a\<close> \<open>b\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>0\<close>]
            has_first_since_shift22[of \<open>b\<close> \<open>a\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>0\<close>] by blast
        hence \<open>?H 0\<close> using have_both_ticked.intros(1-2) by blast
      } thus \<open>?HS 0 \<Longrightarrow> ?H 0\<close> .
    qed
next
  case (Suc p) show ?case
  proof
    { assume h:\<open>?H (Suc p)\<close>
      from this consider
        (a) \<open>has_first_since a b (hamlet r\<^sub>2) 0 (Suc p)\<close>
      | (b) \<open>has_first_since b a (hamlet r\<^sub>2) 0 (Suc p)\<close>
      | (c) \<open>\<exists>n\<^sub>0. have_both_ticked a b (hamlet r\<^sub>2) n\<^sub>0 \<and> has_first_since a b (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close>
      | (d) \<open>\<exists>n\<^sub>0. have_both_ticked a b (hamlet r\<^sub>2) n\<^sub>0 \<and> has_first_since b a (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close>
      using btn_btn0'[OF h] by blast
      thus \<open>?HS (Suc p)\<close>
      proof cases
        case a thus ?thesis using
          has_first_since_shift22[of \<open>a\<close> \<open>b\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>Suc p\<close> \<open>r\<^sub>1\<close>]
          have_both_ticked.simps[of \<open>shift\<^sub>2 a r\<^sub>1 r\<^sub>2\<close> \<open>shift\<^sub>2 b r\<^sub>1 r\<^sub>2\<close> \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> \<open>Suc p\<close>]
          by simp
      next
        case b thus ?thesis using
          has_first_since_shift22[of \<open>b\<close> \<open>a\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>Suc p\<close> \<open>r\<^sub>1\<close>]
          have_both_ticked.simps[of \<open>shift\<^sub>2 a r\<^sub>1 r\<^sub>2\<close> \<open>shift\<^sub>2 b r\<^sub>1 r\<^sub>2\<close> \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> \<open>Suc p\<close>]
          by simp
      next
        case c
          from this obtain n\<^sub>0 where n0prop:
            \<open>have_both_ticked a b (hamlet r\<^sub>2) n\<^sub>0 \<and> has_first_since a b (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close>
            by blast
          hence \<open>has_first_since a b (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close> by simp
          from hft_ht[OF this] have \<open>n\<^sub>0 \<le> p\<close> using  ht_not_empty by blast
          with Suc n0prop have
            \<open>have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0\<close> by simp
          moreover from n0prop have
            \<open>has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            using has_first_since_shift22 by blast
          ultimately show ?thesis using
            have_both_ticked.simps[of \<open>shift\<^sub>2 a r\<^sub>1 r\<^sub>2\<close> \<open>shift\<^sub>2 b r\<^sub>1 r\<^sub>2\<close> \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> \<open>Suc p\<close>]
            by blast
      next
        case d
          from this obtain n\<^sub>0 where n0prop:
            \<open>have_both_ticked a b (hamlet r\<^sub>2) n\<^sub>0 \<and> has_first_since b a (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close>
            by blast
          hence \<open>has_first_since b a (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close> by simp
          from hft_ht[OF this] have \<open>n\<^sub>0 \<le> p\<close> using  ht_not_empty by blast
          with Suc n0prop have
            \<open>have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0\<close> by simp
          moreover from n0prop have
            \<open>has_first_since (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            using has_first_since_shift22 by blast
          ultimately show ?thesis using
            have_both_ticked.simps[of \<open>shift\<^sub>2 a r\<^sub>1 r\<^sub>2\<close> \<open>shift\<^sub>2 b r\<^sub>1 r\<^sub>2\<close> \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)\<close> \<open>Suc p\<close>]
            by blast
      qed
    }
  next
    { assume h:\<open>?HS (Suc p)\<close>
      from this consider
        (a) \<open>has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 (Suc p)\<close>
      | (b) \<open>has_first_since (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) 0 (Suc p)\<close>
      | (c) \<open>\<exists>n\<^sub>0. have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
               \<and> has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
      | (d) \<open>\<exists>n\<^sub>0. have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
               \<and> has_first_since (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
      using btn_btn0'[OF h] by blast
      thus \<open>?H (Suc p)\<close>
      proof cases
        case a thus ?thesis using
          has_first_since_shift22[of \<open>a\<close> \<open>b\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>Suc p\<close> \<open>r\<^sub>1\<close>]
          have_both_ticked.simps[of \<open>a\<close> \<open>b\<close> \<open>hamlet r\<^sub>2\<close> \<open>Suc p\<close>] by simp
      next
        case b thus ?thesis using
          has_first_since_shift22[of \<open>b\<close> \<open>a\<close> \<open>r\<^sub>2\<close> \<open>0\<close> \<open>Suc p\<close> \<open>r\<^sub>1\<close>]
          have_both_ticked.simps[of \<open>a\<close> \<open>b\<close> \<open>hamlet r\<^sub>2\<close> \<open>Suc p\<close>] by simp
      next
        case c
          from this obtain n\<^sub>0 where n0prop:
            \<open>have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
          \<and> has_first_since (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            by blast
          hence \<open>n\<^sub>0 \<le> p\<close> using hft_ht ht_not_empty by blast
          with Suc n0prop have \<open>have_both_ticked a b (hamlet r\<^sub>2) n\<^sub>0\<close> by simp
          moreover have \<open>has_first_since a b (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close>
            using n0prop has_first_since_shift22 by blast
          ultimately show ?thesis using have_both_ticked.simps by blast
      next
        case d
          from this obtain n\<^sub>0 where n0prop:
            \<open>have_both_ticked (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<^sub>0
          \<and> has_first_since (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (Suc n\<^sub>0) (Suc p)\<close>
            by blast
          hence \<open>n\<^sub>0 \<le> p\<close> using hft_ht ht_not_empty by blast
          with Suc n0prop have \<open>have_both_ticked a b (hamlet r\<^sub>2) n\<^sub>0\<close> by simp
          moreover have \<open>has_first_since b a (hamlet r\<^sub>2) (Suc n\<^sub>0) (Suc p)\<close>
            using n0prop has_first_since_shift22 by blast
          ultimately show ?thesis using have_both_ticked.simps by blast
      qed
    }
  qed
qed

text \<open>
  between operator.
\<close>
lemma between_shift1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  and     \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>between a b (hamlet r\<^sub>1) n = between (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<close>
unfolding between_def using ticks_shift1[OF assms(1)] ticks_shift1[OF assms(2)] by simp

lemma between_shift2:
  \<open>between a b (hamlet r\<^sub>2) n = between (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) n\<close>
unfolding between_def using ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] ticks_shift2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

section \<open>
  Preservation of the TESL relations by architectural composition
\<close>

text \<open>
  Sporadic specifications are preserved by composition.
\<close>
lemma sporadic_shift1:
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  and     \<open>r\<^sub>1 \<in> c sporadic \<tau>\<close>
  shows   \<open>(r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) sporadic \<tau>\<close>
using assms(2) unfolding Sporadic_def
using ticks_shift1[OF assms(1)] time_shift\<^sub>1[of \<open>c\<close> \<open>r\<^sub>1\<close> _ \<open>r\<^sub>2\<close>] by simp

lemma sporadic_shift2:
  assumes \<open>r\<^sub>2 \<in> c sporadic \<tau>\<close>
  shows   \<open>(r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) sporadic \<tau>\<close>
using assms unfolding Sporadic_def
using ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] time_shift\<^sub>2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Implications are preserved by composition.
\<close>
lemma implies_shift1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  and     \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  and     \<open>r\<^sub>1 \<in> a implies b\<close>
  shows   \<open>(r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) implies (shift\<^sub>1 b r\<^sub>1 r\<^sub>2)\<close>
using assms(3) unfolding Implies_def
using ticks_shift1[OF assms(1)] ticks_shift1[OF assms(2)] by simp

lemma implies_shift2:
  assumes \<open>r\<^sub>2 \<in> a implies b\<close>
  shows   \<open>(r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) implies (shift\<^sub>2 b r\<^sub>1 r\<^sub>2)\<close>
using assms unfolding Implies_def
using ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] ticks_shift2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Implies every relations are preserved by composition.
\<close>
lemma implies_every_prod1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  and     \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>(r\<^sub>1 \<in> a implies b every n) = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) implies (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) every n)\<close>
unfolding ImpliesEvery_def
using ticks_shift1[OF assms(1)] ticks_shift1[OF assms(2)] tick_count_shift1[OF assms(1)] by simp

lemma implies_every_prod2:
  \<open>(r\<^sub>2 \<in> a implies b every n) = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) implies (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) every n)\<close>
unfolding ImpliesEvery_def
using ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      tick_count_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Tag relations are preserved by composition.
\<close>
lemma tagrel_prod1:
  \<open>(r\<^sub>1 \<in> TagRelation a R b) = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> TagRelation (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) R (shift\<^sub>1 b r\<^sub>1 r\<^sub>2))\<close>
unfolding TagRelation_def
using time_shift\<^sub>1[of \<open>a\<close> \<open>r\<^sub>1\<close> _ \<open>r\<^sub>2\<close>] time_shift\<^sub>1[of \<open>b\<close> \<open>r\<^sub>1\<close> _ \<open>r\<^sub>2\<close>] by simp

lemma tagrel_prod2:
  \<open>(r\<^sub>2 \<in> TagRelation a R b) = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> TagRelation (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) R (shift\<^sub>2 b r\<^sub>1 r\<^sub>2))\<close>
unfolding TagRelation_def
using time_shift\<^sub>2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] time_shift\<^sub>2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Loose tag relations are preserved by projections.
\<close>
lemma loosetagrel_proj1:
  assumes \<open>(r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> LooseTagRelation (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) R (shift\<^sub>1 b r\<^sub>1 r\<^sub>2)\<close>
                                       (is \<open>?P \<in> LooseTagRelation ?SA R ?SB\<close>)
  shows   \<open>r\<^sub>1 \<in> LooseTagRelation a R b\<close>
proof -
  from assms have *:\<open>\<forall>n. tick_occurs (hamlet ?P n)
                         \<longrightarrow> ((timep ?SA)(time ?P n), (timep ?SB)(time ?P n)) \<in> R\<close>
    unfolding LooseTagRelation_def by simp
  { fix n assume h:\<open>tick_occurs (hamlet r\<^sub>1 n)\<close>
    from tick_occurs_prod1[OF this] have \<open>tick_occurs (hamlet ?P n)\<close> .
    with * have \<open>((timep ?SA)(time ?P n), (timep ?SB)(time ?P n)) \<in> R\<close> by simp
    hence \<open>((timep a)(time r\<^sub>1 n), (timep b)(time r\<^sub>1 n)) \<in> R\<close>
      using time_shift\<^sub>1[of \<open>a\<close> \<open>r\<^sub>1\<close> \<open>n\<close> \<open>r\<^sub>2\<close>]
            time_shift\<^sub>1[of \<open>b\<close> \<open>r\<^sub>1\<close> \<open>n\<close> \<open>r\<^sub>2\<close>] by simp
  } thus ?thesis unfolding LooseTagRelation_def by simp
qed

lemma loosetagrel_proj2:
  assumes \<open>(r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> LooseTagRelation (shift\<^sub>2 a r\<^sub>1 r\<^sub>2) R (shift\<^sub>2 b r\<^sub>1 r\<^sub>2)\<close>
          (is \<open>?P \<in> LooseTagRelation ?SA R ?SB\<close>)
  shows   \<open>r\<^sub>2 \<in> LooseTagRelation a R b\<close>
proof -
  from assms have *:\<open>\<forall>n. tick_occurs (hamlet ?P n)
                         \<longrightarrow> ((timep ?SA)(time ?P n), (timep ?SB)(time ?P n)) \<in> R\<close>
    unfolding LooseTagRelation_def by simp
  { fix n assume h:\<open>tick_occurs (hamlet r\<^sub>2 n)\<close>
    from tick_occurs_prod2[OF this] have \<open>tick_occurs (hamlet ?P n)\<close> .
    with * have \<open>((timep ?SA)(time ?P n), (timep ?SB)(time ?P n)) \<in> R\<close> by simp
    hence \<open>((timep a)(time r\<^sub>2 n), (timep b)(time r\<^sub>2 n)) \<in> R\<close>
      using time_shift\<^sub>2[of \<open>a\<close> \<open>r\<^sub>2\<close> \<open>n\<close> \<open>r\<^sub>1\<close>]
            time_shift\<^sub>2[of \<open>b\<close> \<open>r\<^sub>2\<close> \<open>n\<close> \<open>r\<^sub>1\<close>] by simp
  } thus ?thesis unfolding LooseTagRelation_def by simp
qed

text \<open>
  Time delayed relations are preserved by composition.
\<close>
lemma timedelayed_prod1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>(r\<^sub>1 \<in> (a time-delayed by dt on b implies c))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>1 a r\<^sub>1 r\<^sub>2) time-delayed by dt on (shift\<^sub>1 b r\<^sub>1 r\<^sub>2)
                                           implies (shift\<^sub>1 c r\<^sub>1 r\<^sub>2)))\<close>
unfolding TimeDelayed_def
using time_shift\<^sub>1[of \<open>a\<close> \<open>r\<^sub>1\<close> _ \<open>r\<^sub>2\<close>]
      time_shift\<^sub>1[of \<open>b\<close> \<open>r\<^sub>1\<close> _ \<open>r\<^sub>2\<close>]
      ticks_shift1[OF assms(1)]
      ticks_shift1[OF assms(2)] by simp

lemma timedelayed_prod2:
  \<open>(r\<^sub>2 \<in> (a time-delayed by dt on b implies c))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>2 a r\<^sub>1 r\<^sub>2) time-delayed by dt on (shift\<^sub>2 b r\<^sub>1 r\<^sub>2)
                                           implies (shift\<^sub>2 c r\<^sub>1 r\<^sub>2)))\<close>
unfolding TimeDelayed_def
using time_shift\<^sub>2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      time_shift\<^sub>2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Delayed relations are preserved by composition.
\<close>
lemma delayed_prod1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>(r\<^sub>1 \<in> (a delayed by n on b implies c))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>1 a r\<^sub>1 r\<^sub>2) delayed by n on (shift\<^sub>1 b r\<^sub>1 r\<^sub>2)
                                           implies (shift\<^sub>1 c r\<^sub>1 r\<^sub>2)))\<close>
unfolding Delayed_def
using tick_count_between_shift1[OF assms(2)]
      ticks_shift1[OF assms(1)]
      ticks_shift1[OF assms(3)] by simp 

lemma delayed_prod2:
  \<open>(r\<^sub>2 \<in> (a delayed by n on b implies c))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>2 a r\<^sub>1 r\<^sub>2) delayed by n on (shift\<^sub>2 b r\<^sub>1 r\<^sub>2)
          implies (shift\<^sub>2 c r\<^sub>1 r\<^sub>2)))\<close>
unfolding Delayed_def
using tick_count_between_shift2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Filtered relations are preserved by composition.
\<close>
\<^cancel>\<open>declare [[show_sorts]]\<close>
lemma filtered_prod1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>(r\<^sub>1 \<in> (a filtered by s, k (rs, rk)* implies b))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>1 a r\<^sub>1 r\<^sub>2) filtered by s, k (rs, rk)*
                                           implies (shift\<^sub>1 b r\<^sub>1 r\<^sub>2)))\<close>
unfolding Filtered_def
using ticks_shift1[OF assms(1)]
      ticks_shift1[OF assms(2)]
      tick_count_shift1[OF assms(1)] by simp

lemma filtered_prod2:
  \<open>(r\<^sub>2 \<in> (a filtered by s, k (rs, rk)* implies b))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>2 a r\<^sub>1 r\<^sub>2) filtered by s, k (rs, rk)*
          implies (shift\<^sub>2 b r\<^sub>1 r\<^sub>2)))\<close>
unfolding Filtered_def
using ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      tick_count_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Await relations are preserved by composition.
\<close>
lemma await_prod1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>(r\<^sub>1 \<in> (await a, b implies c))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (await (shift\<^sub>1 a r\<^sub>1 r\<^sub>2), (shift\<^sub>1 b r\<^sub>1 r\<^sub>2)
                                          implies (shift\<^sub>1 c r\<^sub>1 r\<^sub>2)))\<close>
unfolding Await_def
using have_both_ticked_shift11[OF assms(1-2)]
      ticks_shift1[OF assms(3)] by simp

lemma await_prod2:
  \<open>(r\<^sub>2 \<in> (await a, b implies c))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> (await (shift\<^sub>2 a r\<^sub>1 r\<^sub>2), (shift\<^sub>2 b r\<^sub>1 r\<^sub>2)
                                          implies (shift\<^sub>2 c r\<^sub>1 r\<^sub>2)))\<close>
unfolding Await_def
using have_both_ticked_shift22[of \<open>a\<close> \<open>b\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp

text \<open>
  Sustain relations are preserved by composition.
\<close>
lemma sustain_prod1:
  assumes \<open>index (shift\<^sub>1 a r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  assumes \<open>index (shift\<^sub>1 d r\<^sub>1 r\<^sub>2) < rank r\<^sub>1\<close>
  shows   \<open>(r\<^sub>1 \<in> (a sustained from b to c implies d))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>1 a r\<^sub>1 r\<^sub>2) sustained
                            from (shift\<^sub>1 b r\<^sub>1 r\<^sub>2) to (shift\<^sub>1 c r\<^sub>1 r\<^sub>2) implies (shift\<^sub>1 d r\<^sub>1 r\<^sub>2)))\<close>
unfolding SustainFromTo_def
using between_shift1[OF assms(2-3)]
      ticks_shift1[OF assms(1)]
      ticks_shift1[OF assms(4)] by simp

lemma sustain_prod2:
  \<open>(r\<^sub>2 \<in> (a sustained from b to c implies d))
        = ((r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) \<in> ((shift\<^sub>2 a r\<^sub>1 r\<^sub>2) sustained
                            from (shift\<^sub>2 b r\<^sub>1 r\<^sub>2) to (shift\<^sub>2 c r\<^sub>1 r\<^sub>2) implies (shift\<^sub>2 d r\<^sub>1 r\<^sub>2)))\<close>
unfolding SustainFromTo_def
using between_shift2[of \<open>b\<close> \<open>c\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>a\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>]
      ticks_shift2[of \<open>d\<close> \<open>r\<^sub>2\<close> _ \<open>r\<^sub>1\<close>] by simp


end
