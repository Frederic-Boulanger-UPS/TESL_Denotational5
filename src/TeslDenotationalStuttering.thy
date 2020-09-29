theory TeslDenotationalStuttering

imports TeslDenotationalRelations

begin

text \<open>
  Properties on TESL runs and specifications.
\<close>

section \<open> Stuttering \<close>

text \<open>
  A run is a subrun of another run if there is a function that can insert empty instants
  in the subrun to obtain the other run.
  Such a \<^emph>\<open>dilating\<close> function is strictly monotonous (and so injective because nat is linorder)
  to preserve the order of events and not collapse distinct instants.
  This function is also \<^emph>\<open>expanding\<close> (i.e. \<^theory_text>\<open>f n \<ge> n\<close>) because it can only insert empty instants
  in the subrun.
  Ticks cannot occur in the inserted instants.
\<close>

definition dilating_fun
where
  \<open>dilating_fun (f::nat \<Rightarrow> nat) h
    \<equiv> strict_mono f \<and> (\<forall>n. f n \<ge> n \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> \<not>(tick_occurs (h n))))\<close>

lemma dilating_fun_injects:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>inj_on f A\<close>
using assms dilating_fun_def strict_mono_imp_inj_on by blast

text \<open>
  If a clock ticks at an instant in a dilated run, that instant is the image
  by the dilating function of an instant of the original run.
\<close>
lemma ticks_image:
  assumes \<open>dilating_fun f h\<close>
  and     \<open>ticks c (h n)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using dilating_fun_def assms one_tick_occurs by blast

text \<open>
  The image of the ticks in a interval by a dilating function is the interval 
  bounded by the image of the bound of the original interval.
  This is proven for all 4 kinds of intervals: ]m, n[, [m, n[, ]m, n] and [m, n].
\<close>
lemma dilating_fun_image_strict:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>{k. f m < k \<and> k < f n \<and> ticks c (h k)} = image f {k. m < k \<and> k < n \<and> ticks c (h (f k))}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> ticks c (h (f k\<^sub>0))\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close> using assms dilating_fun_def strict_mono_less by blast
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close> using assms dilating_fun_def strict_mono_less by blast
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image_left:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>{k. f m \<le> k \<and> k < f n \<and> ticks c (h k)}
          = image f {k. m \<le> k \<and> k < n \<and> ticks c (h (f k))}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> ticks c (h (f k\<^sub>0))\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image_right:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>{k. f m < k \<and> k \<le> f n \<and> ticks c (h k)}
          = image f {k. m < k \<and> k \<le> n \<and> ticks c (h (f k))}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> ticks c (h (f k\<^sub>0))\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>{k. f m \<le> k \<and> k \<le> f n \<and> ticks c (h k)}
          = image f {k. m \<le> k \<and> k \<le> n \<and> ticks c (h (f k))}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> ticks c (h (f k\<^sub>0))\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less_eq by blast
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close> using assms dilating_fun_def strict_mono_less_eq by blast
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

text \<open>
  On any clock, the number of ticks in an interval is preserved
  by a dilating function.
\<close>
lemma ticks_as_often_strict:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>card {p. n < p \<and> p < m \<and> ticks c (h (f p))}
          = card {p. f n < p \<and> p < f m \<and> ticks c (h p)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_strict[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_left:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>card {p. n \<le> p \<and> p < m \<and> ticks c (h (f p))}
          = card {p. f n \<le> p \<and> p < f m \<and> ticks c (h p)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_left[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_right:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>card {p. n < p \<and> p \<le> m \<and> ticks c (h (f p))}
          = card {p. f n < p \<and> p \<le> f m \<and> ticks c (h p)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_right[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often:
  assumes \<open>dilating_fun f h\<close>
  shows   \<open>card {p. n \<le> p \<and> p \<le> m \<and> ticks c (h (f p))}
          = card {p. f n \<le> p \<and> p \<le> f m \<and> ticks c (h p)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

text \<open>
  Dilating a run. A run r is a dilation of a run sub by function f if:
    * f is a dilating function on the hamlet of r
    * the time in r is the time in sub dilated by f
    * the hamlet in r is the hamlet in sub dilated by f
\<close>
definition dilating
  where \<open>dilating f sub r \<equiv>   dilating_fun f (hamlet r)
                            \<and> time sub = (time r) \<circ> f
                            \<and> hamlet sub = (hamlet r) \<circ> f\<close>

lemma dilating_injects:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>inj_on f A\<close>
using assms dilating_def dilating_fun_def strict_mono_imp_inj_on by blast

text \<open>
  If there is a tick at instant n in a dilated run, n is necessarily the image
  of some instant in the subrun.
\<close>
lemma ticks_image_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>ticks c (hamlet r n)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using assms dilating_def ticks_image by blast

lemma ticks_image_sub':
  assumes \<open>dilating f sub r\<close>
  and     \<open>tick_occurs (hamlet r n)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using assms dilating_def dilating_fun_def by blast

text \<open>
  Time is preserved by dilation when ticks occur.
\<close>
lemma ticks_tag_image:
  assumes \<open>dilating f sub r\<close>
  and     \<open>tick_occurs (hamlet r k)\<close>
  and     \<open>(timeof c in r at k) = \<tau>\<close>
  shows   \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> (timep c) (time sub k\<^sub>0) = \<tau>\<close>
proof -
  from assms(1,2) have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> using ticks_image_sub' tick_occurs_def by simp
  from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
  moreover with assms(1,3) have \<open>(timeof c in sub at k\<^sub>0) = \<tau>\<close> by (simp add: dilating_def)
  ultimately show ?thesis by blast
qed

text \<open>
  A run is a subrun of another run if there exists a dilation between them.
\<close>
definition is_subrun ::\<open>'a::orderedrank run \<Rightarrow> 'a run \<Rightarrow> bool\<close> (infixl "\<lless>" 60)
where
  \<open>sub \<lless> r \<equiv> (\<exists>f. dilating f sub r)\<close>


text \<open>
  TESL operators are preserved by dilation.
\<close>

lemma ticks_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>ticks a (hamlet sub n) = ticks a (hamlet r (f n))\<close>
using assms by (simp add: dilating_def)

lemma no_tick_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>(\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> \<not>ticks c (hamlet r n)\<close>
using assms dilating_def dilating_fun_def one_tick_occurs by blast

text \<open>
  Lifting a total function to a partial function on an option domain.
\<close>
definition opt_lift::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a option \<Rightarrow> 'a option)\<close>
where
  \<open>opt_lift f \<equiv> \<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (f y)\<close>

text \<open>
  The set of instants when a clock ticks in a dilated run is the image by the dilation function
  of the set of instants when it ticks in the subrun.
\<close>
lemma tick_set_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{k. ticks c (hamlet r k)} = image f {k. ticks c (hamlet sub k)}\<close>
    (is \<open>?R = image f ?S\<close>)
proof
  { fix k assume h:\<open>k \<in> ?R\<close>
    with no_tick_sub[OF assms] have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> by blast
    from this obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k\<close> by blast
    with ticks_sub[OF assms] h have \<open>ticks c (hamlet sub k\<^sub>0)\<close> by blast
    with k0prop have \<open>k \<in> image f ?S\<close> by blast
  }
  thus \<open>?R \<subseteq> image f ?S\<close> by blast
next
  { fix k assume h:\<open>k \<in> image f ?S\<close>
    from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k \<and> ticks c (hamlet sub k\<^sub>0)\<close> by blast
    with assms have \<open>k \<in> ?R\<close> using ticks_sub by blast 
  }
  thus \<open>image f ?S \<subseteq> ?R\<close> by blast
qed

text \<open>
  Strictly monotonous functions preserve the least element.
\<close>
lemma Least_strict_mono:
  assumes \<open>strict_mono f\<close>
  and     \<open>\<exists>x \<in> S. \<forall>y \<in> S. x \<le> y\<close>
  shows   \<open>(LEAST y. y \<in> f ` S) = f (LEAST x. x \<in> S)\<close>
using Least_mono[OF strict_mono_mono, OF assms] .

text \<open>
  The first instant when a clock ticks in a dilated run is the image by the dilation
  function of the first instant when it ticks in the subrun.
\<close>
lemma Least_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>k::nat. ticks c (hamlet sub k)\<close>
  shows   \<open>(LEAST k. k \<in> {t. ticks c (hamlet r t)}) = f (LEAST k. k \<in> {t. ticks c (hamlet sub t)})\<close>
          (is \<open>(LEAST k. k \<in> ?R) = f (LEAST k. k \<in> ?S)\<close>)
proof -
  from assms(2) have \<open>\<exists>x. x \<in> ?S\<close> by simp
  hence least:\<open>\<exists>x \<in> ?S. \<forall>y \<in> ?S. x \<le> y\<close>
    using Least_nat_ex ..
  from assms(1) have \<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  from Least_strict_mono[OF this least] have
    \<open>(LEAST y. y \<in> f ` ?S)  = f (LEAST x. x \<in> ?S)\<close> .
  with tick_set_sub[OF assms(1), of \<open>c\<close>] show ?thesis by auto
qed

text \<open>
  If a clock ticks in a run, it ticks in the subrun.
\<close>
lemma ticks_imp_ticks_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>k. ticks c (hamlet r k)\<close>
  shows   \<open>\<exists>k\<^sub>0. ticks c (hamlet sub k\<^sub>0)\<close>
proof -
  from assms(2) obtain k where \<open>ticks c (hamlet r k)\<close> by blast
  with ticks_image_sub[OF assms(1)] ticks_sub[OF assms(1)] show ?thesis by blast
qed

text \<open>
  Stronger version: it ticks in the subrun and we know when.
\<close>
lemma ticks_imp_ticks_subk:
  assumes \<open>dilating f sub r\<close>
  and     \<open>ticks c (hamlet r k)\<close>
  shows   \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> ticks c (hamlet sub k\<^sub>0)\<close>
proof -
  from no_tick_sub[OF assms(1)] assms(2) have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> by blast
  from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
  moreover with ticks_sub[OF assms(1)] assms(2) have \<open>ticks c (hamlet sub k\<^sub>0)\<close> by blast
  ultimately show ?thesis by blast
qed

text \<open>
  The first_tick operator is preserved by dilation.
\<close>
lemma first_tick_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>first_tick c (hamlet r) = opt_lift f (first_tick c (hamlet sub))\<close>
proof (cases \<open>first_tick c (hamlet sub) = None\<close>)
  case True
    hence nsub:\<open>\<nexists>t. ticks c (hamlet sub t)\<close> using no_first_tick_no_tick by simp
    hence \<open>opt_lift f (first_tick c (hamlet sub)) = None\<close>
      unfolding first_tick_def opt_lift_def by simp
    moreover from nsub ticks_imp_ticks_sub[OF assms]
      have \<open>\<nexists>t. ticks c (hamlet r t)\<close> by blast
    ultimately show ?thesis unfolding first_tick_def by simp
next
  case False
    from first_tick_ticks[OF this] have esub:\<open>\<exists>t. ticks c (hamlet sub t)\<close> . 
    hence \<open>\<exists>t. first_tick c (hamlet sub) = Some t\<close> by (simp add: first_tick_def)
    from this obtain t\<^sub>f where tfprop:\<open>first_tick c (hamlet sub) = Some t\<^sub>f\<close> by blast
    hence \<open>(LEAST k. ticks c (hamlet sub k)) = t\<^sub>f\<close> unfolding first_tick_def using esub by simp
    moreover from esub have \<open>\<exists>t. ticks c (hamlet r t)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>first_tick c (hamlet r) = Some (f t\<^sub>f)\<close>
      unfolding first_tick_def using  Least_sub[OF assms esub] by simp
    with tfprop show ?thesis unfolding opt_lift_def by simp
qed

text \<open>
  A dilating function preserves the tick count on an interval for any clock.
\<close>
lemma dilated_ticks_strict:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m < i \<and> i < f n \<and> ticks c (hamlet r i)}
          = image f {i. m < i \<and> i < n \<and> ticks c (hamlet sub i)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m < i \<and> i < n\<close> by simp
    hence \<open>f m < f i \<and> f i < (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>ticks c (hamlet sub i)\<close> by simp
    hence \<open>ticks c (hamlet r (f i))\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>ticks c (hamlet r i)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> ticks c (hamlet sub i\<^sub>0)\<close> by blast
    with h have \<open>f m < f i\<^sub>0 \<and> f i\<^sub>0 < f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m < i\<^sub>0 \<and> i\<^sub>0 < n\<close> using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks_left:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m \<le> i \<and> i < f n \<and> ticks c (hamlet r i)}
          = image f {i. m \<le> i \<and> i < n \<and> ticks c (hamlet sub i)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m \<le> i \<and> i < n\<close> by simp
    hence \<open>f m \<le> f i \<and> f i < (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>ticks c (hamlet sub i)\<close> by simp
    hence \<open>ticks c (hamlet r (f i))\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>ticks c (hamlet r i)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> ticks c (hamlet sub i\<^sub>0)\<close> by blast
    with h have \<open>f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 < f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m \<le> i\<^sub>0 \<and> i\<^sub>0 < n\<close> using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks_right:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m < i \<and> i \<le> f n \<and> ticks c (hamlet r i)}
          = image f {i. m < i \<and> i \<le> n \<and> ticks c (hamlet sub i)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i  assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m < i \<and> i \<le> n\<close> by simp
    hence \<open>f m < f i \<and> f i \<le> (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>ticks c (hamlet sub i)\<close> by simp
    hence \<open>ticks c (hamlet r (f i))\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>ticks c (hamlet r i)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> ticks c (hamlet sub i\<^sub>0)\<close> by blast
    with h have \<open>f m < f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m < i\<^sub>0 \<and> i\<^sub>0 \<le> n\<close> using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m \<le> i \<and> i \<le> f n \<and> ticks c (hamlet r i)}
          = image f {i. m \<le> i \<and> i \<le> n \<and> ticks c (hamlet sub i)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m \<le> i \<and> i \<le> n\<close> by simp
    hence \<open>f m \<le> f i \<and> f i \<le> (f n)\<close>
      using assms by (simp add: dilating_def dilating_fun_def strict_mono_less_eq)
    moreover from h have \<open>ticks c (hamlet sub i)\<close> by simp
    hence \<open>ticks c (hamlet r (f i))\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in>?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>ticks c (hamlet r i)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> ticks c (hamlet sub i\<^sub>0)\<close> by blast
    with h have \<open>f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m \<le> i\<^sub>0 \<and> i\<^sub>0 \<le> n\<close> using strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

text \<open>
  No tick can occur in a dilated run before the image of 0 by the dilation function.
\<close>
lemma empty_dilated_prefix:
  assumes \<open>dilating f sub r\<close>
  and     \<open>n < f 0\<close>
  shows   \<open>\<not>ticks c (hamlet r n)\<close>
proof
  { assume \<open>ticks c (hamlet r n)\<close>
    hence \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close> using no_tick_sub[OF assms(1)] by blast
    from this obtain n\<^sub>0 where \<open>f n\<^sub>0 = n\<close> by blast
    hence \<open>f n\<^sub>0 < f 0\<close> using assms(2) by simp
    moreover have \<open>strict_mono f\<close> using assms(1) dilating_def dilating_fun_def by blast
    ultimately have \<open>n\<^sub>0 < 0\<close> using strict_mono_less by blast
    hence False by simp
  } thus \<open>ticks c (hamlet r n) \<Longrightarrow> False\<close> .
qed

corollary empty_dilated_prefix':
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f 0 \<le> i \<and> i \<le> f n \<and> ticks c (hamlet r i)} = {i. i \<le> f n \<and> ticks c (hamlet r i)}\<close>
proof -
  from assms have \<open>strict_mono f\<close> using dilating_def dilating_fun_def by blast
  hence \<open>f 0 \<le> f n\<close> unfolding strict_mono_def by (simp add: less_mono_imp_le_mono)
  hence \<open>\<forall>i. i \<le> f n = (i < f 0) \<or> (f 0 \<le> i \<and> i \<le> f n)\<close> by auto
  hence \<open>{i. i \<le> f n \<and> ticks c (hamlet r i)}
        = {i. i < f 0 \<and> ticks c (hamlet r i)} \<union> {i. f 0 \<le> i \<and> i \<le> f n \<and> ticks c (hamlet r i)}\<close>
    by auto
  also have \<open>... = {i. f 0 \<le> i \<and> i \<le> f n \<and> ticks c (hamlet r i)}\<close>
     using empty_dilated_prefix[OF assms] by blast
  finally show ?thesis by simp
qed

corollary dilated_prefix:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. i \<le> f n \<and> ticks c (hamlet r i)}
          = image f {i. i \<le> n \<and> ticks c (hamlet sub i)}\<close>
proof -
  have \<open>{i. 0 \<le> i \<and> i \<le> f n \<and> ticks c (hamlet r i)}
        = image f {i. 0 \<le> i \<and> i \<le> n \<and> ticks c (hamlet sub i)}\<close>
    using dilated_ticks[OF assms] empty_dilated_prefix'[OF assms] by blast
  thus ?thesis by simp
qed

text \<open>
  The tick_count operator is preserved by dilation.
\<close>
lemma tick_count_sub:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count c (hamlet sub) n = tick_count c (hamlet r) (f n)\<close>
proof -
  have \<open>tick_count c (hamlet sub) n = card {i. i \<le> n \<and> ticks c (hamlet sub i)}\<close>
    using tick_count_def[of \<open>c\<close> \<open>hamlet sub\<close> \<open>n\<close>] .
  also have \<open>... = card (image f {i. i \<le> n \<and> ticks c (hamlet sub i)})\<close>
    using assms dilating_def dilating_injects[OF assms] by (simp add: card_image)
  also have \<open>... = card {i. i \<le> f n \<and> ticks c (hamlet r i)}\<close>
    using dilated_prefix[OF assms, symmetric, of \<open>n\<close> \<open>c\<close>] by simp
  also have \<open>... = tick_count c (hamlet r) (f n)\<close>
    using tick_count_def[of \<open>c\<close> \<open>hamlet r\<close> \<open>f n\<close>] by simp
  finally show ?thesis .
qed

text \<open>
  The tick_count_between operator is preserved by dilation.
\<close>
lemma tick_count_between_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>tick_count_between c (hamlet sub) m n = tick_count_between c (hamlet r) (f m) (f n)\<close>
proof -
  from assms have df:\<open>dilating_fun f (hamlet r)\<close> by (simp add: dilating_def)
  have \<open>card {p. m < p \<and> p \<le> n \<and> ticks c (hamlet sub p)}
      = card {p. m < p \<and> p \<le> n \<and> ticks c (hamlet r (f p))}\<close>
    using ticks_sub[OF assms, of \<open>c\<close>] by simp
  also have \<open>... = card {p. f m < p \<and> p \<le> f n \<and> ticks c (hamlet r p)}\<close>
    using ticks_as_often_right[OF df, of \<open>m\<close> \<open>n\<close> \<open>c\<close>] .
  finally show ?thesis unfolding tick_count_between_def .
qed

text \<open>
  The first_tick_since operator is preserved by dilation.
\<close>
lemma first_tick_since_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>first_tick_since c (hamlet sub) fr now = first_tick_since c (hamlet r) (f fr) (f now)\<close>
proof -
  from ticks_sub[OF assms]
    have 1:\<open>ticks c (hamlet sub now) = ticks c (hamlet r (f now))\<close> by blast
  from assms
    have 2:\<open>now \<ge> fr = (f now \<ge> f fr)\<close>
      by (simp add: dilating_def dilating_fun_def strict_mono_less_eq)
  have 3:\<open>(\<forall>t. (fr \<le> t \<and> t < now) \<longrightarrow> \<not>ticks c (hamlet sub t))
        = (\<forall>t. (f fr \<le> t \<and> t < f now) \<longrightarrow> \<not>ticks c (hamlet r t))\<close>
    using dilated_ticks_left[OF assms] by blast
  have \<open>first_tick_since c (hamlet sub) fr now
        = (ticks c (hamlet sub now) \<and> (now \<ge> fr)
        \<and> (\<forall>t. (fr \<le> t \<and> t < now) \<longrightarrow> \<not>ticks c (hamlet sub t)))\<close>
    by (simp add:first_tick_since_def)
  also have \<open>... = (ticks c (hamlet r (f now)) \<and> (f now \<ge> f fr)
                 \<and> (\<forall>t. (f fr \<le> t \<and> t < f now) \<longrightarrow> \<not>ticks c (hamlet r t)))\<close>
    using 1 2 3 by simp
  also have \<open>... = first_tick_since c (hamlet r) (f fr) (f now)\<close> by (simp add:first_tick_since_def)
  finally show ?thesis .
qed

text \<open>
  Special case when the origin is 0.
\<close>
lemma first_tick_since0_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>first_tick_since c (hamlet r) 0 (f n) = first_tick_since c (hamlet sub) 0 n\<close>
proof
  assume h1:\<open>first_tick_since c (hamlet r) 0 (f n)\<close>
  thus \<open>first_tick_since c (hamlet sub) 0 n\<close> using assms
    by (simp add: first_tick_since_def strict_mono_def dilating_def dilating_fun_def)
next
  assume h2:\<open>first_tick_since c (hamlet sub) 0 n\<close>
  hence p:\<open>first_tick_since c (hamlet r) (f 0) (f n)\<close>
    using first_tick_since_sub[OF assms, of \<open>c\<close> \<open>0\<close> \<open>n\<close>] by simp
  hence \<open>ticks c (hamlet r (f n)) \<and> f 0 \<le> f n = ticks c (hamlet r (f n)) \<and> 0 \<le> f n\<close>
    using empty_dilated_prefix[OF assms] using first_tick_since_def by blast
  moreover have \<open>(\<forall>t. f 0 \<le> t \<and> t < f n \<longrightarrow> \<not> ticks c (hamlet r t))
               = (\<forall>t. 0 \<le> t \<and> t < f n \<longrightarrow> \<not> ticks c (hamlet r t))\<close>
    using empty_dilated_prefix[OF assms] not_le_imp_less by blast
  ultimately show \<open>first_tick_since c (hamlet r) 0 (f n)\<close>
    using first_tick_since_def p by blast
qed

text \<open>
  Special case when the origin is the successor of a nat.
\<close>
lemma first_tick_since_suc_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>first_tick_since a (hamlet sub) (Suc n\<^sub>0) n\<close>
  shows   \<open>first_tick_since a (hamlet r) (Suc (f n\<^sub>0)) (f n)\<close>
proof -
  from first_tick_since_sub[OF assms(1)] assms(2)
    have 1:\<open>first_tick_since a (hamlet r) (f (Suc n\<^sub>0)) (f n)\<close> ..
  hence *:\<open>ticks a (hamlet r (f n))\<close> using first_tick_since_def by blast

  from assms(1) have 2:\<open>Suc (f n\<^sub>0) \<le> f (Suc n\<^sub>0)\<close>
    by (simp add: dilating_def dilating_fun_def strict_mono_def Suc_leI)
  with 1 have **:\<open>f n \<ge> Suc (f n\<^sub>0)\<close> using first_tick_since_def le_trans by blast

  have \<open>\<nexists>k. n\<^sub>0 < k \<and> k < Suc n\<^sub>0\<close> by simp
  with assms(1) have \<open>\<nexists>k. f n\<^sub>0 < f k \<and> f k < f (Suc n\<^sub>0) \<and> ticks a (hamlet r (f k))\<close>
    by (simp add: dilating_def dilating_fun_def strict_mono_less)
  hence \<open>\<nexists>t. f n\<^sub>0 < t \<and> t < f (Suc n\<^sub>0) \<and> ticks a (hamlet r t)\<close>
    using ticks_image_sub[OF assms(1), of \<open>a\<close>] by blast
  hence \<open>\<nexists>t. Suc (f n\<^sub>0) \<le> t \<and> t < f (Suc n\<^sub>0) \<and> ticks a (hamlet r t)\<close> by simp
  moreover from 1 have \<open>\<forall>t. (f (Suc n\<^sub>0) \<le> t \<and> t < f n) \<longrightarrow> \<not>ticks a (hamlet r t)\<close>
    using first_tick_since_def by blast
  ultimately have \<open>\<forall>t. (Suc (f n\<^sub>0) \<le> t \<and> t < f n) \<longrightarrow> \<not>ticks a (hamlet r t)\<close>
    using not_le by blast

  with * ** show ?thesis using first_tick_since_def by blast
qed

text \<open>
  The has_ticked_since operator is preserved by dilation.
\<close>
lemma has_ticked_since_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>has_ticked_since c (hamlet sub) fr now = has_ticked_since c (hamlet r) (f fr) (f now)\<close>
unfolding has_ticked_since_def using dilated_ticks[OF assms, of \<open>fr\<close> \<open>now\<close> \<open>c\<close>] by blast

text \<open>
  Special case for the prefix of the dilated run.
\<close>
lemma has_ticked_since_prefix:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>has_ticked_since c (hamlet r) 0 (f 0) = ticks c (hamlet r (f 0))\<close>
using empty_dilated_prefix[OF assms, of _ \<open>c\<close>] le_neq_trans
unfolding has_ticked_since_def by blast

text \<open>
  Special case when the origin is 0.
\<close>
lemma has_ticked_since0_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>has_ticked_since c (hamlet r) 0 (f n) = has_ticked_since c (hamlet sub) 0 n\<close>
proof -
  have f0n:\<open>f 0 \<le> f n\<close> using assms  dilating_fun_def strict_mono_def
    by (simp add: dilating_def strict_mono_less_eq)
  have f00:\<open>0 \<le> f 0\<close> using assms dilating_fun_def by blast
  have fn:\<open>0 \<le> f 0 \<and> f 0 \<le> f n\<close> using f00 f0n by simp
  from has_ticked_since_sub[OF assms, of \<open>c\<close> \<open>0\<close> \<open>n\<close>] have
    \<open>has_ticked_since c (hamlet sub) 0 n = has_ticked_since c (hamlet r) (f 0) (f n)\<close> .
  also have \<open>... = (has_ticked_since c (hamlet r) 0 (f 0)
                 \<or> has_ticked_since c (hamlet r) (f 0) (f n))\<close>
    using has_ticked_since_prefix[OF assms, of \<open>c\<close>]
          has_ticked_since_from_idem[OF f0n, of \<open>c\<close> \<open>hamlet r\<close>]
    by blast
  also have \<open>... = has_ticked_since c (hamlet r) 0 (f n)\<close>
    using has_ticked_since_split[OF fn, of \<open>c\<close> \<open>hamlet r\<close>, symmetric] .
  finally show ?thesis ..
qed

text \<open>
  Special case when the origin is the successor of a nat.
\<close>
lemma has_ticked_since_suc_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>has_ticked_since a (hamlet sub) (Suc n\<^sub>0) n\<close>
  shows   \<open>has_ticked_since a (hamlet r) (Suc (f n\<^sub>0)) (f n)\<close>
proof -
  from has_ticked_since_sub[OF assms(1)] assms(2)
    have \<open>has_ticked_since a (hamlet r) (f (Suc n\<^sub>0)) (f n)\<close> ..
  moreover from assms(1) have \<open>Suc (f n\<^sub>0) \<le> f (Suc n\<^sub>0)\<close>
    by (simp add: dilating_def dilating_fun_def strict_mono_def Suc_leI)
  ultimately show ?thesis using has_ticked_since_earlier by blast
qed

text \<open>
  The has_first_since operator is preserved by dilation.
\<close>
lemma has_first_since_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>has_first_since a b (hamlet sub) n\<^sub>0 n = has_first_since a b (hamlet r) (f n\<^sub>0) (f n)\<close>
by (simp add: first_tick_since_sub[OF assms] has_ticked_since_sub[OF assms] has_first_since_def)

text \<open>
  Special case when the origin is 0.
\<close>
lemma has_first_since0_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) 0 (f n) = has_first_since c\<^sub>1 c\<^sub>2 (hamlet sub) 0 n\<close>
by (simp add: first_tick_since0_sub[OF assms] has_ticked_since0_sub[OF assms] has_first_since_def)

text \<open>
  Special case when the origin is the successor of a nat.
\<close>
lemma has_first_since_suc_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>has_first_since a b (hamlet sub) (Suc n\<^sub>0) n\<close>
  shows   \<open>has_first_since a b (hamlet r) (Suc (f n\<^sub>0)) (f n)\<close>
unfolding has_first_since_def
proof
  show \<open>has_ticked_since a (hamlet r) (Suc (f n\<^sub>0)) (f n)\<close>
    using assms(2) unfolding has_first_since_def
    using has_ticked_since_suc_sub[OF assms(1)] by blast
next
  show \<open>first_tick_since b (hamlet r) (Suc (f n\<^sub>0)) (f n)\<close>
    using assms(2) unfolding has_first_since_def
    using first_tick_since_suc_sub[OF assms(1)] by blast
qed

text \<open>
  When either a or b ticks in the dilated run at some instant,
  this instant is the image of an instant by the dilated function.
  Notice that since a and b may not have the same type, the proof must be split
  in two cases.
\<close>
lemma ticks_ab_image:
  assumes \<open>dilating f sub r\<close>
  and \<open>ticks a (hamlet r n) \<or> ticks b (hamlet r n)\<close>
  shows \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
proof -
  from assms(2) show ?thesis
  proof
    from assms(1) dilating_def have *:\<open>dilating_fun f (hamlet r)\<close> by blast
    { assume  \<open>ticks a (hamlet r n)\<close>
      from ticks_image[OF * this] show \<open>\<exists>n\<^sub>0::nat. f n\<^sub>0 = n\<close> .
    }
    { assume  \<open>ticks b (hamlet r n)\<close>
      from ticks_image[OF * this] show \<open>\<exists>n\<^sub>0::nat. f n\<^sub>0 = n\<close> .
    }
  qed
qed

text \<open>
  When two clocks have both ticked at instant n and one of them has ticked for the first time no
  later than (f 0), they have both ticked at 0 in the subrun.
\<close>
lemma have_both_ticked_sub_f0:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>n. have_both_ticked a b (hamlet r) n \<and> has_first_since a b (hamlet r) (Suc n) (f 0)\<close>
  shows   \<open>have_both_ticked a b (hamlet sub) 0\<close>
proof -
  from assms(2) obtain n where
    nprop:\<open>have_both_ticked a b (hamlet r) n \<and> has_first_since a b (hamlet r) (Suc n) (f 0)\<close>
    by blast
  hence \<open>ticks a (hamlet r n) \<or> ticks b (hamlet r n)\<close> by (simp add: hbt_t)
  from ticks_ab_image[OF assms(1) this] obtain n\<^sub>0 where n0prop:\<open>f n\<^sub>0 = n\<close> by blast
  from nprop have \<open>f 0 \<ge> Suc n\<close> using hft_ht ht_not_empty by blast
  hence \<open>f 0 > f n\<^sub>0\<close> using n0prop by simp
  moreover have \<open>strict_mono f\<close> using assms(1) using dilating_def dilating_fun_def by blast
  ultimately have \<open>0 > n\<^sub>0\<close> using strict_mono_less by blast
  hence False by simp
  thus ?thesis by simp
qed

lemma have_both_ticked_sub_f0':
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>n. have_both_ticked a b (hamlet r) n \<and> has_first_since b a (hamlet r) (Suc n) (f 0)\<close>
  shows   \<open>have_both_ticked a b (hamlet sub) 0\<close>
proof -
  from assms(2) obtain n
    where nprop:\<open>have_both_ticked a b (hamlet r) n
               \<and> has_first_since b a (hamlet r) (Suc n) (f 0)\<close> by blast
  hence \<open>ticks a (hamlet r n) \<or> ticks b (hamlet r n)\<close> by (simp add: hbt_t)
  from ticks_ab_image[OF assms(1) this] obtain n\<^sub>0 where n0prop:\<open>f n\<^sub>0 = n\<close> by blast
  from nprop have \<open>f 0 \<ge> Suc n\<close> using hft_ht ht_not_empty by blast
  hence \<open>f 0 > f n\<^sub>0\<close> using n0prop by simp
  moreover have \<open>strict_mono f\<close> using assms(1) using dilating_def dilating_fun_def by blast
  ultimately have \<open>0 > n\<^sub>0\<close> using strict_mono_less by blast
  hence False by simp
  thus ?thesis by simp
qed

text \<open>
  The next two lemmas are used in the inductive proof of the preservation
  of have_both_ticked by dilation.
\<close>
lemma have_both_ticked_sub_fn:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>n. have_both_ticked a b (hamlet r) n \<and> has_first_since a b (hamlet r) (Suc n) (f (Suc m))\<close>
  and     \<open>\<forall>k \<le> m. have_both_ticked a b (hamlet r) (f k) = have_both_ticked a b (hamlet sub) k\<close>
  shows   \<open>have_both_ticked a b (hamlet sub) (Suc m)\<close>
proof -
  from assms(2) obtain n where
    nprop:\<open>have_both_ticked a b (hamlet r) n
         \<and> has_first_since a b (hamlet r) (Suc n) (f (Suc m))\<close> by blast
  hence \<open>ticks a (hamlet r n) \<or> ticks b (hamlet r n)\<close> by (simp add: hbt_t)
  from ticks_ab_image[OF assms(1) this] obtain n\<^sub>0 where n0prop:\<open>f n\<^sub>0 = n\<close> by blast
  from nprop have *:\<open>has_first_since a b (hamlet r) (Suc n) (f (Suc m))\<close> by simp
  hence \<open>first_tick_since b (hamlet r) (Suc n) (f (Suc m))\<close> unfolding has_first_since_def by simp
  hence \<open>f (Suc m) \<ge> Suc n\<close> unfolding first_tick_since_def by simp
  hence \<open>f (Suc m) > f n\<^sub>0\<close> using n0prop by simp
  moreover have smf:\<open>strict_mono f\<close> using assms(1) using dilating_def dilating_fun_def by blast
  ultimately have sucmn0:\<open>Suc m > n\<^sub>0\<close> using strict_mono_less by blast
  hence \<open>n\<^sub>0 \<le> m\<close> by simp
  with assms(3) have
    \<open>have_both_ticked a b (hamlet r) (f n\<^sub>0) = have_both_ticked a b (hamlet sub) n\<^sub>0\<close> by simp
  with n0prop nprop have 1:\<open>have_both_ticked a b (hamlet sub) n\<^sub>0\<close> by simp

  from * have \<open>\<exists>t. (Suc n) \<le> t \<and> t \<le> (f (Suc m)) \<and> ticks a (hamlet r t)\<close>
    unfolding has_first_since_def using has_ticked_since_def by blast
  from this obtain t\<^sub>0 where t0prop:\<open>(Suc n) \<le> t\<^sub>0 \<and> t\<^sub>0 \<le> (f (Suc m))
                                  \<and> ticks a (hamlet r t\<^sub>0)\<close> by blast
  hence \<open>ticks a (hamlet r t\<^sub>0)\<close> by simp
  from ticks_imp_ticks_subk[OF assms(1) this]
    obtain n\<^sub>1 where n1prop:\<open>f n\<^sub>1 = t\<^sub>0\<close> by blast
  with t0prop n0prop have \<open>f n\<^sub>0 < f n\<^sub>1\<close> by simp
  with assms(1) dilating_def dilating_fun_def strict_mono_less
    have \<open>n\<^sub>0 < n\<^sub>1\<close> by blast
  hence \<open>n\<^sub>1 \<ge> Suc n\<^sub>0\<close> by simp
  moreover from t0prop have \<open>has_ticked_since a (hamlet r) t\<^sub>0 (f (Suc m))\<close>
    by (simp add: has_ticked_since_from)
  hence \<open>has_ticked_since a (hamlet sub) n\<^sub>1 (Suc m)\<close>
    using n1prop has_ticked_since_sub[OF assms(1)] by blast
  ultimately have htsa:\<open>has_ticked_since a (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
    using has_ticked_since_earlier by blast

  from * have ftsb:\<open>first_tick_since b (hamlet r) (Suc n) (f (Suc m))\<close> unfolding has_first_since_def by simp
  have \<open>\<forall>t. Suc n\<^sub>0 \<le> t \<and> t < Suc m \<longrightarrow> \<not>ticks b (hamlet sub t)\<close>
  proof -
    {
      assume \<open>\<not>(\<forall>t. Suc n\<^sub>0 \<le> t \<and> t < Suc m \<longrightarrow> \<not>ticks b (hamlet sub t))\<close>
      hence \<open>\<exists>h\<^sub>0. Suc n\<^sub>0 \<le> h\<^sub>0 \<and> h\<^sub>0 < Suc m \<and> ticks b (hamlet sub h\<^sub>0)\<close> by simp
      from this obtain h\<^sub>0 where \<open>Suc n\<^sub>0 \<le> h\<^sub>0 \<and> h\<^sub>0 < Suc m \<and> ticks b (hamlet sub h\<^sub>0)\<close> by blast
      hence \<open>f (Suc n\<^sub>0) \<le> f h\<^sub>0 \<and> f h\<^sub>0 < f (Suc m) \<and> ticks b (hamlet r (f h\<^sub>0))\<close>
        using assms(1) dilating_def dilating_fun_def strict_monoD strict_mono_less_eq by fastforce
      moreover from n0prop have \<open>f (Suc n\<^sub>0) \<ge> Suc n\<close> using smf not_less_eq_eq strict_mono_less_eq by blast
      ultimately have \<open>Suc n \<le> f h\<^sub>0 \<and> f h\<^sub>0 < f (Suc m) \<and> ticks b (hamlet r (f h\<^sub>0))\<close> by simp
      hence \<open>\<not>first_tick_since b (hamlet r) (Suc n) (f (Suc m))\<close> using first_tick_since_def by blast
      with ftsb have False by simp
    }
    thus ?thesis by blast
  qed
  moreover from * have \<open>ticks b (hamlet r (f (Suc m)))\<close>
    unfolding has_first_since_def by (simp add:first_tick_since_def)
  hence \<open>ticks b (hamlet sub (Suc m))\<close> by (simp add: ticks_sub[OF assms(1)])
  ultimately have \<open>first_tick_since b (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
    using sucmn0 first_tick_since_def Suc_leI by blast
  with htsa have \<open>has_first_since a b (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
    unfolding has_first_since_def by simp
  with 1 show ?thesis using have_both_ticked.intros(3) by blast
qed

lemma have_both_ticked_sub_fn':
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>n. have_both_ticked a b (hamlet r) n \<and> has_first_since b a (hamlet r) (Suc n) (f (Suc m))\<close>
  and     \<open>\<forall>k \<le> m. have_both_ticked a b (hamlet r) (f k) = have_both_ticked a b (hamlet sub) k\<close>
  shows   \<open>have_both_ticked a b (hamlet sub) (Suc m)\<close>
proof -
  from assms(2) hbt_commutes have
    \<open>\<exists>n. have_both_ticked b a (hamlet r) n \<and> has_first_since b a (hamlet r) (Suc n) (f (Suc m))\<close>
  by blast
  moreover from assms(3) hbt_commutes[of \<open>a\<close> \<open>b\<close>] have
    \<open>\<forall>k \<le> m. have_both_ticked b a (hamlet r) (f k) = have_both_ticked b a (hamlet sub) k\<close>
    using hbt_commutes by blast
  ultimately have \<open>have_both_ticked b a (hamlet sub) (Suc m)\<close>
    using have_both_ticked_sub_fn[OF assms(1)] by blast
  from hbt_commutes[OF this] show ?thesis .
qed

text \<open>
  The have_both_ticked operator is preserved by dilation.
\<close>
lemma have_both_ticked_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f n) = have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) n\<close>
proof (induction n rule: nat_strong_induct)
  case 0 show ?case
  proof
    assume h1:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f 0)\<close>
    consider
      (a) \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) 0 (f 0)\<close>
    | (b) \<open>has_first_since c\<^sub>2 c\<^sub>1 (hamlet r) 0 (f 0)\<close>
    | (c) \<open>\<exists>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n\<^sub>0 \<and> has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) (Suc n\<^sub>0) (f 0)\<close>
    | (d) \<open>\<exists>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n\<^sub>0 \<and> has_first_since c\<^sub>2 c\<^sub>1 (hamlet r) (Suc n\<^sub>0) (f 0)\<close>
    using btn_btn0'[OF h1] by blast
    thus \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) 0\<close>
    proof cases
      case a thus ?thesis using assms has_first_since0_sub have_both_ticked.intros(1) by blast
    next
      case b thus ?thesis using assms has_first_since0_sub have_both_ticked.intros(2) by blast
    next
      case c thus ?thesis using have_both_ticked_sub_f0[OF assms(1) c] ..
    next
      case d thus ?thesis using have_both_ticked_sub_f0'[OF assms(1) d] ..
    qed
  next
    assume h2:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) 0\<close>
    hence \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet sub) 0 0 \<or> has_first_since c\<^sub>2 c\<^sub>1 (hamlet sub) 0 0\<close>
      unfolding has_first_since_def using bt0_bt0 first_tick_since_def hbt_htb by blast
    hence \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) 0 (f 0) \<or> has_first_since c\<^sub>2 c\<^sub>1 (hamlet r) 0 (f 0)\<close>
      using has_first_since0_sub[OF assms, of \<open>c\<^sub>1\<close> \<open>c\<^sub>2\<close> \<open>0\<close>]
            has_first_since0_sub[OF assms, of \<open>c\<^sub>2\<close> \<open>c\<^sub>1\<close> \<open>0\<close>] by blast
    thus \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f 0)\<close> using have_both_ticked.intros(1,2) by blast
  qed
next
  case (Suc m) print_facts show ?case
  proof
    assume h1:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f (Suc m))\<close>
    from this consider
      (a) \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) 0 (f (Suc m))\<close>
    | (b) \<open>has_first_since c\<^sub>2 c\<^sub>1 (hamlet r) 0 (f (Suc m))\<close>
    | (c) \<open>\<exists>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n\<^sub>0 \<and> has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) (Suc n\<^sub>0) (f (Suc m))\<close>
    | (d) \<open>\<exists>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n\<^sub>0 \<and> has_first_since c\<^sub>2 c\<^sub>1 (hamlet r) (Suc n\<^sub>0) (f (Suc m))\<close>
    using btn_btn0'[OF h1] by blast
    thus \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) (Suc m)\<close>
    proof cases
      case a thus ?thesis using assms has_first_since0_sub have_both_ticked.intros(1) by blast
    next
      case b thus ?thesis using assms has_first_since0_sub have_both_ticked.intros(2) by blast
    next
      case c show ?thesis using have_both_ticked_sub_fn[OF assms(1) c Suc.IH] .
    next
      case d show ?thesis using have_both_ticked_sub_fn'[OF assms(1) d Suc.IH] .
    qed
  next
    assume h2:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) (Suc m)\<close>
    from this consider
      (a) \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet sub) 0 (Suc m)\<close>
    | (b) \<open>has_first_since c\<^sub>2 c\<^sub>1 (hamlet sub) 0 (Suc m)\<close>
    | (c) \<open>\<exists>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) n\<^sub>0 \<and> has_first_since c\<^sub>1 c\<^sub>2 (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
    | (d) \<open>\<exists>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) n\<^sub>0 \<and> has_first_since c\<^sub>2 c\<^sub>1 (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
    using btn_btn0'[OF h2] by blast
    thus \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f (Suc m))\<close>
    proof cases
      case a thus ?thesis
        using assms has_first_since0_sub have_both_ticked.intros(1) by blast
    next
      case b thus ?thesis
        using assms has_first_since0_sub have_both_ticked.intros(2) by blast
    next
      case c
      from this obtain n\<^sub>0 where 
        1:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) n\<^sub>0\<close> and 2:\<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
        by blast
      from 2 have \<open>n\<^sub>0 \<le> m\<close> using hft_ht ht_not_empty by blast
      with Suc.IH 1 have \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f n\<^sub>0)\<close> by blast
      moreover from 2 assms has_first_since_suc_sub
        have \<open>has_first_since c\<^sub>1 c\<^sub>2 (hamlet r) (Suc (f n\<^sub>0)) (f (Suc m))\<close> by blast
      ultimately show ?thesis using have_both_ticked.intros(3) by blast
    next
      case d 
      from this obtain n\<^sub>0 where 
        1:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) n\<^sub>0\<close> and 2:\<open>has_first_since c\<^sub>2 c\<^sub>1 (hamlet sub) (Suc n\<^sub>0) (Suc m)\<close>
        by blast
      from 2 have \<open>n\<^sub>0 \<le> m\<close> using hft_ht ht_not_empty by blast
      with Suc.IH 1 have \<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f n\<^sub>0)\<close> by blast
      moreover from 2 assms has_first_since_suc_sub
        have \<open>has_first_since c\<^sub>2 c\<^sub>1 (hamlet r) (Suc (f n\<^sub>0)) (f (Suc m))\<close> by blast
      ultimately show ?thesis using have_both_ticked.intros(4) by blast
    qed
  qed
qed

text \<open>
  The between operator is preserved by dilation.
\<close>
lemma between_sub1:
  assumes \<open>dilating f sub r\<close>
  and     \<open>between a b (hamlet sub) n\<close>
  shows   \<open>between a b (hamlet r) (f n)\<close>
proof -
  from assms(2) between_def obtain m where
    mprop:\<open>m < n \<and> ticks a (hamlet sub m) \<and> (\<forall>k. m \<le> k \<and> k < n \<longrightarrow> \<not>ticks b (hamlet sub k))\<close>
  by blast
  with assms(1) have
    \<open>f m < f n \<and> ticks a (hamlet r (f m)) \<and> (\<forall>k. m \<le> k \<and> k < n \<longrightarrow> \<not>ticks b (hamlet r (f k)))\<close>
  by (simp add: dilating_def dilating_fun_def strict_monoD)
  hence \<open>f m < f n \<and> ticks a (hamlet r (f m)) \<and> (\<forall>k. f m \<le> k \<and> k < f n \<longrightarrow> \<not>ticks b (hamlet r k))\<close>
    using assms(1) dilating_def dilating_fun_image_left by blast
  thus ?thesis by (auto simp add: between_def)
qed

lemma between_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>between a b (hamlet sub) n = between a b (hamlet r) (f n)\<close>
proof
  assume \<open>between a b (hamlet sub) n\<close>
  from between_sub1[OF assms(1) this] show \<open>between a b (hamlet r) (f n)\<close> .
next
  assume h:\<open>between a b (hamlet r) (f n)\<close>
  with between_def obtain m where
    mprop: \<open>m < f n \<and> ticks a (hamlet r m) \<and> (\<forall>k. m \<le> k \<and> k < f n \<longrightarrow> \<not>ticks b (hamlet r k))\<close>
  by blast
  hence \<open>ticks a (hamlet r m)\<close> by simp
  from this obtain m\<^sub>0 where \<open>f m\<^sub>0 = m\<close>
    using assms dilating_def dilating_fun_def one_tick_occurs by blast
  with mprop have 
    \<open>f m\<^sub>0 < f n \<and> ticks a (hamlet r (f m\<^sub>0)) \<and> (\<forall>k. (f m\<^sub>0) \<le> k \<and> k < f n \<longrightarrow> \<not>ticks b (hamlet r k))\<close>
  by simp
  hence \<open>m\<^sub>0 < n \<and> ticks a (hamlet sub m\<^sub>0) \<and> (\<forall>k. m\<^sub>0 \<le> k \<and> k < n \<longrightarrow> \<not>ticks b (hamlet sub k))\<close>
    using assms dilating_def dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  thus \<open>between a b (hamlet sub) n\<close> using between_def by blast
qed

text \<open>
  Sporadic specifications are preserved in a dilated run.
\<close>
lemma sporadic_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> c sporadic \<tau>\<close>
    shows \<open>r \<in> c sporadic \<tau>\<close>
proof -
  from assms(1) is_subrun_def obtain f
    where \<open>dilating f sub r\<close> by blast
  hence \<open>\<forall>n. time sub n = time r (f n) 
           \<and> hamlet sub n = hamlet r (f n)\<close> by (simp add: dilating_def)
  moreover from assms(2) have
    \<open>sub \<in> {r. \<exists> n. (timep c) (time r n) = \<tau> \<and> ticks c (hamlet r n)}\<close> by (simp add: Sporadic_def)
  from this obtain k where \<open>(timep c) (time sub k) = \<tau> \<and> ticks c (hamlet sub k)\<close> by auto
  ultimately have \<open>(timep c) (time r (f k)) = \<tau> \<and> ticks c (hamlet r (f k))\<close> by simp
  thus ?thesis using Sporadic_def[of \<open>c\<close> \<open>\<tau>\<close>] by blast
qed

text \<open>
  Implications are preserved in a dilated run.
\<close>
lemma implies_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> c\<^sub>1 implies c\<^sub>2\<close>
    shows \<open>r \<in> c\<^sub>1 implies c\<^sub>2\<close>
proof -
  from assms(1) is_subrun_def obtain f where \<open>dilating f sub r\<close> by blast
  moreover from assms(2) Implies_def have
    \<open>sub \<in> {r. \<forall>n. ticks c\<^sub>1 (hamlet r n) \<longrightarrow> ticks c\<^sub>2 (hamlet r n)}\<close> by blast
  hence \<open>\<forall>n. ticks c\<^sub>1 (hamlet sub n) \<longrightarrow> ticks c\<^sub>2 (hamlet sub n)\<close> by blast
  ultimately have \<open>\<forall>n. ticks c\<^sub>1 (hamlet r n) \<longrightarrow> ticks c\<^sub>2 (hamlet r n)\<close>
    using ticks_imp_ticks_subk ticks_sub by blast
  thus ?thesis by (simp add: Implies_def)
qed

text \<open>
  Implies every specifications are preserved in dilated runs.
\<close>
lemma implies_every_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> c\<^sub>1 implies c\<^sub>2 every k\<close>
    shows \<open>r \<in> c\<^sub>1 implies c\<^sub>2 every k\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  from assms(2) ImpliesEvery_def have
    \<open>sub \<in> {r. \<forall>n. ticks c\<^sub>1 (hamlet r n)
                  \<and> (tick_count c\<^sub>1 (hamlet r) n) mod k = 0 \<longrightarrow> ticks c\<^sub>2 (hamlet r n)}\<close>
      by (rule back_subst)
  hence \<open>\<forall>n. ticks c\<^sub>1 (hamlet sub n)
                  \<and> (tick_count c\<^sub>1 (hamlet sub) n) mod k = 0 \<longrightarrow> ticks c\<^sub>2 (hamlet sub n)\<close> by simp
  hence **:\<open>\<forall>n. ticks c\<^sub>1 (hamlet r (f n))
                  \<and> (tick_count c\<^sub>1 (hamlet r) (f n)) mod k = 0 \<longrightarrow> ticks c\<^sub>2 (hamlet r (f n))\<close>
    by (simp add:ticks_sub[OF *] tick_count_sub[OF *])
  have \<open>\<forall>n. ticks c\<^sub>1 (hamlet r n)
                  \<and> (tick_count c\<^sub>1 (hamlet r) n) mod k = 0 \<longrightarrow> ticks c\<^sub>2 (hamlet r n)\<close>
  proof -
    { fix n
      assume assm:\<open>ticks c\<^sub>1 (hamlet r (f n))
                 \<and> tick_count c\<^sub>1 (hamlet r) (f n) mod k = 0 \<longrightarrow> ticks c\<^sub>2 (hamlet r (f n))\<close>
      have \<open>ticks c\<^sub>1 (hamlet r n)
         \<and> tick_count c\<^sub>1 (hamlet r) n mod k = 0 \<longrightarrow> ticks c\<^sub>2 (hamlet r n) \<close>
        using ** no_tick_sub[OF *] by (case_tac \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>, auto, blast)
    }
    with ** show ?thesis by simp
  qed
  thus ?thesis by (simp add: ImpliesEvery_def)
qed

text \<open> Tag relations are not strictly invariant through dilation \<close>
lemma tagrel_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> TagRelation c\<^sub>1 R c\<^sub>2\<close>
    shows \<open>r \<in> TagRelation c\<^sub>1 R c\<^sub>2\<close>
oops \<comment> \<open> No way: there is no other constrain than mono on time r in the subrun relation. \<close>

text \<open>
  Tag relations are preserved by contraction
\<close>
lemma tagrel_sub_inv:
  assumes \<open>sub \<lless> r\<close>
      and \<open>r \<in> TagRelation c\<^sub>1 R c\<^sub>2\<close>
    shows \<open>sub \<in> TagRelation c\<^sub>1 R c\<^sub>2\<close>
proof -
  from assms(1) is_subrun_def obtain f where df:\<open>dilating f sub r\<close> by blast
  moreover from assms(2) TagRelation_def have
    \<open>r \<in> {r. \<forall>n. ((timep c\<^sub>1) (time r n), (timep c\<^sub>2) (time r n)) \<in> R}\<close> by blast
  hence \<open>\<forall>n. ((timep c\<^sub>1) (time r n), (timep c\<^sub>2) (time r n)) \<in> R\<close> by simp
  hence \<open>\<forall>n. (\<exists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> ((timep c\<^sub>1) (time r n), (timep c\<^sub>2) (time r n)) \<in> R\<close> by simp
  hence \<open>\<forall>n\<^sub>0. ((timep c\<^sub>1) (time r (f n\<^sub>0)), (timep c\<^sub>2) (time r (f n\<^sub>0))) \<in> R\<close> by blast
  moreover from dilating_def df have \<open>time sub = (time r) \<circ> f\<close> by blast
  ultimately have \<open>\<forall>n\<^sub>0. ((timep c\<^sub>1) (time sub n\<^sub>0), (timep c\<^sub>2) (time sub n\<^sub>0)) \<in> R\<close> by auto
  thus ?thesis by (simp add: TagRelation_def)
qed

text \<open>
  A tag relation becomes a loose tag relation through dilation of a run.
\<close>
lemma loose_tagrel_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> TagRelation c\<^sub>1 R c\<^sub>2\<close>
    shows \<open>r \<in> LooseTagRelation c\<^sub>1 R c\<^sub>2\<close>
proof -
  from assms(1) is_subrun_def obtain f where \<open>dilating f sub r\<close> by blast
  moreover from assms(2) TagRelation_def have
    \<open>sub \<in> {r. \<forall>n. ((timep c\<^sub>1) (time r n), (timep c\<^sub>2) (time r n)) \<in> R}\<close> by blast
  hence \<open>\<forall>n. ((timep c\<^sub>1) (time sub n), (timep c\<^sub>2) (time sub n)) \<in> R\<close> by simp
  moreover have \<open>\<forall>n\<^sub>0. ((timep c\<^sub>1) (time r (f n\<^sub>0)), (timep c\<^sub>2) (time r (f n\<^sub>0))) \<in> R\<close>
    using calculation by (simp add:dilating_def)
  ultimately have
    \<open>\<forall>n. tick_occurs (hamlet r n) \<longrightarrow> ((timep c\<^sub>1) (time r n), (timep c\<^sub>2) (time r n)) \<in> R\<close>
    using ticks_image_sub' by blast
  thus ?thesis by (simp add: LooseTagRelation_def)
qed

text \<open>
  Time delayed implications are preserved by dilation.
\<close>
lemma timedelay_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> (c\<^sub>1 time-delayed by \<tau> on c\<^sub>2 implies c\<^sub>3)\<close>
    shows \<open>r \<in> (c\<^sub>1 time-delayed by \<tau> on c\<^sub>2 implies c\<^sub>3)\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  from assms(2) have \<open>\<forall>n. ticks c\<^sub>1 (hamlet sub n)
                          \<longrightarrow> (\<exists>m > n. ticks c\<^sub>3 (hamlet sub m)
                                    \<and> (timep c\<^sub>2) (time sub m) = (timep c\<^sub>2) (time sub n) + \<tau>)\<close>
  unfolding TimeDelayed_def by simp
  hence **:\<open>\<forall>n\<^sub>0. ticks c\<^sub>1 (hamlet r (f n\<^sub>0))
                  \<longrightarrow> (\<exists>m\<^sub>0 > n\<^sub>0. ticks c\<^sub>3 (hamlet r (f m\<^sub>0))
                             \<and>  (timep c\<^sub>2) (time r (f m\<^sub>0)) = (timep c\<^sub>2) (time r (f n\<^sub>0)) + \<tau>)\<close>
    using * by (simp add: dilating_def)
  hence \<open>\<forall>n. ticks c\<^sub>1 (hamlet r n)
                  \<longrightarrow> (\<exists>m > n. ticks c\<^sub>3 (hamlet r m)
                             \<and> (timep c\<^sub>2) (time r m) = (timep c\<^sub>2) (time r n) + \<tau>)\<close>
  proof -
    { fix n assume assm:\<open>ticks c\<^sub>1 (hamlet r n)\<close>
      from ticks_image_sub[OF * assm] obtain n\<^sub>0 where nfn0:\<open>n = f n\<^sub>0\<close> by blast
      with ** assm have
        \<open>(\<exists>m\<^sub>0 > n\<^sub>0. ticks c\<^sub>3 (hamlet r (f m\<^sub>0))
               \<and>  (timep c\<^sub>2) (time r (f m\<^sub>0)) = (timep c\<^sub>2) (time r (f n\<^sub>0)) + \<tau>)\<close> by blast
      hence \<open>(\<exists>m > n. ticks c\<^sub>3 (hamlet r m)
               \<and>  (timep c\<^sub>2) (time r m) = (timep c\<^sub>2) (time r n) + \<tau>)\<close>
        using * nfn0 strict_mono_def dilating_def dilating_fun_def by blast
    } thus ?thesis by simp
  qed
  thus ?thesis unfolding TimeDelayed_def by simp
qed

text \<open>
  Delayed implications are preserved by dilation.
\<close>
lemma delayed_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> (c\<^sub>1 delayed by d on c\<^sub>2 implies c\<^sub>3)\<close>
    shows \<open>r \<in> (c\<^sub>1 delayed by d on c\<^sub>2 implies c\<^sub>3)\<close>
proof -
  from assms(1) is_subrun_def obtain f
    where *:\<open>dilating f sub r\<close> by blast
  hence df:\<open>dilating_fun f (hamlet r)\<close> unfolding dilating_def by simp
  from assms(2) Delayed_def have
    \<open>\<forall>n. ticks c\<^sub>1 (hamlet sub n)
          \<longrightarrow> (\<exists>m > n. ticks c\<^sub>3 (hamlet sub m)
                    \<and> tick_count_between c\<^sub>2 (hamlet sub) n m = d)\<close> by blast
  hence **:\<open>\<forall>n\<^sub>0. ticks c\<^sub>1 (hamlet r (f n\<^sub>0))
             \<longrightarrow> (\<exists>m\<^sub>0 > n\<^sub>0. ticks c\<^sub>3 (hamlet r (f m\<^sub>0))
                          \<and> tick_count_between c\<^sub>2 (hamlet r) (f n\<^sub>0) (f m\<^sub>0) = d)\<close>
    by (simp add: ticks_sub[OF *] tick_count_between_sub[OF *])
  hence \<open>\<forall>n. ticks c\<^sub>1 (hamlet r n)
          \<longrightarrow> (\<exists>m > n. ticks c\<^sub>3 (hamlet r m)
                    \<and> tick_count_between c\<^sub>2 (hamlet r) n m = d)\<close>
  proof -
    { fix n assume assm:\<open>ticks c\<^sub>1 (hamlet r n)\<close>
      from ticks_image[OF df assm] obtain n\<^sub>0 where nfn0:\<open>n = f n\<^sub>0\<close> by blast
      with ** assm have
        \<open>(\<exists>m\<^sub>0 > n\<^sub>0. ticks c\<^sub>3 (hamlet r (f m\<^sub>0))
                \<and>  tick_count_between c\<^sub>2 (hamlet r) (f n\<^sub>0) (f m\<^sub>0) = d)\<close> by simp
      with nfn0 have
        \<open>(\<exists>m > n. ticks c\<^sub>3 (hamlet r m)
                \<and>  tick_count_between c\<^sub>2 (hamlet r) n m = d)\<close>
        using df dilating_fun_def strict_mono_less by blast
    }
    thus ?thesis by simp
  qed
  thus ?thesis unfolding Delayed_def by simp
qed

text \<open>
  Filtered implications are preserved by dilation.
\<close>
lemma filtered_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> (c\<^sub>1 filtered by s, k (rs, rk)* implies c\<^sub>2)\<close>
    shows \<open>r \<in>  (c\<^sub>1 filtered by s, k (rs, rk)* implies c\<^sub>2)\<close>
proof -
  from assms(1) is_subrun_def obtain f
    where *:\<open>dilating f sub r\<close> by blast
  from assms(2) Filtered_def have
    \<open>sub \<in> {r. (\<forall>n. ticks c\<^sub>1 (hamlet r n)
                  \<and> filter s k rs rk (tick_count c\<^sub>1 (hamlet r) n)
                \<longrightarrow> ticks c\<^sub>2 (hamlet r n)
               )}\<close> by blast
  hence \<open>\<forall>n. ticks c\<^sub>1 (hamlet sub n)
                  \<and> filter s k rs rk (tick_count c\<^sub>1 (hamlet sub) n)
                \<longrightarrow> ticks c\<^sub>2 (hamlet sub n)\<close> by simp
  hence **:\<open>\<forall>n\<^sub>0. ticks c\<^sub>1 (hamlet r (f n\<^sub>0))
                  \<and> filter s k rs rk (tick_count c\<^sub>1 (hamlet r) (f n\<^sub>0))
                \<longrightarrow> ticks c\<^sub>2 (hamlet r (f n\<^sub>0))\<close>
    by (simp add: tick_count_sub[OF *] ticks_sub[OF *])
  have \<open>\<forall>n. ticks c\<^sub>1 (hamlet r n) \<and> filter s k rs rk (tick_count c\<^sub>1 (hamlet r) n)
            \<longrightarrow> ticks c\<^sub>2 (hamlet r n)\<close>
  proof -
    { fix n
      assume assm:\<open>ticks c\<^sub>1 (hamlet r n) \<and> filter s k rs rk (tick_count c\<^sub>1 (hamlet r) n)\<close>
      hence \<open>ticks c\<^sub>1 (hamlet r n)\<close> by simp
      hence \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close> using no_tick_sub[OF *] by blast
      from this obtain n\<^sub>0 where nfn0:\<open>n = f n\<^sub>0\<close> by blast
      with ** assm have \<open>ticks c\<^sub>2 (hamlet r n)\<close> by simp
    }
    thus ?thesis by simp
  qed
  thus ?thesis by (simp add: Filtered_def)
qed

text \<open>
  Await implications are preserved by dilation.
\<close>
lemma await_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> await c\<^sub>1, c\<^sub>2 implies c\<^sub>3\<close>
    shows \<open>r \<in> await c\<^sub>1, c\<^sub>2 implies c\<^sub>3\<close>
proof -
  from assms(1) is_subrun_def obtain f
    where *:\<open>dilating f sub r\<close> by blast
  from assms(2) Await_def have
    \<open>sub \<in> {r. (\<forall>n. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n \<longrightarrow> ticks c\<^sub>3 (hamlet r n))}\<close> by blast
  hence \<open>\<forall>n. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet sub) n \<longrightarrow> ticks c\<^sub>3 (hamlet sub n)\<close> by simp
  hence **:\<open>\<forall>n\<^sub>0. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) (f n\<^sub>0) \<longrightarrow> ticks c\<^sub>3 (hamlet r (f n\<^sub>0))\<close>
    using have_both_ticked_sub[OF *, of \<open>c\<^sub>1\<close> \<open>c\<^sub>2\<close>] ticks_sub[OF *, of \<open>c\<^sub>3\<close>] by blast
  have \<open>\<forall>n. have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n \<longrightarrow> ticks c\<^sub>3 (hamlet r n)\<close>
  proof -
    { fix n
      assume assm:\<open>have_both_ticked c\<^sub>1 c\<^sub>2 (hamlet r) n\<close>
      from hbt_t[OF assm] have \<open>ticks c\<^sub>1 (hamlet r n) \<or> ticks c\<^sub>2 (hamlet r n)\<close> .
      from ticks_ab_image[OF * this] obtain n\<^sub>0 where nfn0:\<open>n = f n\<^sub>0\<close> by blast
      from nfn0 ** assm have \<open>ticks c\<^sub>3 (hamlet r n)\<close> by simp
    }
    thus ?thesis by simp
  qed
  thus ?thesis by (simp add: Await_def)
qed

text \<open>
  Sustained implications are preserved by dilation.
\<close>
lemma sustain_sub:
  assumes \<open>sub \<lless> r\<close>
  and     \<open>sub \<in> (m sustained from b to e implies s)\<close>
  shows   \<open>r \<in> (m sustained from b to e implies s)\<close>
proof -
  from assms(1) obtain f where fprop:\<open>dilating f sub r\<close> using is_subrun_def by blast
  from assms(2) have
    1:\<open>\<forall>n. between b e (hamlet sub) n \<and> ticks m ((hamlet sub) n) \<longrightarrow> ticks s ((hamlet sub) n)\<close>
    using SustainFromTo_def by blast
  hence
    *:\<open>\<forall>n. between b e (hamlet r) (f n) \<and> ticks m ((hamlet r) (f n)) \<longrightarrow> ticks s ((hamlet r) (f n))\<close>
    by (simp add: between_sub[OF fprop] ticks_sub[OF fprop])
  have
    \<open>\<forall>n. between b e (hamlet r) n \<and> ticks m ((hamlet r) n) \<longrightarrow> ticks s ((hamlet r) n)\<close>
  proof -
    { fix n
      assume h:\<open>between b e (hamlet r) n \<and> ticks m (hamlet r n)\<close>
      have \<open>ticks s (hamlet r n)\<close>
      proof (cases \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>)
        case True
          from this obtain n\<^sub>0 where n0prop:\<open>f n\<^sub>0 = n\<close> by blast
          with h have \<open>between b e (hamlet sub) n\<^sub>0 \<and> ticks m ((hamlet sub) n\<^sub>0)\<close>
            by (simp add: between_sub[OF fprop] ticks_sub[OF fprop])
          with 1 have \<open>ticks s ((hamlet sub) n\<^sub>0)\<close> by simp
          thus ?thesis using n0prop ticks_sub[OF fprop] by blast
      next
        case False
          hence \<open>\<not>ticks m (hamlet r n)\<close> using fprop dilating_def dilating_fun_def one_tick_occurs by blast
          with h have False by simp
          thus ?thesis ..
      qed
    }
    thus ?thesis by simp
  qed
  thus ?thesis by (simp add: SustainFromTo_def)
qed

end
