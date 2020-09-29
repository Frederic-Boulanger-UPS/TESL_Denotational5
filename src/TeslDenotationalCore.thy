theory TeslDenotationalCore
imports Main HOL.Real
begin

text \<open>
  We define here the semantic domain of TESL.
\<close>

section \<open> Preliminaries \<close>

text \<open>
  The rank of a system of clocks is its number of elementary clocks.
\<close>

class rank = 
  fixes   rank :: \<open>'a \<Rightarrow> nat\<close>
  assumes pos  : \<open>rank x > 0\<close>
    and   const: \<open>rank x = rank y\<close>

text \<open>
  Basic types are instances of rank.
\<close>

instantiation nat :: rank
begin
   definition rank_nat_def : \<open>rank (x::nat) = 1\<close>
   instance proof 
     show \<open>\<And>x::nat. 0 < rank x\<close> using rank_nat_def by simp
     show \<open>\<And>(x::nat) (y::nat). rank x = rank y\<close> using rank_nat_def by simp
   qed
end 

instantiation int :: rank
begin
   definition rank_int_def : \<open>rank (x::int) = 1\<close>
   instance proof 
     show \<open>\<And>x::int. 0 < rank x\<close> using rank_int_def by simp 
     show \<open>\<And>(x::int) (y::int). rank x = rank y\<close> using rank_int_def by simp
   qed 
end 

instantiation real :: rank
begin
   definition rank_real_def : \<open>rank (x::real) = 1\<close>
   instance proof
     show \<open>\<And>x::real. 0 < rank x\<close> using rank_real_def by simp 
     show \<open>\<And>(x::real) (y::real). rank x = rank y\<close> using rank_real_def by simp 
   qed
end 

text \<open>
  The product of to rank types is a rank too.
\<close>

instantiation prod :: (rank,rank)rank
begin
  definition rank_prod_def : \<open>rank (x::'a\<times>'b) = rank(fst x) + rank(snd x)\<close>
  instance proof
    show \<open>\<And>(x::'a\<times>'b). 0 < rank x\<close> using rank_prod_def by (simp add:pos) 

    { fix x y
      have \<open>rank x = rank (fst x) + rank (snd x)\<close> using rank_prod_def by simp
      moreover have \<open>rank y = rank (fst y) + rank (snd y)\<close> using rank_prod_def by simp
      moreover have \<open>rank (fst x) = rank (fst y)\<close> by (simp add: const)
      moreover have \<open>rank (snd x) = rank (snd y)\<close> by (simp add: const)
      ultimately have \<open>rank x = rank y\<close> by simp
    } thus \<open>\<And>(x::'a\<times>'b) (y::'a\<times>'b). rank x = rank y\<close> .
  qed
end

text \<open>
  The behavior of a TESL system of clocks is a series of instants where each clock
  has its own time. We define here an order on instants seen as tuples of dates.
  An instant is before another if all its components are less than the components of the other.
  An instant is strictly before another if it is before the other and at least one component
  is strictly less than the matching component in the other instant.
\<close>
instantiation prod :: (order,order)order
begin
   definition less_eq_prod_def : 
             \<open>(s::('a::order \<times> 'b::order)) \<le> t \<equiv> 
                    (fst s \<le> fst t \<and> snd s \<le> snd t)\<close>
   definition less_prod_def : 
             \<open>(s::('a::order \<times> 'b::order)) < t \<equiv> 
                       (s \<le> t \<and> (fst s < fst t \<or> snd s < snd t))\<close>
   instance proof 
     fix x::\<open>('a::order \<times> 'b::order)\<close> 
     fix y::\<open>('a::order \<times> 'b::order)\<close> 
     show   \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close> 
            unfolding less_eq_prod_def less_prod_def by (auto simp add: less_le_not_le)
   next
     fix x::\<open>('a::order \<times> 'b::order)\<close> 
     show   \<open>x \<le> x\<close>  
            unfolding less_eq_prod_def less_prod_def by auto
   next
     fix x::\<open>('a::order \<times> 'b::order)\<close> 
     fix y::\<open>('a::order \<times> 'b::order)\<close> 
     fix z::\<open>('a::order \<times> 'b::order)\<close> 
     assume \<open>x \<le> y\<close>
      and   \<open>y \<le> z\<close>
     then show   \<open>x \<le> z\<close> 
            unfolding less_eq_prod_def less_prod_def by auto
   next
     fix x::\<open>('a::order \<times> 'b::order)\<close> 
     fix y::\<open>('a::order \<times> 'b::order)\<close> 
     assume \<open>x \<le> y\<close>
     and    \<open>y \<le> x\<close>
     then show   \<open>x = y\<close>
            unfolding less_eq_prod_def less_prod_def by (auto simp add: prod.expand)
   qed
end

section\<open> Tesl Domain Foundation \<close>

text \<open> An instant is a list of booleans telling which clocks tick. \<close>
type_synonym event    = \<open>bool list\<close>
text \<open> The index of a clock in an instant is a nat. \<close>
type_synonym clockidx = \<open>nat\<close>
text \<open> The index of an instant in a run is a nat. \<close>
type_synonym instant  = \<open>nat\<close>

text \<open> The structure of time \<close>
type_synonym 'a time_structure = \<open>(instant \<Rightarrow> 'a)\<close>

text\<open> A hamlet associates an event to an instant: To tick or not to tick \<close>
type_synonym hamlet = \<open>instant \<Rightarrow> event\<close>

text\<open> Tell whether a tick occurs in an event. \<close>
definition tick_occurs :: \<open>bool list \<Rightarrow> bool\<close>
where
  \<open>tick_occurs l \<equiv> (\<exists>x \<in> set l. x)\<close>

definition tick_occurs_fun :: \<open>bool list \<Rightarrow> bool\<close> 
where     \<open>tick_occurs_fun \<equiv> foldl disj False \<close> 

lemma foldl_or:
  \<open>foldl disj False (b#l) = (b \<or> (foldl disj False l))\<close>
proof
  show \<open>foldl disj False (b # l) \<Longrightarrow> b \<or> foldl disj False l\<close>
    by (induction l, simp, case_tac b, simp+)
next
  show \<open>b \<or> foldl disj False l \<Longrightarrow> foldl disj False (b # l)\<close>
  proof -
    assume assm: \<open>b \<or> foldl disj False l\<close>
    { assume h:\<open>\<not> foldl disj False (b # l)\<close>
      hence \<open>\<not> foldl disj (False \<or> b) l\<close> using foldl_Cons by simp
      with assm have \<open>(False \<or> b)\<close> by fastforce
      hence \<open>foldl disj (False \<or> b) l\<close> by (simp add: rev_induct)
      with h have False by simp
    } thus ?thesis by blast
  qed
qed

lemma occurs_or: \<open>tick_occurs_fun (b # l) = (b \<or> (tick_occurs_fun l))\<close>
unfolding tick_occurs_fun_def using foldl_or .

lemma tick_occurs_is_fun: \<open>tick_occurs l = tick_occurs_fun l\<close>
proof (induction l)
  case Nil show ?case unfolding tick_occurs_def tick_occurs_fun_def by simp
next
  case (Cons b l)
    show ?case using occurs_or Cons.IH tick_occurs_def by simp
qed


text\<open>
The semantic domain of a single run consists of two components :
\<^enum> the time structure of the "global current time" evolution.
  The global current time is just the product of local effective times of the clocks of a 
  specification. The time structure is monotonous because time cannot regress in a run.
\<^enum> an additional component that captures the \<^emph>\<open>ticks\<close> of the clocks,
  i.e. the moments when the event modeled by a clock occurs, which may force
  surrounding processes into synchronization.

The latter component is also called the "Hamlet component": to tick or not to tick.
\<close>

class orderedrank = order + rank

instance nat::orderedrank ..
instance int::orderedrank ..

text \<open>
  In all runs, time is monotonic and the size of the hamlet is always the number of clocks.
\<close>
definition \<open>run_rep_prop (t::(('a::orderedrank)time_structure)) (h::hamlet)
            \<equiv> mono t \<and> (\<forall>n. rank (t n) = length (h n))\<close>

typedef (overloaded) ('a) run = \<open>{(t::(('a::orderedrank)time_structure), (h::hamlet)). 
                                      run_rep_prop t h
                                 }\<close>
proof -
  {
    fix c::\<open>'a::orderedrank\<close>
    fix r::\<open>'a time_structure \<times> hamlet\<close>
    assume assm: \<open>r = ((\<lambda>n::instant. c),  (\<lambda>n::instant. replicate (rank c) True))\<close>
      have \<open>mono (\<lambda>n::instant. c)\<close> by (simp add: monoI)
      moreover have \<open>length (replicate (rank c) True) = rank c\<close> by simp
      ultimately have \<open>r \<in> {(t, h). run_rep_prop t h}\<close> using assm by (simp add: run_rep_prop_def)
  }
  thus ?thesis by blast
qed

text \<open> Projection of a run onto its time structure. \<close>
definition time :: \<open>('a::orderedrank) run \<Rightarrow> 'a time_structure\<close>
where
  \<open>time r \<equiv> fst (Rep_run r)\<close>

text \<open> Projection of a run onto its events. \<close>
definition hamlet :: \<open>('a::orderedrank) run \<Rightarrow> hamlet\<close>
where
  \<open>hamlet r \<equiv> snd (Rep_run r)\<close>

lemma run_rep_has_prop[intro]:
  \<open>(t, h) = Rep_run (r::('a::orderedrank) run) \<Longrightarrow> run_rep_prop t h\<close>
using Rep_run[of \<open>r\<close>] by auto

lemma run_has_prop[intro]:
  \<open>run_rep_prop (time r) (hamlet r)\<close>
by (simp add: hamlet_def run_rep_has_prop time_def)

lemma mono_time_run[intro]:
  \<open>mono (time r)\<close>
using run_has_prop run_rep_prop_def by blast

lemma compat_time_hamlet[intro]:
  \<open>rank (time r n) = length (hamlet r n)\<close>
using run_rep_prop_def by blast

text \<open>
  The rank of a run is its number of clocks.
\<close>
instantiation run :: (orderedrank) rank
begin
  definition rank_run_def : \<open>rank (r::('a::orderedrank) run) = rank (time r 0)\<close>
  instance proof
    show \<open>\<And>r::('a::orderedrank) run. 0 < rank r\<close>
      unfolding rank_run_def using rank_class.pos .
    show \<open>\<And>(r\<^sub>1::('a::orderedrank) run) (r\<^sub>2::('a::orderedrank) run). rank r\<^sub>1 = rank r\<^sub>2\<close>
      unfolding rank_run_def by (simp add: rank_class.const)
  qed
end 

lemma rank_any_time:\<open>rank r = rank (time r n)\<close>
using rank_run_def[of \<open>r\<close>] rank_class.const[of \<open>time r 0\<close> \<open>time r n\<close>] by simp

lemma rank_any_hamlet:\<open>length (hamlet r n) = rank r\<close>
proof -
  from rank_any_time have \<open>rank r = rank (time r n)\<close> .
  with run_has_prop have \<open>rank r = length (hamlet r n)\<close> using run_rep_prop_def by auto
  thus ?thesis ..
qed

instantiation prod :: (orderedrank, orderedrank) orderedrank
begin
  instance proof qed
end

text \<open>
  Projection of a run onto its components: we project the time structure onto the component
  and keep only the corresponding occurrences of ticks in the hamlet.
\<close>
definition fst\<^sub>r\<^sub>u\<^sub>n :: \<open>('a::orderedrank \<times> 'b::orderedrank) run \<Rightarrow> 'a run\<close>
where     \<open>fst\<^sub>r\<^sub>u\<^sub>n r = Abs_run ((\<lambda>n. fst (time r n)), (\<lambda>n. take (rank (fst (time r n))) (hamlet r n)))\<close>

definition snd\<^sub>r\<^sub>u\<^sub>n :: \<open>('a::orderedrank \<times> 'b::orderedrank) run \<Rightarrow> 'b run\<close>
where     \<open>snd\<^sub>r\<^sub>u\<^sub>n r = Abs_run ((\<lambda>n. snd (time r n)), (\<lambda>n. drop (rank (fst (time r n))) (hamlet r n)))\<close>

definition prod\<^sub>r\<^sub>u\<^sub>n :: \<open>('a::orderedrank) run \<Rightarrow> 'b::orderedrank run \<Rightarrow> ('a \<times> 'b) run\<close> (infix "\<times>\<^sub>r\<^sub>u\<^sub>n" 60)
where
  \<open>r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2 \<equiv> Abs_run ((\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n)), (\<lambda>n. (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n)))\<close>

text \<open>
  The projections of a run and the product of two runs are runs.
\<close>
lemma fstrun_is_run:
  \<open>run_rep_prop (time (fst\<^sub>r\<^sub>u\<^sub>n r)) (hamlet (fst\<^sub>r\<^sub>u\<^sub>n r))\<close>
by (simp add: run_has_prop)

lemma sndrun_is_run:
  \<open>run_rep_prop (time (snd\<^sub>r\<^sub>u\<^sub>n r)) (hamlet (snd\<^sub>r\<^sub>u\<^sub>n r))\<close>
by (simp add: run_has_prop)

lemma prod_run_is_run:
  \<open>run_rep_prop (time (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2)) (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2))\<close>
by (simp add: run_has_prop)

lemma take_as_long:
  assumes \<open>n \<le> length l\<close>
  shows   \<open>n = length (take n l)\<close>
using assms by (simp add: min.absorb2)

lemma drop_as_long:
  assumes \<open>n \<le> length l\<close>
  shows   \<open>(length l) - n = length (drop n l)\<close>
using assms by (simp add: min.absorb2)

lemma rank_fst_le: \<open>rank (fst x) \<le> rank x\<close>
by (simp add: rank_prod_def)

lemma rank_snd_le: \<open>rank (snd x) \<le> rank x\<close>
by (simp add: rank_prod_def)

lemma fst_run_rep:
  \<open>mono (\<lambda>n. fst (time r n))
  \<and> (\<forall>n. rank (fst (time r n)) = length (take (rank (fst (time r n))) (hamlet r n)))\<close>
proof
  have mtr:\<open>mono (time r)\<close> by (simp add: mono_time_run)
  thus \<open>mono (\<lambda>n. fst (time r n))\<close> by (simp add: run_has_prop less_eq_prod_def mono_def)
next
  have \<open>\<forall>n. rank (fst (time r n)) \<le> rank (time r n)\<close> using rank_fst_le ..
  hence \<open>\<forall>n. rank (fst (time r n)) \<le> length (hamlet r n)\<close> by (simp add: compat_time_hamlet)
  with take_as_long show 
    \<open>\<forall>n. rank (fst (time r n)) = length (take (rank (fst (time r n))) (hamlet r n))\<close> by auto
qed

lemma snd_run_rep:
  \<open>mono (\<lambda>n. snd (time r n))
  \<and> (\<forall>n. rank (snd (time r n)) = length (drop (rank (fst (time r n))) (hamlet r n)))\<close>
proof
  have mtr:\<open>mono (time r)\<close> by (simp add: mono_time_run)
  thus \<open>mono (\<lambda>n. snd (time r n))\<close> by (simp add: less_eq_prod_def mono_def)
next
  { fix n
    from compat_time_hamlet[of \<open>r\<close> \<open>n\<close>] rank_prod_def[of \<open>time r n\<close>] have
      \<open>length (hamlet r n) = rank (fst (time r n)) + rank (snd (time r n))\<close> by simp
    with diff_add_inverse have
      \<open>rank (snd (time r n)) = length (hamlet r n) - rank (fst (time r n))\<close> by simp
    also have \<open>rank (fst (time r n)) \<le> rank (time r n)\<close> using rank_fst_le .
    hence \<open>rank (fst (time r n)) \<le> length (hamlet r n)\<close> by (simp add: compat_time_hamlet)
    from drop_as_long[OF this] have
      \<open>(length (hamlet r n)) - (rank (fst (time r n))) =
        length (drop (rank (fst (time r n))) (hamlet r n))\<close> .
    finally have \<open>rank (snd (time r n)) = length (drop (rank (fst (time r n))) (hamlet r n))\<close> .
  }
  thus \<open>\<forall>n. rank (snd (time r n)) = length (drop (rank (fst (time r n))) (hamlet r n))\<close> ..
qed

lemma prod_run_rep:
  \<open>mono (\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n))
  \<and> (\<forall>n. rank (time r\<^sub>1 n, time r\<^sub>2 n) = length ((hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n)))\<close>
proof
  have \<open>mono (time r\<^sub>1)\<close> by (simp add: mono_time_run)
  moreover have \<open>mono (time r\<^sub>2)\<close> by (simp add: mono_time_run)
  ultimately show \<open>mono (\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n))\<close> by (simp add: less_eq_prod_def mono_def)

  have \<open>\<forall>n. rank (time r\<^sub>1 n) = length (hamlet r\<^sub>1 n)\<close> by (simp add: compat_time_hamlet)
  moreover have \<open>\<forall>n. rank (time r\<^sub>2 n) = length (hamlet r\<^sub>2 n)\<close> by (simp add: compat_time_hamlet)
  ultimately show \<open>\<forall>n. rank (time r\<^sub>1 n, time r\<^sub>2 n) = length ((hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))\<close>
    by (simp add: rank_prod_def)
qed

lemma fst_run_rep':\<open>((\<lambda>n. fst (time r n)), (\<lambda>n. take (rank (fst (time r n))) (hamlet r n)))
                     \<in> {(t, h). run_rep_prop t h}\<close>
using fst_run_rep by (simp add: run_rep_prop_def)

lemma snd_run_rep':\<open>((\<lambda>n. snd (time r n)), (\<lambda>n. drop (rank (fst (time r n))) (hamlet r n)))
                     \<in> {(t, h). run_rep_prop t h}\<close>
using snd_run_rep by (simp add: run_rep_prop_def)

lemma prod_run_rep':\<open>((\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n)), (\<lambda>n. (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n)))
                     \<in> {(t, h). run_rep_prop t h}\<close>
using prod_run_rep by (simp add: run_rep_prop_def)

lemma time_fst_time:
  \<open>time (fst\<^sub>r\<^sub>u\<^sub>n r) = (\<lambda>n. fst (time r n))\<close>
proof
  let ?REP = \<open>((\<lambda>n. fst (time r n)), (\<lambda>n. take (rank (fst (time r n))) (hamlet r n)))\<close>
  have \<open>Rep_run (Abs_run ?REP) = ?REP\<close> using Abs_run_inverse[OF fst_run_rep'] .
  hence \<open>time (fst\<^sub>r\<^sub>u\<^sub>n r) = fst ?REP\<close> unfolding fst\<^sub>r\<^sub>u\<^sub>n_def time_def by simp
  also have \<open>... = (\<lambda>n. fst (time r n))\<close> by simp
  finally show \<open>\<And>n. time (fst\<^sub>r\<^sub>u\<^sub>n r) n = fst (time r n)\<close> by simp
qed

lemma time_snd_time:
  \<open>time (snd\<^sub>r\<^sub>u\<^sub>n r) = (\<lambda>n. snd (time r n))\<close>
proof
  let ?REP = \<open>((\<lambda>n. snd (time r n)), (\<lambda>n. drop (rank (fst (time r n))) (hamlet r n)))\<close>
  have \<open>Rep_run (Abs_run ?REP) = ?REP\<close> using Abs_run_inverse[OF snd_run_rep'] .
  hence \<open>time (snd\<^sub>r\<^sub>u\<^sub>n r) = fst ?REP\<close> unfolding snd\<^sub>r\<^sub>u\<^sub>n_def time_def by simp
  also have \<open>... = (\<lambda>n. snd (time r n))\<close> by simp
  finally show \<open>\<And>n. time (snd\<^sub>r\<^sub>u\<^sub>n r) n = snd (time r n)\<close> by simp
qed

lemma time_prod_time: \<open>time (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = (\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n))\<close>
proof
  let ?REP = \<open>((\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n)), (\<lambda>n. (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n)))\<close>
  have \<open>Rep_run (Abs_run ?REP) = ?REP\<close> using Abs_run_inverse[OF prod_run_rep'] .
  hence \<open>time (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = fst ?REP\<close> unfolding prod\<^sub>r\<^sub>u\<^sub>n_def time_def by simp
  also have \<open>... = (\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n))\<close> by simp
  finally show \<open>\<And>n. time (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n = (time r\<^sub>1 n, time r\<^sub>2 n)\<close> by simp
qed

lemma hamlet_fst_hamlet:
  \<open>hamlet (fst\<^sub>r\<^sub>u\<^sub>n r) = (\<lambda>n. take (rank (fst (time r n))) (hamlet r n))\<close>
proof
  let ?REP = \<open>((\<lambda>n. fst (time r n)), (\<lambda>n. take (rank (fst (time r n))) (hamlet r n)))\<close>
  have \<open>Rep_run (Abs_run ?REP) = ?REP\<close> using Abs_run_inverse[OF fst_run_rep'] .
  hence \<open>hamlet (fst\<^sub>r\<^sub>u\<^sub>n r) = snd ?REP\<close> unfolding fst\<^sub>r\<^sub>u\<^sub>n_def hamlet_def by simp
  also have \<open>... = (\<lambda>n. take (rank (fst (time r n))) (hamlet r n))\<close> by simp
  finally show \<open>\<And>n. hamlet (fst\<^sub>r\<^sub>u\<^sub>n r) n = take (rank (fst (time r n))) (hamlet r n)\<close> by simp
qed

lemma hamlet_snd_hamlet:
  \<open>hamlet (snd\<^sub>r\<^sub>u\<^sub>n r) = (\<lambda>n. drop (rank (fst (time r n))) (hamlet r n))\<close>
proof
  let ?REP = \<open>((\<lambda>n. snd (time r n)), (\<lambda>n. drop (rank (fst (time r n))) (hamlet r n)))\<close>
  have \<open>Rep_run (Abs_run ?REP) = ?REP\<close> using Abs_run_inverse[OF snd_run_rep'] .
  hence \<open>hamlet (snd\<^sub>r\<^sub>u\<^sub>n r) = snd ?REP\<close> unfolding snd\<^sub>r\<^sub>u\<^sub>n_def hamlet_def by simp
  also have \<open>... = (\<lambda>n. drop (rank (fst (time r n))) (hamlet r n))\<close> by simp
  finally show \<open>\<And>n. hamlet (snd\<^sub>r\<^sub>u\<^sub>n r) n = drop (rank (fst (time r n))) (hamlet r n)\<close> by simp
qed

lemma hamlet_prod_hamlet:
  \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = (\<lambda>n. (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))\<close>
proof
  let ?REP = \<open>((\<lambda>n. (time r\<^sub>1 n, time r\<^sub>2 n)), (\<lambda>n. (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n)))\<close>
  have \<open>Rep_run (Abs_run ?REP) = ?REP\<close> using Abs_run_inverse[OF prod_run_rep'] .
  hence \<open>hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = snd ?REP\<close> unfolding prod\<^sub>r\<^sub>u\<^sub>n_def hamlet_def by simp
  also have \<open>... = (\<lambda>n. (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))\<close> by simp
  finally show \<open>\<And>n. hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n = (hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n)\<close> by simp
qed

lemma rank_fst:
  \<open>rank (fst\<^sub>r\<^sub>u\<^sub>n r) = rank (fst (time r 0))\<close>
unfolding rank_run_def using time_fst_time[of \<open>r\<close>] by simp

lemma rank_snd:
  \<open>rank (snd\<^sub>r\<^sub>u\<^sub>n r) = rank (snd (time r 0))\<close>
unfolding rank_run_def using time_snd_time[of \<open>r\<close>] by simp

lemma rank_run_prod:
  \<open>rank (r::('a::{orderedrank} \<times> 'b::{orderedrank}) run)
   = rank (fst\<^sub>r\<^sub>u\<^sub>n r) + rank (snd\<^sub>r\<^sub>u\<^sub>n r)\<close>
using rank_fst[of \<open>r\<close>] rank_snd[of \<open>r\<close>] rank_prod_def[of \<open>time r 0\<close>] rank_run_def[of \<open>r\<close>] by simp

lemma rank_run_prod_any:
  \<open>rank (r::('a::{orderedrank} \<times> 'b::{orderedrank}) run)
 = rank (r\<^sub>1::'a run) + rank (r\<^sub>2::'b run)\<close>
proof -
  have \<open>rank r = rank (time r 0)\<close> by (simp add: rank_run_def)
  also have \<open>... = rank ((time r\<^sub>1 0), (time r\<^sub>2 0))\<close> using rank_class.const .
  also have \<open>... = rank (time r\<^sub>1 0) + rank (time r\<^sub>2 0)\<close> by (simp add: rank_prod_def)
  finally show \<open> rank r = rank r\<^sub>1 + rank r\<^sub>2\<close> by (simp add: rank_run_def)
qed

lemma run_prod_rank:\<open>rank (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = rank r\<^sub>1 + rank r\<^sub>2\<close>
using rank_run_prod_any .

lemma fst_run_proj:\<open>fst\<^sub>r\<^sub>u\<^sub>n (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = r\<^sub>1\<close>
proof -
  have lh:\<open>\<forall>n. length (hamlet r\<^sub>1 n) = rank (time r\<^sub>1 n)\<close> by (simp add: compat_time_hamlet)
  have \<open>fst\<^sub>r\<^sub>u\<^sub>n (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = Abs_run ((\<lambda>n. time r\<^sub>1 n),
                                     (\<lambda>n. (hamlet r\<^sub>1 n)))\<close>
    unfolding fst\<^sub>r\<^sub>u\<^sub>n_def
    using time_prod_time[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close>] hamlet_prod_hamlet[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close>] lh by simp
  thus ?thesis by (simp add: Rep_run_inverse hamlet_def time_def)
qed

lemma snd_run_proj:\<open>snd\<^sub>r\<^sub>u\<^sub>n (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = r\<^sub>2\<close>
proof -
  have lh:\<open>\<forall>n. length (hamlet r\<^sub>1 n) = rank (time r\<^sub>1 n)\<close> by (simp add: compat_time_hamlet)
  have \<open>snd\<^sub>r\<^sub>u\<^sub>n (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) = Abs_run ((\<lambda>n. time r\<^sub>2 n),
                                     (\<lambda>n. (hamlet r\<^sub>2 n)))\<close>
    unfolding snd\<^sub>r\<^sub>u\<^sub>n_def
    using time_prod_time[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close>] hamlet_prod_hamlet[of \<open>r\<^sub>1\<close> \<open>r\<^sub>2\<close>] lh by simp
  thus ?thesis by (simp add: Rep_run_inverse hamlet_def time_def)
qed

type_synonym ('a) runs = \<open>('a) run set\<close>

section\<open> The semantic domain of Tesl is a lattice \<close>

text \<open>
  The most permissive TESL specification allows all well formed runs.
\<close>
definition TeslTop :: \<open>('a::orderedrank) runs\<close> ("\<top>")
where     \<open>\<top> \<equiv> {r. run_rep_prop (time r) (hamlet r)}\<close>

text \<open>
  The most restrictive TESL specification allows no run.
\<close>
definition TeslBot :: \<open>('a::order) runs\<close> ("\<bottom>")
where     \<open>\<bottom> \<equiv> {}\<close>

(* Runs that start after \<tau> *)
definition TeslTopFrom :: \<open>'a \<Rightarrow> ('a::orderedrank) runs\<close> ("\<top>\<^bsub>\<le>_\<^esub>")
where     \<open>\<top>\<^bsub>\<le>\<tau>\<^esub> \<equiv> {r. run_rep_prop (time r) (hamlet r) \<and> \<tau> \<le> (time r) 0}\<close>

lemma foundation1 [intro]:
  \<open>r \<in> \<top>\<^bsub>\<le>\<tau>\<^esub> \<Longrightarrow> run_rep_prop (time r) (hamlet r) \<and> \<tau> \<le> (time r) 0 \<close>
by (simp add: TeslTopFrom_def)

text \<open> Composition of TESL specs: the runs have to satisfy both specs. \<close>
definition TeslComp :: \<open>('a::order) runs \<Rightarrow> 'a runs \<Rightarrow> 'a runs\<close> (infixl  "\<otimes>" 55)
where     \<open>S \<otimes> T \<equiv> S \<inter> T\<close>

text \<open>
  If a run satisfies two specifications, it satisfies their composition.
\<close>
lemma teslcomp:
  assumes \<open>r \<in> S\<close>
  and     \<open>r \<in> T\<close>
  shows   \<open>r \<in> S \<otimes> T\<close>
using assms by (simp add: TeslComp_def)

text \<open> Composing a spec with itself yields the same spec \<close>
lemma idem : \<open>S \<otimes> S = S\<close>
unfolding TeslComp_def by simp

text \<open> The composition of specifications commutes \<close>
lemma commute : \<open>S \<otimes> T = T \<otimes> S\<close>
unfolding TeslComp_def
by (simp add: Int_commute)

text \<open> The composition of specifications is associative \<close>
lemma assoc : \<open>S \<otimes> (T \<otimes> U) = (S \<otimes> T) \<otimes> U\<close>
unfolding TeslComp_def
by blast

text \<open> The empty specification is neutral for composition \<close>
lemma all_runs_in_top:\<open>S \<subseteq> \<top>\<close>
using TeslTop_def by auto
                                                                   
lemma idem_top : \<open>\<top> \<otimes> S = S\<close>
unfolding TeslComp_def using all_runs_in_top by blast

text \<open> Composing with the unsatisfiable specification yields the unsatisfiable specification. \<close>
lemma bot_strict : \<open>\<bottom> \<otimes> S = \<bottom>\<close>
unfolding TeslComp_def TeslBot_def by simp

text \<open> The composition of two specifications is stricter than each specification. \<close>
lemma \<open>S \<otimes> S' \<subseteq> S\<close>
unfolding TeslComp_def by simp

section \<open> Tesl clocks \<close>

text \<open>
A clock has two facets :
\begin{itemize}
  \item it is a projection from the denotational universe @{typ '\<AA>}
        of a system run onto a particular time line
  \item it is a projection from the hamlet of the system run onto its own hamlet component
\<close>

type_synonym ('a,'b)\<H> = \<open>(('a \<Rightarrow> 'b) \<times> clockidx)\<close>

\<comment> \<open>A way to build only consistent clocks (an idea by Chantal Keller)\<close>
definition clock0::\<open>(('a\<times>'b),'a)\<H>\<close>
where \<open>clock0 \<equiv> (fst,0)\<close>

fun clock_suc::\<open>('a, 'b)\<H> \<Rightarrow> ('c \<times> 'a, 'b)\<H>\<close>
  where \<open>clock_suc (f, n) = ((f\<circ>snd), (Suc n))\<close>

text \<open> Projection of a clock onto its time component. \<close>
abbreviation \<open>timep \<equiv> fst\<close>
text \<open> Projection of a clock onto its hamlet index. \<close>
abbreviation \<open>index \<equiv> snd\<close>

lemma \<open>timep clock0 = fst\<close> by (simp add: clock0_def)
lemma \<open>index clock0 = 0\<close> by (simp add: clock0_def)
lemma \<open>timep (clock_suc clock0) = fst\<circ>snd\<close> by (simp add: clock0_def)
lemma \<open>index (clock_suc clock0) = 1\<close> by (simp add: clock0_def)
lemma \<open>timep (clock_suc (clock_suc clock0)) = fst\<circ>snd\<circ>snd\<close> by (simp add: clock0_def)
lemma \<open>index (clock_suc (clock_suc clock0)) = 2\<close> by (simp add: clock0_def)

value \<open>(timep clock0) (a, b, c, ())\<close>
value \<open>(timep (clock_suc clock0)) (a, b, c, ())\<close>
value \<open>(timep (clock_suc (clock_suc clock0))) (a, b, c, ())\<close>

value \<open>[a, b, c]!(index clock0)\<close>
value \<open>[a, b, c]!(index (clock_suc clock0))\<close>
value \<open>[a, b, c]!(index (clock_suc (clock_suc clock0)))\<close>

\<comment> \<open>****************************\<close>

abbreviation timeOfClockOnRun ::\<open>('a::orderedrank,'b)\<H> \<Rightarrow> 'a run \<Rightarrow> nat \<Rightarrow> 'b\<close>
             ("timeof _ in _ at _")
where \<open>timeof c in r at n \<equiv> ((timep c) (time r n))\<close>

end
