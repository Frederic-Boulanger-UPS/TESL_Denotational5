theory TeslDenotationalRelations

imports TeslDenotationalOperators

begin

text \<open>
  Definition of the relations between clocks in TESL.
\<close>

text \<open>
  Sporadic forces a clock to have a tick with a given time stamp (or tag).
\<close>
definition Sporadic :: \<open>('\<AA>,'b)\<H> \<Rightarrow> 'b \<Rightarrow> ('\<AA>::orderedrank) runs\<close> 
                       (infixl "sporadic" 55)
where \<open>(H sporadic \<tau>) = {r. \<exists> n. (timeof H in r at n) = \<tau> \<and> ticks H (hamlet r n)}\<close>

text \<open>
  When a clock A implies a clock B, B must tick at each instant where A ticks.
\<close>
definition Implies :: \<open>('\<AA>,'b)\<H> \<Rightarrow> ('\<AA>,'c)\<H> \<Rightarrow> ('\<AA>::orderedrank) runs\<close> (infixl "implies" 55)
where \<open>(H\<^sub>1 implies H\<^sub>2) = {r. \<forall>n. ticks H\<^sub>1 (hamlet r n) \<longrightarrow> ticks H\<^sub>2 (hamlet r n)}\<close>

text \<open>
  ImpliesEvery is similar to Implies, but only every k ticks.
\<close>
definition ImpliesEvery :: \<open>('\<AA>,'b)\<H> \<Rightarrow> ('\<AA>,'c)\<H> \<Rightarrow> nat \<Rightarrow> ('\<AA>::orderedrank) runs\<close> 
                           ( "_ implies _ every _" [70,70,70] 55)
where \<open>H\<^sub>1 implies H\<^sub>2 every k = {r. \<forall>n. ticks H\<^sub>1 (hamlet r n)
                                    \<and> (tick_count H\<^sub>1 (hamlet r) n) mod k = 0 
                                          \<longrightarrow> ticks H\<^sub>2 (hamlet r n)
                               }\<close>

text\<open> Tag Relations define the structure of the temporal mesh (fabric, texture) \<close>

definition TagRelation :: \<open>('\<AA>,'a)\<H> 
                        \<Rightarrow> ('a \<times> 'b) set
                        \<Rightarrow> ('\<AA>,'b)\<H>
                        \<Rightarrow> ('\<AA>::orderedrank) runs \<close>
where \<open>TagRelation  H\<^sub>1 R H\<^sub>2 = {r. \<forall>n. (timeof H\<^sub>1 in r at n, timeof H\<^sub>2 in r at n) \<in> R}\<close>

text \<open>
  Loose tag relations hold only when events occur.
\<close>
definition LooseTagRelation :: \<open>('\<AA>,'a)\<H> 
                             \<Rightarrow> ('a \<times> 'b) set
                             \<Rightarrow> ('\<AA>,'b)\<H>
                             \<Rightarrow> ('\<AA>::orderedrank) runs \<close>
where \<open>LooseTagRelation H\<^sub>1 R H\<^sub>2 = {r. (\<forall>n. tick_occurs (hamlet r n)
                                      \<longrightarrow> (timeof H\<^sub>1 in r at n, timeof H\<^sub>2 in r at n) \<in> R)
                                  }\<close>
text \<open>
  A tag relation is a stricter specification than the equivalent loose tag relation.
\<close>
lemma tagrel_is_loose:
  shows   \<open>TagRelation H\<^sub>1 R H\<^sub>2 \<subseteq> LooseTagRelation H\<^sub>1 R H\<^sub>2\<close>
unfolding TagRelation_def LooseTagRelation_def by blast

text \<open>
  Affine tag relations are a special case of tag relations defined by an affine function.
  The case of integers is complicated by the fact that multiplication and division 
  are not reciprocal.
\<close>
fun AffineTagRelation\<^sub>i\<^sub>n\<^sub>t :: \<open>('\<AA>,int)\<H> 
                         \<Rightarrow> (int \<times> int)
                         \<Rightarrow> ('\<AA>,int)\<H>
                         \<Rightarrow> ('\<AA>::orderedrank) runs\<close> ("tag relation _ = _  _" [70,70,70] 55)
where \<open>AffineTagRelation\<^sub>i\<^sub>n\<^sub>t  H\<^sub>1 (a,b) H\<^sub>2
        = TagRelation H\<^sub>1 {(m::int,n::int). (m = a * n + b) \<or> (n = (m-b) div a)} H\<^sub>2\<close>  


text\<open> The following definition works because in fields, the inverses exist
       and the more complicated case for integers is therefore not necessary, \<close>  
definition AffineTagRelation\<^sub>r\<^sub>i\<^sub>n\<^sub>g :: \<open>('\<AA>,'b)\<H> 
                                 \<Rightarrow> ('b::field)
                                 \<Rightarrow> ('\<AA>,'b)\<H>
                                 \<Rightarrow> 'b \<Rightarrow> ('\<AA>::orderedrank) runs \<close>
                                  ("tag relation _ = _ * _ + _" [70,70,70,70] 55)
where \<open>AffineTagRelation\<^sub>r\<^sub>i\<^sub>n\<^sub>g H\<^sub>1 a H\<^sub>2 b = TagRelation H\<^sub>1 {(y,x). y = a * x + b} H\<^sub>2\<close>

text \<open>
  The time delayed implication forces a tick to occur on a clock a fixed delay (measured in
  time on another reference clock) after each tick of the master clock.
\<close>
definition TimeDelayed :: \<open>('\<AA>,'b::{semiring,order})\<H>  
                        \<Rightarrow> 'c::{semiring,order}
                        \<Rightarrow> ('\<AA>,'c)\<H>
                        \<Rightarrow> ('\<AA>,'d)\<H>
                        \<Rightarrow> ('\<AA>::orderedrank) runs\<close>
                        ("'( _ time-delayed by _ on _ implies _')" 56)
where \<open>(master time-delayed by dt on ref implies slave) \<equiv> 
        {r. \<forall>n. ticks master (hamlet r n) \<longrightarrow>
                  (\<exists>m > n. ticks slave (hamlet r m)
                        \<and> ((timeof ref in r at m) = (timeof ref in r at n) + dt))
        }\<close>


text \<open>
  The delayed implication forces a tick to occur on a clock after a fixed number of
  ticks has occurred on another clock each time a tick occurs on the master clock.
\<close>
definition Delayed :: \<open>('\<AA>,'b)\<H>  
                     \<Rightarrow> nat
                     \<Rightarrow> ('\<AA>,'c)\<H>
                     \<Rightarrow> ('\<AA>,'d)\<H>
                     \<Rightarrow> ('\<AA>::orderedrank) runs\<close>
                     ("'( _ delayed by _ on _ implies _')" 56)
where \<open>(m delayed by d on counter implies slave) \<equiv> 
         {r. \<forall>n. ticks m (hamlet r n)
                  \<longrightarrow> (\<exists>n\<^sub>f\<^sub>i\<^sub>r\<^sub>e > n. ticks slave (hamlet r n\<^sub>f\<^sub>i\<^sub>r\<^sub>e)
                    \<and> tick_count_between counter (hamlet r) n n\<^sub>f\<^sub>i\<^sub>r\<^sub>e = d)
          }\<close>

text \<open>
  The filtered implication is similar to the regular implication, but is active only
  through a pattern fixed by a regular expression.
  This pattern is defined as s, k (rs, rk)*, which means that s ticks of the master clock
  are skipped, then k ticks are kept, and then, repeatedly, rs ticks are skipped and rk
  ticks are kept. The implication is active only for the kept ticks.
\<close>
definition Filtered :: \<open>('\<AA>,'b)\<H>  
                      \<Rightarrow> nat
                      \<Rightarrow> nat
                      \<Rightarrow> nat
                      \<Rightarrow> nat
                      \<Rightarrow> ('\<AA>,'c)\<H>
                      \<Rightarrow> ('\<AA>::orderedrank) runs\<close>
                      ("'( _ filtered by _, _ '(_, _')* implies _')" 56)
where \<open>(m filtered by s, k (rs, rk)* implies slave) \<equiv> 
           {r. \<forall>n. ticks m (hamlet r n) \<and> filter s k rs rk (tick_count m (hamlet r) n)
                    \<longrightarrow> ticks slave (hamlet r n)
            }\<close>


text \<open>
  The \<^emph>\<open>await\<close> implication.
  await a, b implies c makes c tick each time a and b have both ticked.
\<close>
definition Await :: \<open>('\<AA>,'a)\<H>
                  \<Rightarrow> ('\<AA>,'b)\<H>
                  \<Rightarrow> ('\<AA>,'c)\<H>
                  \<Rightarrow> ('\<AA>::orderedrank) runs\<close>
                  ("await _ , _ implies _" 56)
where \<open>await a, b implies slave \<equiv> 
        {r. \<forall>n. have_both_ticked a b (hamlet r) n \<longrightarrow> ticks slave (hamlet r n)}\<close>

text \<open>
  This implication is activated when a \<^emph>\<open>begin\<close> clock ticks, and deactivated
  when an \<^emph>\<open>end\<close> clock ticks. It is therefore only active between an occurrence
  of the begin clock and an occurrence of the end clock.
\<close>
definition SustainFromTo ::\<open>('\<AA>,'a)\<H>
                         \<Rightarrow> ('\<AA>,'b)\<H>
                         \<Rightarrow> ('\<AA>,'c)\<H>
                         \<Rightarrow> ('\<AA>,'d)\<H>
                         \<Rightarrow> ('\<AA>::orderedrank) runs\<close>
                        ("_ sustained from _ to _ implies _" 55)
where
  \<open>m sustained from beg to end implies slave \<equiv> {
    r. \<forall>n. between beg end (hamlet r) n \<and> ticks m (hamlet r n)
            \<longrightarrow> ticks slave (hamlet r n)
   }\<close>


end

