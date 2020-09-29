theory TeslOperationalPrimitives

imports "../TeslDenotationalCore"
        "../TeslDenotationalOperators"

begin

text \<open>
  A run context contains constraints on a run.
  \<^item> \<^theory_text>\<open>time\<close> is a time structure that contains the mandatory time values
  \<^item> \<^theory_text>\<open>timec\<close> is a hamlet that indicates whether each time value in \<^theory_text>\<open>time\<close> is mandatory or not
  \<^item> \<^theory_text>\<open>ham\<close> is a hamlet that tells when the clocks have to tick
  \<^item> \<^theory_text>\<open>antiham\<close> is a hamlet that tells when the clocks have to \<^emph>\<open>not\<close> tick

  Additionally, a run context has the same rank for all its components.
\<close>
datatype 'a run_context_base = 
  Context (time:\<open>'a time_structure\<close>) (timec:\<open>hamlet\<close>) (ham:\<open>hamlet\<close>) (antiham:\<open>hamlet\<close>)

typedef (overloaded) 'a run_context = \<open>
  {rc::('a::orderedrank run_context_base).
      rank ((time rc) 0) = length ((timec rc) 0)
    \<and> rank ((time rc) 0) = length ((ham rc) 0)
    \<and> rank ((time rc) 0) = length ((antiham rc) 0)
  }
\<close>
by (metis (mono_tags, lifting) mem_Collect_eq rank_any_hamlet rank_run_def run_context_base.sel(1-4))

text \<open>
  The rank of a run context is the number of clocks it specifies.
\<close>
instantiation run_context :: (orderedrank) rank
begin
  definition \<open>rank_run_context rc \<equiv> rank ((time (Rep_run_context rc)) 0)\<close>
  instance proof
    show \<open>\<And>x::('a::orderedrank run_context). 0 < rank x\<close> by (simp add: pos rank_run_context_def)
    show \<open>\<And>(x::('a::orderedrank run_context)) (y::('a::orderedrank run_context)). rank x = rank y\<close>
      by (simp add: const rank_run_context_def)
  qed
end

text \<open>
  A time constraint is satisfied when either the component in the \<^theory_text>\<open>timec\<close> hamlet is false
  or the time on the clock is the specified time value.
\<close>
definition \<open>time_constraint ctxt r h n \<equiv>
    \<not>(ticks h (timec (Rep_run_context ctxt) n))
  \<or> ((timeof h in r at n) = (timep h) (time (Rep_run_context ctxt) n))
\<close>

text \<open>
  A tick constraint is satisfied either when the clock has to tick and it ticks
  or when it has to not tick and it does not tick.
\<close>
definition tick_constraint::\<open>'a::orderedrank run_context \<Rightarrow> 'a run \<Rightarrow> ('a \<Rightarrow> 'b) \<times> nat \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>tick_constraint ctxt r h n  \<equiv>
    (((ticks h (ham (Rep_run_context ctxt) n)) \<and> \<not>(ticks h (antiham (Rep_run_context ctxt) n))) \<longrightarrow> (ticks h (hamlet r n)))
  \<and> ((\<not>(ticks h (ham (Rep_run_context ctxt) n)) \<and> (ticks h (antiham (Rep_run_context ctxt) n))) \<longrightarrow> \<not>(ticks h (hamlet r n)))
\<close>

text \<open>
  The interpretation of a run context is the set of runs that verify its constraints.
\<close>
definition \<open>context_interp ctxt \<equiv>
  {r. \<forall>n. \<forall>k < rank r. time_constraint ctxt r ((clock_suc^^k) clock0) n
                    \<and> tick_constraint ctxt r ((clock_suc^^k) clock0) n}
\<close>

notation context_interp ("\<lbrakk> _ \<rbrakk>\<^sub>c\<^sub>t\<^sub>x\<^sub>t")

end
