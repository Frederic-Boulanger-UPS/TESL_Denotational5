theory TeslOperational

imports TeslRelations
        TeslOperationalPrimitives

begin

term \<open>(timep (h::('\<U>, 'a)\<H>)) (time (Rep_run_context (c::('\<U>::orderedrank run_context))) n)\<close>

text \<open>
  Build a run context with identical values excepted for the time on h at instant n
  which become t.
\<close>
definition \<open>set_time c h n t \<equiv> THE ctxt. (
    \<comment> \<open>The time on h at instant n is t\<close>
    (timep h) (time (Rep_run_context ctxt) n) = t
    \<comment> \<open>The time and time constraint at instant n on any clock other than h are the same as in the original context\<close>
    \<comment> \<open>There may be a problem here: \<^theory_text>\<open>\<forall>k \<noteq> h\<close> makes k of the same type as h, so the quantification is not really universal\<close>
  \<and> (\<forall>k \<noteq> h. (timep k) (time (Rep_run_context ctxt) n) = (timep k) (time (Rep_run_context c) n))
  \<and> (\<forall>k \<noteq> h. (ticks k (timec (Rep_run_context ctxt) n)) = (ticks k (timec (Rep_run_context c) n)))
    \<comment> \<open>The time and time constraint on any clock at any instant other than n is the same as in the original context\<close>
  \<and> (\<forall>i \<noteq> n. \<forall>k < rank ctxt. (timep ((clock_suc^^k) clock0)) (time (Rep_run_context ctxt) i)
                            = (timep ((clock_suc^^k) clock0)) (time (Rep_run_context c) i))
  \<and> (\<forall>i \<noteq> n. \<forall>k < rank ctxt. (timec (Rep_run_context ctxt) i)!(index ((clock_suc^^k) clock0)) 
                            = (timec (Rep_run_context c) i)!(index ((clock_suc^^k) clock0)) )
    \<comment> \<open>The hamlet and antihamlet are unchanged\<close>
  \<and> (ham (Rep_run_context ctxt) = ham (Rep_run_context c))
  \<and> (antiham (Rep_run_context ctxt) = antiham (Rep_run_context c) )
)\<close>

inductive handle_relation 
where
  empty_e:      \<open>handle_relation c Empty n c Empty\<close>
| sporadic_e1:  \<open>handle_relation c (Sporadic h t) n c (Sporadic h t)\<close>
| sporadic_e2:  \<open>handle_relation c (Sporadic h t) n (set_time c h n t) Empty\<close>

end

\<^cancel>\<open>
    (\<lambda>i. if i = n then
      (\<lambda>k. if k = h then t else (timep k) (time (Rep_run_context c) i) )
    else
      (\<lambda>k. (timep k) (time (Rep_run_context c) i))
    ) (timec (Rep_run_context c)) (ham (Rep_run_context c)) (antiham (Rep_run_context c))
\<close>