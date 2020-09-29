theory TeslRelations

imports "../TeslDenotationalCore"

begin

datatype ('\<U>, 'a, 'b, 'c, 'd) tesl_relation =
    Empty
  | Sporadic \<open>('\<U>, 'a)\<H>\<close> \<open>'a\<close>
  | Implies \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'b)\<H>\<close>
  | ImpliesEvery \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'b)\<H>\<close> nat
  | TimeRelation \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'b)\<H>\<close> \<open>('a \<times> 'b) set\<close>
  | LooseTimeRelation \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'b)\<H>\<close> \<open>('a \<times> 'b) set\<close>
  | AffineTagRelation\<^sub>i\<^sub>n\<^sub>t \<open>('\<U>, int)\<H>\<close> \<open>('\<U>, int)\<H>\<close> \<open>(int \<times> int)\<close>
  | AffineTagRelation\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'a)\<H>\<close> \<open>'a\<close> \<open>'a\<close>
  | TimeDelayed \<open>('\<U>, 'a)\<H>\<close> \<open>'b\<close> \<open>('\<U>, 'b)\<H>\<close> \<open>('\<U>, 'c)\<H>\<close>
  | Delayed \<open>('\<U>, 'a)\<H>\<close> \<open>nat\<close> \<open>('\<U>, 'b)\<H>\<close> \<open>('\<U>, 'c)\<H>\<close>
  | Filtered \<open>('\<U>, 'a)\<H>\<close> nat nat nat nat \<open>('\<U>, 'b)\<H>\<close>
  | Await \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'b)\<H>\<close> \<open>('\<U>, 'c)\<H>\<close>
  | SustainFromTo \<open>('\<U>, 'a)\<H>\<close> \<open>('\<U>, 'b)\<H>\<close> \<open>('\<U>, 'c)\<H>\<close> \<open>('\<U>, 'd)\<H>\<close>

end
