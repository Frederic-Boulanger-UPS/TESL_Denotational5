theory NatStrongInduct

imports Main

begin

\<comment> \<open>
  Transformation of our induction hypothesis into the form expected by less_induct.
\<close>
lemma suc_induct:
  assumes \<open>\<And>n. \<forall>m \<le> n. P m \<Longrightarrow> P (Suc n)\<close>
  and     \<open>P 0\<close>
  and     \<open>\<forall>m < n. P m\<close>
  shows   \<open>P n\<close>
proof (cases n)
  case 0
    thus ?thesis using assms(2) by simp
next
  case (Suc k)
    thus ?thesis using assms le_imp_less_Suc by blast
qed

\<comment> \<open>
 Another induction rule for Noetherian induction that is easier to use in some proofs
\<close>
lemma nat_strong_induct [case_names 0 Suc]:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  assumes \<open>P 0\<close>
      and \<open>\<And>n. \<forall>m \<le> n. P m \<Longrightarrow> P (Suc n)\<close>
    shows \<open>P n\<close>
using suc_induct[of \<open>P\<close>] assms less_induct[of \<open>P\<close> \<open>n\<close>] by blast

end
