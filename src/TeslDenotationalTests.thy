theory TeslDenotationalTests

imports TeslDenotationalOperators

begin
text \<open> A base case \<close>
lemma test1 : \<open>rank(x::nat,y::real,z::int) = 3\<close>
unfolding rank_prod_def rank_real_def rank_int_def rank_nat_def
by simp


text \<open> A generic case \<close>
lemma test2 : \<open>rank(x::nat,y::('a::rank),z::int) = 2 + rank y\<close>
unfolding rank_prod_def rank_real_def rank_int_def rank_nat_def
by simp

abbreviation \<open>ticks1 \<equiv> [True, False, False, True, True, False, True]\<close>
abbreviation \<open>ham1 \<equiv> (\<lambda>n::nat. (if n < (length ticks1) then [ticks1 ! n] else [False]))\<close>
abbreviation \<open>c\<^sub>0::((nat\<times>nat), nat)\<H> \<equiv> (fst, 0)\<close>

value \<open>ham1 3\<close>
lemma \<open>tick_count c\<^sub>0 ham1 5 = 3\<close> by eval

value \<open>ticks c\<^sub>0 (ham1 0)\<close>
value \<open>ticks c\<^sub>0 (ham1 3)\<close>
value \<open>tick_count c\<^sub>0 ham1 0\<close>
value \<open>tick_count c\<^sub>0 ham1 1\<close>
value \<open>tick_count c\<^sub>0 ham1 2\<close>
value \<open>tick_count c\<^sub>0 ham1 3\<close>
value \<open>tick_count c\<^sub>0 ham1 4\<close>
value \<open>tick_count c\<^sub>0 ham1 5\<close>
value \<open>tick_count c\<^sub>0 ham1 6\<close>
value \<open>tick_count c\<^sub>0 ham1 7\<close>

declare [[show_sorts]]
lemma \<open>tick_count_between c\<^sub>0 ham1 0 2 = 0\<close>
proof -
  have h:\<open>(0::nat) \<le> 2\<close> by simp
  have \<open>tick_count c\<^sub>0 ham1 2 = 1\<close> by eval
  moreover have \<open>tick_count c\<^sub>0 ham1 0 = 1\<close> by eval
  moreover have \<open>tick_count_between c\<^sub>0 ham1 0 2
               = tick_count c\<^sub>0 ham1 2 - (tick_count c\<^sub>0 ham1 0)\<close>
    using count_diff[OF h] by simp
  ultimately show ?thesis using count_diff[OF h, of \<open>(timep,0)\<close> \<open>ham1\<close>] by auto
qed

lemma \<open>first_tick c\<^sub>0 ham1 = Some 0\<close>
proof -
  have \<open>ticks c\<^sub>0 (ham1 0)\<close> by (simp add:ticks_def)
  thus ?thesis unfolding first_tick_def  by (metis (no_types, lifting) Least_eq_0)
qed

value \<open>filter 1 2 1 1 (0::int)\<close>
value \<open>filter 1 2 1 1 (1::int)\<close>
value \<open>filter 1 2 1 1 (2::int)\<close>
value \<open>filter 1 2 1 1 (3::int)\<close>
value \<open>filter 1 2 1 1 (4::int)\<close>
value \<open>filter 1 2 1 1 (5::int)\<close>
value \<open>filter 1 2 1 1 (6::int)\<close>
value \<open>filter 1 2 1 1 (7::int)\<close>

value \<open>filter 0 0 1 2 (0::int)\<close>
value \<open>filter 0 0 1 2 (1::int)\<close>
value \<open>filter 0 0 1 2 (2::int)\<close>
value \<open>filter 0 0 1 2 (3::int)\<close>
value \<open>filter 0 0 1 2 (4::int)\<close>
value \<open>filter 0 0 1 2 (5::int)\<close>
value \<open>filter 0 0 1 2 (6::int)\<close>
value \<open>filter 0 0 1 2 (7::int)\<close>

value \<open>filter 1 2 0 1 (0::int)\<close>
value \<open>filter 1 2 0 1 (1::int)\<close>
value \<open>filter 1 2 0 1 (2::int)\<close>
value \<open>filter 1 2 0 1 (3::int)\<close>
value \<open>filter 1 2 0 1 (4::int)\<close>
value \<open>filter 1 2 0 1 (5::int)\<close>

value \<open>filter 1 2 0 0 (0::int)\<close>
value \<open>filter 1 2 0 0 (1::int)\<close>
value \<open>filter 1 2 0 0 (2::int)\<close>
value \<open>filter 1 2 0 0 (3::int)\<close>
value \<open>filter 1 2 0 0 (4::int)\<close>
value \<open>filter 1 2 0 0 (5::int)\<close>

end

