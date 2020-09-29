theory TeslDenotationalTickNum

imports "../TeslDenotationalOperators"

begin

text {*
  Number of ticks of clock c in a window [s, s+w]
*}
definition tick_num
where
  "tick_num c h s w \<equiv> card {i. s \<le> i \<and> i \<le> s+w \<and> ticks c (h i)}"

fun tick_num_fun :: "('a, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat \<Rightarrow> nat"
where
  "tick_num_fun c h s 0 = (if ticks c (h s) then 1 else 0)"
| "tick_num_fun c h s (Suc w) = (if ticks c (h (s + (Suc w)))
                                 then Suc (tick_num_fun c h s w)
                                 else tick_num_fun c h s w)"

text {*
  Some lemmas about cardinals
*}
lemma card_sing:"card {i. i = k \<and> P i} = (if P k then 1 else 0)"
proof (cases "P k")
  case True
    hence "{i. i = k \<and> P i} = {k}" by auto
    hence "card {i. i = k \<and> P i} = 1" by simp
    thus ?thesis using True by simp
next
  case False
    hence "{i. i = k \<and> P i} = {}" by auto
    hence "card {i. i = k \<and> P i} = 0" by simp
    thus ?thesis using False by simp
qed

lemma card_suc:"card {i. l \<le> i \<and> i \<le> l + (Suc h) \<and> P i} =
                  (if P (l + Suc h) then Suc (card {i. l \<le> i \<and> i \<le> l + h \<and> P i})
                                else card {i. l \<le> i \<and> i \<le> l + h \<and> P i})"
proof (cases "P (l + Suc h)")
  case True
    hence "{i. l \<le> i \<and> i \<le> l + (Suc h) \<and> P i} = {i. l \<le> i \<and> i \<le> l + h \<and> P i} \<union> {l + Suc h}" by auto
    hence "card {i. l \<le> i \<and> i \<le> l + (Suc h) \<and> P i} = Suc (card {i. l \<le> i \<and> i \<le> l + h \<and> P i})" by simp
    thus ?thesis using True by simp
next
  case False
    hence "{i. l \<le> i \<and> i \<le> l + (Suc h) \<and> P i} = {i. l \<le> i \<and> i \<le> l + h \<and> P i}" using le_Suc_eq by auto
    hence "card {i. l \<le> i \<and> i \<le> l + (Suc h) \<and> P i} = card {i. l \<le> i \<and> i \<le> l + h \<and> P i}" by simp
    thus ?thesis using False by simp
qed

text {*
  Equivalence of the denotational and the function definitions of tick_num.
*}
lemma tick_num_is_fun:"tick_num c h s w = tick_num_fun c h s w"
proof (induction w)
  case 0
    have "tick_num c h s 0 = card {i. s \<le> i \<and> i \<le> s+0 \<and> ticks c (h i)}" using tick_num_def by blast
    also have "... = card {i. s = i \<and> ticks c (h i)}" by (simp add: eq_iff)
    also have "... = card {i. i = s \<and> ticks c (h i)}" using eq_sym_conv[of _ "s"] by simp 
    also have "... = (if ticks c (h s) then 1 else 0)" using card_sing[of "s" "\<lambda>i. ticks c (h i)"] .
    finally show ?case by simp
next
  case (Suc v)
    have "tick_num c h s (Suc v) = card {i. s \<le> i \<and> i \<le> s + (Suc v) \<and> ticks c (h i)}" using tick_num_def by blast
    also have "... = (if ticks c (h (s + Suc v))
                      then Suc (card {i. s \<le> i \<and> i \<le> s + v \<and> ticks c (h i)})
                      else card {i. s \<le> i \<and> i \<le> s + v \<and> ticks c (h i)})"  using card_suc by simp
    also have "... = (if ticks c (h (s + Suc v))
                      then Suc (tick_num c h s v)
                      else tick_num c h s v)" using tick_num_def[of "c" "h" "s" "v",symmetric] by simp
    finally show ?case using Suc.IH by simp
qed

text {*
  hasticked clk hmt from width n = clock clk, in a system with hamlet hmt, has ticked n times
                               in the interval [from, from+width]
*}
inductive hasticked :: "('a, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  (* Base case for a singleton interval *)
  "\<not> ticks clk (hmt from) \<Longrightarrow> hasticked clk hmt from 0 0"
| "  ticks clk (hmt from) \<Longrightarrow> hasticked clk hmt from 0 1"
  (* Induction for larger intervals *)
| "hasticked clk hmt from w d \<and> \<not> ticks clk (hmt (from + (Suc w))) \<Longrightarrow> hasticked clk hmt from (Suc w) d"
| "hasticked clk hmt from w d \<and> ticks clk (hmt (from + (Suc w))) \<Longrightarrow> hasticked clk hmt from (Suc w) (Suc d)"

inductive_cases Ticked00[elim!]: "hasticked clk hmt from 0 0"
thm Ticked00
inductive_cases Ticked01[elim!]: "hasticked clk hmt from 0 1"
thm Ticked01
inductive_cases Tickedw0[elim!]: "hasticked clk hmt from (Suc w) d"
inductive_cases Tickedwd[elim!]: "hasticked clk hmt from (Suc w) (Suc d)"
inductive_cases Ticked0d[elim!]:"hasticked clk hmt from 0 d"
thm Ticked0d
inductive_cases Ticked0sd[elim!]:"hasticked clk hmt from 0 (Suc d)"
thm Ticked0sd

lemmas hasticked.intros[intro]

text {*
  Functional version of the inductive predicate
*}
fun hasticked_fun :: "('a, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "hasticked_fun clk hmt from 0 0 = (\<not>ticks clk (hmt from))"
| "hasticked_fun clk hmt from 0 (Suc 0) = ticks clk (hmt from)"
| "hasticked_fun clk hmt from (Suc w) 0 =
    (hasticked_fun clk hmt from w 0 \<and> \<not>ticks clk (hmt (from + (Suc w))))"
| "hasticked_fun clk hmt from (Suc w) (Suc d) = (
    (hasticked_fun clk hmt from w (Suc d) \<and> \<not>ticks clk (hmt (from + (Suc w))))
  \<or> (hasticked_fun clk hmt from w d \<and> ticks clk (hmt (from + (Suc w))))
   )"
| "hasticked_fun clk hmt from _ _ = False"

text {*
  Proof of equivalence of the two definitions.
*}
lemma hasticked_is_fun[code]: "hasticked clk hmt from w d = hasticked_fun clk hmt from w d"
proof (induction d arbitrary: w)
  case 0 thus ?case by (induction w, auto)
next
  case (Suc d') thus ?case
    proof (induction w)
      case 0 thus ?case
        proof (cases "d' = 0")
          case True thus ?thesis by (metis One_nat_def Ticked01 hasticked_fun.simps(2) hasticked.intros(2))
        next
          case False
            hence "\<not>hasticked clk hmt from 0 (Suc d')" using Ticked0sd by blast
            moreover have "\<not>hasticked_fun clk hmt from 0 (Suc d')" by (metis False hasticked_fun.simps(5) lessI less_Suc_eq_0_disj) 
            ultimately show ?thesis by simp
        qed
    next
      case (Suc w') thus ?case by auto
    qed
qed

text {*
  hasjustticked clk hmt from width n = clock c, in a system with hamlet h, has ticked for the nth time
                                       at the end of the interval [from, from+width]
*}
inductive hasjustticked :: "('a, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "ticks clk (hmt from) \<Longrightarrow> hasjustticked clk hmt from 0 1"
| "hasticked clk hmt from w d \<and> ticks clk (hmt (from + (Suc w)))
    \<Longrightarrow> hasjustticked clk hmt from (Suc w) (Suc d)"

fun hasjustticked_fun :: "('a, 'b)\<H> \<Rightarrow> hamlet \<Rightarrow> instant \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "hasjustticked_fun clk hmt from 0 (Suc 0) = ticks clk (hmt from)"
| "hasjustticked_fun clk hmt from (Suc w) (Suc d)
    = (hasticked_fun clk hmt from w d \<and> ticks clk (hmt (from + (Suc w))))"
| "hasjustticked_fun clk hmt from w 0 = False"
| "hasjustticked_fun clk hmt from 0 (Suc (Suc d)) = False"


end
