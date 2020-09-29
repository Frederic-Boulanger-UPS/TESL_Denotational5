theory TeslDenotationalArchiWrong

imports TeslDenotationalArchi

begin

(*
  FIXME:  no link between timep and index in clocks
          so no way to prove that (index c) < rank r\<^sub>1 implies
          that the time of c is in the first component of the time structure.
*)
lemma clock_proj\<^sub>1:
  assumes "ticks c (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)"
  and     "(index c) < rank r\<^sub>1"
  shows   "\<exists>c\<^sub>0. c = shift\<^sub>1 c\<^sub>0 r\<^sub>1"
proof -
  from assms have "\<exists>f. c = (f \<circ> fst, index c)" sorry
  from this obtain f where "c = (f \<circ> fst, index c)" by blast
  hence "c = shift\<^sub>1 (f, index c) r\<^sub>1" unfolding shift\<^sub>1_def by auto
  thus ?thesis by blast
qed

lemma clock_proj\<^sub>2:
  assumes "ticks c (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)"
  and     "(index c) \<ge> rank r\<^sub>1"
  shows   "\<exists>c\<^sub>0. c = shift\<^sub>2 c\<^sub>0 r\<^sub>1"
proof -
  from assms(2) have "\<exists>i\<^sub>0. (index c) = i\<^sub>0 + rank r\<^sub>1" by presburger
  from this obtain i\<^sub>0 where i0prop:"(index c) = i\<^sub>0 + rank r\<^sub>1" by blast
  from assms have "\<exists>f. c = (f \<circ> snd, index c)" sorry
  from this obtain f where "c = (f \<circ> snd, index c)" by blast
  with i0prop have "c = shift\<^sub>2 (f, i\<^sub>0) r\<^sub>1" unfolding shift\<^sub>2_def by auto
  thus ?thesis by blast
qed

lemma 
  assumes "ticks (c::('a::orderedrank \<times> 'b::orderedrank, 'c)\<H>) (hamlet ((r\<^sub>1::'a run) \<times>\<^sub>r\<^sub>u\<^sub>n (r\<^sub>2::'b run)) n)"
  and     "index c < rank r\<^sub>1"
  shows   "\<exists>sc. c = shift\<^sub>1 sc r\<^sub>1 \<and> ticks sc (hamlet r\<^sub>1 n)"
proof -
  from assms have "(hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index c)" unfolding ticks_def by metis
  hence "((hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))!(index c)" by (simp add: hamlet_prod_hamlet)
  with assms(2) have *:"(hamlet r\<^sub>1 n)!(index c)" by (simp add: nth_append rank_any_hamlet)
  from clock_proj\<^sub>1[OF assms] obtain sc where scprop:"c = shift\<^sub>1 sc r\<^sub>1" by blast
  with * have "(hamlet r\<^sub>1 n)!(index sc)" unfolding shift\<^sub>1_def by simp
  moreover from assms(2) have "index sc < rank r\<^sub>1" by (simp add: scprop shift\<^sub>1_def)
  ultimately have "ticks sc (hamlet r\<^sub>1 n)" unfolding ticks_def by (simp add: rank_any_hamlet)
  with scprop show ?thesis by blast
qed

lemma 
  assumes "ticks (c::('a::orderedrank \<times> 'b::orderedrank, 'c)\<H>) (hamlet ((r\<^sub>1::'a run) \<times>\<^sub>r\<^sub>u\<^sub>n (r\<^sub>2::'b run)) n)"
  and     "index c \<ge> rank r\<^sub>1"
  shows   "\<exists>sc. c = shift\<^sub>2 sc r\<^sub>1 \<and> ticks sc (hamlet r\<^sub>2 n)"
proof -
  from assms have "index c < length (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n) \<and> (hamlet (r\<^sub>1 \<times>\<^sub>r\<^sub>u\<^sub>n r\<^sub>2) n)!(index c)"
    unfolding ticks_def by metis
  hence "index c < rank r\<^sub>1 + rank r\<^sub>2 \<and> ((hamlet r\<^sub>1 n)@(hamlet r\<^sub>2 n))!(index c)"
    by (simp add: hamlet_prod_hamlet rank_any_hamlet)
  with assms(2) have *:"(index c - rank r\<^sub>1) < rank r\<^sub>2 \<and> (hamlet r\<^sub>2 n)!(index c - rank r\<^sub>1)"
    by (auto simp add: nth_append rank_any_hamlet)
  from clock_proj\<^sub>2[OF assms] obtain sc where scprop:"c = shift\<^sub>2 sc r\<^sub>1" by blast
  with * have "index sc < rank r\<^sub>2 \<and> (hamlet r\<^sub>2 n)!(index sc)" unfolding shift\<^sub>2_def by simp
  hence "ticks sc (hamlet r\<^sub>2 n)" unfolding ticks_def by (simp add: rank_any_hamlet)
  with scprop show ?thesis by blast
qed

end
