theory mealy
  imports Main
begin

sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

text \<open>transitions mealy\<close>
type_synonym ('state,'input,'output) transition = "(('state \<times> 'input) \<Rightarrow> ('state \<times> 'output))"

type_synonym ('state,'input,'output) mealy = "'state \<times> 'state set \<times> ('state,'input,'output) transition"


fun trans_star :: "('state,'input,'output) transition \<Rightarrow> 'state \<Rightarrow> 'input list \<Rightarrow> ('state \<times> 'output list)" where
  "trans_star f q [] = (q, [])" |
  "trans_star f q (w # ws) = (let (st,op) = f (q,w) in (let (q',x) = trans_star f st ws in (q',op # x)))"


fun trans_star_output :: "('state,'input,'output) transition \<Rightarrow> 'state \<Rightarrow> 'input list \<Rightarrow> ('output list)" where
  "trans_star_output f q [] = []" |
  "trans_star_output f q (i # is) = (let (st,op) = f (q,i) in (let x = trans_star_output f st is in (op # x)))"


fun trans_star_state :: "('state,'input,'output) transition \<Rightarrow> 'state \<Rightarrow> 'input list \<Rightarrow> ('state)" where
  "trans_star_state f q [] = q" |
  "trans_star_state f q (i # is) = (let (st,op) = f (q,i) in (let x = trans_star_state f st is in x))"


lemma trans_star_output_state: "trans_star f q i = (trans_star_state f q i,trans_star_output f q i)"
  apply (induction i arbitrary: f q)
  apply auto
  by (smt (verit) case_prod_conv prod.case_distrib split_cong)

definition mealy_eq :: "('state,'input,'output) mealy \<Rightarrow> 'state \<Rightarrow> ('state2,'input,'output) mealy \<Rightarrow> 'state2 \<Rightarrow> bool" where
  "mealy_eq a q b p \<equiv> (case (a,b) of
    ((q_0,S,f),(p_0,S_2,g)) \<Rightarrow> (\<forall> is. trans_star_output f q is = trans_star_output g p is))"

abbreviation equal :: "('state,'input,'output) mealy \<Rightarrow> ('state2,'input,'output) mealy \<Rightarrow> bool" (infixr"\<approx>" 80) where
  "a \<approx> b \<equiv> (case (a,b) of
    ((q_0,S,f),(p_0,S_2,g)) \<Rightarrow> mealy_eq a q_0 b p_0)"

definition mealy_invar :: "('state,'input,'output) mealy \<Rightarrow> bool" where
  "mealy_invar m = (case m of
    (q_0,S,t) \<Rightarrow> q_0 \<in> S \<and> (\<forall> q q' i out. q \<in> S \<and> (t (q,i) = (q',out)) \<longrightarrow> q' \<in> S))"

definition func_sim :: "('state \<Rightarrow> 'state2) \<Rightarrow> ('state,'input,'output) mealy \<Rightarrow> 
  ('state2,'input,'output) mealy \<Rightarrow> bool" where
  "func_sim f a b \<equiv> (case (a,b) of
    ((q_0,S,t),(p_0,S_2,g)) \<Rightarrow> (f q_0 = p_0) \<and> (\<forall> q q' i op. q \<in> S \<and> q' \<in> S \<and> t (q,i) = (q',op) \<longrightarrow>
       g (f q,i) = (f q',op)))"


lemma split_trans_star_output: "t (q,i) = (q',ot) \<Longrightarrow> trans_star_output t q' is = op \<Longrightarrow> 
    trans_star_output t q (i # is) = (ot # op)"
  by (auto split: prod.splits option.splits)

lemma split_trans_star_output_rev: "trans_star_output t q (i # is) = (ot # op) \<Longrightarrow> 
    \<exists> q'. t (q,i) = (q',ot) \<and> trans_star_output t q' is = op"
  by (auto split: prod.splits option.splits)


lemma split_trans_star: "t (q,i) = (q',ot) \<Longrightarrow> trans_star t q' is = (st,op) \<Longrightarrow> 
    trans_star t q (i # is) = (st,ot # op)"
  by (auto split: prod.splits option.splits)

lemma split_trans_star_rev: "trans_star t q (i # is) = (st,ot # op) \<Longrightarrow> 
    \<exists> q'. t (q,i) = (q',ot) \<and> trans_star t q' is = (st,op)"
  by (auto split: prod.splits option.splits)


lemma
  assumes "trans_star_state t q_0 acc = st" and
    "trans_star_state t st is = (st2)"
  shows "(trans_star_state t q_0 (acc @ is)) = (st2)"
using assms proof (induction t q_0 acc rule: trans_star.induct)
  case (1 f q)
  then show ?case
    by fastforce
next
  case (2 f q w ws)
  then show ?case
    by (metis (no_types,lifting) append_Cons case_prod_conv old.prod.exhaust trans_star_state.simps(2))
qed


lemma trans_star_length: "trans_star t q_0 iss = (q,os) \<Longrightarrow> length iss = length os"
proof (induction iss arbitrary: os q q_0)
  case Nil
  then show ?case
    by auto
next
  case (Cons a iss)
  then show ?case
    by (auto split: prod.splits option.splits)
qed

lemma trans_star_two:
  assumes "trans_star t q_0 acc = (st,op1)" and
    "trans_star t st is = (st2,op2)"
  shows "(trans_star t q_0 (acc @ is)) = (st2,op1 @ op2)"
using assms proof (induction acc arbitrary: q_0 op1 op2 st st2)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons w ws)
  have a: "trans_star_output t q_0 (w # ws) = op1"
    using trans_star_output_state Cons
    by (metis prod.inject)
  then obtain op11 op12 where
    op: "op1 = op11 # op12"
    by (meson old.prod.exhaust split_trans_star_output)
  then have "\<exists> q'. t (q_0,w) = (q',op11) \<and> trans_star t q' ws = (st,op12)"
    using split_trans_star_rev Cons
    by fast
  then obtain q' where
    q': "t (q_0,w) = (q',op11) \<and> trans_star t q' ws = (st,op12)"
    by blast
  then have "trans_star t q' (ws @ is) = (st2,op12 @ op2)"
    using Cons
    by blast
  then have "trans_star t q_0 (w # ws @ is) = (st2,op11 # op12 @ op2)"
    using split_trans_star q'
    by simp
  then show ?case
    by (simp add: op)

qed


lemma trans_star_two_nested:
  "trans_star t (fst (trans_star t q_0 acc)) is =
  (fst (trans_star t q_0 (acc @ is)),drop (length acc) (snd (trans_star t q_0 (acc @ is))))"
proof -
  obtain st op1 where
    op1: "(trans_star t q_0 acc) = (st,op1)"
    by fastforce
  obtain st2 op2 where
    op2: "(trans_star t st is) = (st2,op2)"
    by fastforce
  have "trans_star t (fst (trans_star t q_0 acc)) is = trans_star t st is"
    using op1 op2
    by simp
  show ?thesis proof (standard,goal_cases)
    case 1
    have "fst (trans_star t q_0 (acc @ is)) = fst (trans_star t st is)"
      using trans_star_two op1 op2
      by fastforce
    then show ?case
      using op1 op2
      by auto
  next
    case 2
    have a: "snd (trans_star t q_0 (acc @ is)) = (op1 @ op2)"
      using op1 op2 trans_star_two
      by fastforce
    have "length op1 = length acc"
      using op1 trans_star_length
      by metis
    then have "drop (length acc) (op1 @ op2) = op2"
      by simp
    then show ?case
      using a op1 op2
      by simp
  qed
qed


lemma sim_subset:
  assumes "mealy_invar (q_0,S,t)" and
    "mealy_invar (p_0,S_2,g)" and
    "func_sim f (q_0,S,t) (p_0,S_2,g)" and
    "q \<in> S" and
    "trans_star_output t q i = ot"
  shows "trans_star_output g (f q) i = ot"
using assms proof (induction i arbitrary: q ot)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons a i)
  have a: "\<forall> q' ot. t (q,a) = (q',ot) \<longrightarrow> g (f q,a) = (f q',ot)"
    using assms(3) Cons(5) assms(1) assms(2) unfolding mealy_invar_def func_sim_def
    apply auto
    by metis
  have "\<exists> q' out. t (q,a) = (q',out)"
    using Cons
    by auto
  then obtain q' out where
    q: "t (q,a) = (q',out)"
    using Cons
    by fastforce
  then have "\<exists> os. ot = out # os"
    using Cons
    by (auto split: prod.splits option.splits)
  then obtain os where
    ot: "ot = out # os"
    by auto
  then have "trans_star_output t q' i = os \<Longrightarrow> trans_star_output g (f q') i = os"
    using Cons.IH Cons.prems(4) q assms(1) assms(2) assms(3) unfolding mealy_invar_def
    by blast
  then have "trans_star_output t q (a # i) = (out # os) \<Longrightarrow> trans_star_output g (f q) (a # i) = (out # os)"
    using a q split_trans_star_output
    by (auto split: prod.splits option.splits)
  then show ?case
    using Cons q a ot
    by argo
qed


definition apart :: "('state,'input,'output) mealy \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
  "apart m q p \<equiv> (case m of
    (q_0,Q,t) \<Rightarrow> \<exists> i x y. trans_star_output t p i = x \<and> trans_star_output t q i = y \<and> x \<noteq> y)"


definition apart_with_witness :: "('state,'input,'output) mealy \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> 'input list \<Rightarrow> bool" where
  "apart_with_witness m q p is \<equiv> (case m of
    (q_0,Q,t) \<Rightarrow> \<exists> x y. trans_star_output t p is = x \<and> trans_star_output t q is = y \<and> x \<noteq> y)"

lemma simulation_apart:
  assumes "func_sim f (q_0,Q,t) (p_0,P,g)" and
    "apart (q_0,Q,t) q q'" and
    "q \<in> Q" and
    "q' \<in> Q" and
    "mealy_invar (p_0,P,g)" and
    "mealy_invar (q_0,Q,t)"
  shows "\<not> mealy_eq (p_0,P,g) (f q) (p_0,P,g) (f q')"
proof
    assume "mealy_eq (p_0,P,g) (f q) (p_0,P,g) (f q')"
  then have c: "(\<forall> is. trans_star_output g (f q) is = trans_star_output g (f q') is)" unfolding mealy_eq_def
    by fastforce

  have "\<exists> w x y. trans_star_output t q w = x \<and> trans_star_output t q' w = y \<and> x \<noteq> y"
    using assms (2) unfolding apart_def
    apply auto
    by metis
  then obtain w x y where
    w: "trans_star_output t q w = x \<and> trans_star_output t q' w = y \<and> x \<noteq> y"
    by blast
  then have a: "trans_star_output g (f q) w = x"
    using assms sim_subset
    by fast
  have b: "trans_star_output g (f q') w = y"
    using w assms sim_subset
    by meson
  have d: "x \<noteq> y"
    using w
    by simp
  then show False
    using a b c d
    by force
qed


lemma weak_co_transitivity:
  assumes "apart_with_witness (q_0,Q,t) r r' \<sigma>" and
    "mealy_invar (q_0,Q,t)" and
    "trans_star_output t q \<sigma> = x"
  shows "apart (q_0,Q,t) r q \<or> apart (q_0,Q,t) r' q"
proof auto
  show "\<not> apart (q_0,Q,t) r' q \<Longrightarrow> apart (q_0,Q,t) r q"
    using assms unfolding apart_def apart_with_witness_def
    by blast
qed


end
