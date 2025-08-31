theory MealyMachine
  imports Main "HOL-Library.LaTeXsugar"
begin

sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

text \<open>trans mealy\<close>


type_synonym ('s,'in,'out) trans = "(('s \<times> 'in) \<Rightarrow> ('s \<times> 'out))"

type_synonym ('s,'in,'out) mealy = "'s \<times> ('s,'in,'out) trans"


fun run_mealy :: "('s,'in,'out) trans \<Rightarrow> 's \<Rightarrow> 'in list \<Rightarrow> ('s \<times> 'out list)" where
"run_mealy f q [] = (q, [])" |
"run_mealy f q (w # ws) = (let (st,op) = f (q,w) in 
  (let (q',x) = run_mealy f st ws in (q',op # x)))"


definition outs_run_mealy :: "('s,'in,'out) trans \<Rightarrow> 's \<Rightarrow> 'in list \<Rightarrow> ('out list)" where
"outs_run_mealy f q ins =  snd (run_mealy f q ins)" 
definition state_run_mealy :: "('s,'in,'out) trans \<Rightarrow> 's \<Rightarrow> 'in list \<Rightarrow> ('s)" where
"state_run_mealy f q ins = fst (run_mealy f q ins)" 



lemma run_mealy_twostep:"run_mealy f q' ins = (q'',out) \<Longrightarrow> 
    f (q,i) = (q',ou) \<Longrightarrow> 
  run_mealy f q (i#ins) = (q'',ou#out)"
  by simp

lemma outs_run_mealy_twostep:"outs_run_mealy f q' ins = out \<Longrightarrow> f (q,i) = (q',ou) \<Longrightarrow> outs_run_mealy f q (i#ins) = ou#out"
  unfolding outs_run_mealy_def using run_mealy_twostep 
  by (metis split_pairs)

lemma out_state_run_mealy: "run_mealy f q i = (state_run_mealy f q i,outs_run_mealy f q i)"
unfolding outs_run_mealy_def state_run_mealy_def 
  by auto
  

definition eq_mealy :: "('s,'in,'out) mealy \<Rightarrow> 's \<Rightarrow> ('s2,'in,'out) mealy \<Rightarrow> 's2 \<Rightarrow> bool" where
"eq_mealy a q b p \<equiv> (case (a,b) of
    ((q_0,f),(p_0,g)) \<Rightarrow> (\<forall> is. outs_run_mealy f q is = outs_run_mealy g p is))"

abbreviation equal :: "('s,'in,'out) mealy \<Rightarrow> ('s2,'in,'out) mealy \<Rightarrow> bool" (infixr"\<approx>" 80) where
"a \<approx> b \<equiv> (case (a,b) of
    ((q_0,f),(p_0,g)) \<Rightarrow> eq_mealy a q_0 b p_0)"



definition func_sim_mealy :: "('s \<Rightarrow> 's2) \<Rightarrow> ('s,'in,'out) mealy \<Rightarrow>
    ('s2,'in,'out) mealy \<Rightarrow> bool" where
"func_sim_mealy f a b \<equiv> (case (a,b) of
    ((q_0,t),(p_0,g)) \<Rightarrow> (f q_0 = p_0) \<and> (\<forall> q q' i op. t (q,i) = (q',op) \<longrightarrow>
      g (f q,i) = (f q',op)))"


lemma split_outs_run_mealy: "t (q,i) = (q',ot) \<Longrightarrow> outs_run_mealy t q' is = op \<Longrightarrow>
    outs_run_mealy t q (i # is) = (ot # op)"
  unfolding outs_run_mealy_def
  by (auto split: prod.splits option.splits)


lemma split_outs_run_mealy_rev: "outs_run_mealy t q (i # is) = (ot # op) \<Longrightarrow>
    \<exists> q'. t (q,i) = (q',ot) \<and> outs_run_mealy t q' is = op"
  unfolding outs_run_mealy_def
  by (auto split: prod.splits option.splits)


lemma split_run_mealy: "t (q,i) = (q',ot) \<Longrightarrow> run_mealy t q' is = (st,op) \<Longrightarrow>
    run_mealy t q (i # is) = (st,ot # op)"
  by (auto split: prod.splits option.splits)


lemma split_run_mealy_rev: "run_mealy t q (i # is) = (st,ot # op) \<Longrightarrow>
    \<exists> q'. t (q,i) = (q',ot) \<and> run_mealy t q' is = (st,op)"
  by (auto split: prod.splits option.splits)

lemma run_mealy_split_end:
  assumes "t (st,i) = (st',op)" and
    "run_mealy t q acc = (st,out)"
  shows "run_mealy  t q (acc @ [i]) =  (st',out @ [op])"
using assms proof (induction acc arbitrary: out q)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a acc)
 
  obtain q' op' where q':"t (q,a) = (q', op')"
    by fastforce
   then have "run_mealy t q (a # acc) = (let (qnew,x) = run_mealy t q' acc in (qnew,op' # x)) "
     by auto
   then have "EX outnew. run_mealy t q' acc = (st,outnew)" using Cons 
     by (simp add: out_state_run_mealy)
   then obtain outnew where outnew:"run_mealy t q' acc = (st,outnew)" 
     by presburger
   then have "run_mealy t q' (acc @ [i]) = (st', outnew @ [op])" using Cons 
     by blast
   then have "run_mealy t q (a#(acc@[i])) =  (st',op' # outnew@[op]) " using  q' 
     by simp
  then show ?case using q' outnew 
    using Cons.prems(2) by auto
qed



lemma run_mealy_length: "run_mealy t q_0 iss = (q,os) \<Longrightarrow> length iss = length os"
proof (induction iss arbitrary: os q q_0)
  case Nil
  then show ?case
    by auto
next
  case (Cons a iss)
  then show ?case
    by (auto split: prod.splits option.splits)
qed


lemma run_mealy_two:
  assumes "run_mealy t q_0 acc = (st,op1)" and
    "run_mealy t st is = (st2,op2)"
  shows "(run_mealy t q_0 (acc @ is)) = (st2,op1 @ op2)"
using assms proof (induction acc arbitrary: q_0 op1 op2 st st2)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons w ws)
  have a: "outs_run_mealy t q_0 (w # ws) = op1"
    using out_state_run_mealy Cons
    by (metis prod.inject)
  then obtain op11 op12 where
    op: "op1 = op11 # op12"
    by (meson old.prod.exhaust split_outs_run_mealy)
  then have "\<exists> q'. t (q_0,w) = (q',op11) \<and> run_mealy t q' ws = (st,op12)"
    using split_run_mealy_rev Cons
    by fast
  then obtain q' where
    q': "t (q_0,w) = (q',op11) \<and> run_mealy t q' ws = (st,op12)"
    by blast
  then have "run_mealy t q' (ws @ is) = (st2,op12 @ op2)"
    using Cons
    by blast
  then have "run_mealy t q_0 (w # ws @ is) = (st2,op11 # op12 @ op2)"
    using split_run_mealy q'
    by simp
  then show ?case
    by (simp add: op)

qed


lemma run_mealy_two_nested:
"run_mealy t (fst (run_mealy t q_0 acc)) is =
    (fst (run_mealy t q_0 (acc @ is)),drop (length acc) (snd (run_mealy t q_0 (acc @ is))))"
proof -
  obtain st op1 where
    op1: "(run_mealy t q_0 acc) = (st,op1)"
    by fastforce
  obtain st2 op2 where
    op2: "(run_mealy t st is) = (st2,op2)"
    by fastforce
  have "run_mealy t (fst (run_mealy t q_0 acc)) is = run_mealy t st is"
    using op1 op2
    by simp
  show ?thesis proof (standard,goal_cases)
    case 1
    have "fst (run_mealy t q_0 (acc @ is)) = fst (run_mealy t st is)"
      using run_mealy_two op1 op2
      by fastforce
    then show ?case
      using op1 op2
      by auto
  next
    case 2
    have a: "snd (run_mealy t q_0 (acc @ is)) = (op1 @ op2)"
      using op1 op2 run_mealy_two
      by fastforce
    have "length op1 = length acc"
      using op1 run_mealy_length
      by metis
    then have "drop (length acc) (op1 @ op2) = op2"
      by simp
    then show ?case
      using a op1 op2
      by simp
  qed
qed


lemma sim_subset:
  assumes "func_sim_mealy f (q_0,t) (p_0,g)" and
    "outs_run_mealy t q i = ot"
  shows "outs_run_mealy g (f q) i = ot"
using assms proof (induction i arbitrary: q ot)
  case Nil
  then show ?case
     unfolding outs_run_mealy_def
    by fastforce
next
  case (Cons a i)
  have a: "\<forall> q' ot. t (q,a) = (q',ot) \<longrightarrow> g (f q,a) = (f q',ot)"
    using assms Cons
    unfolding func_sim_mealy_def
    by simp     
  have "\<exists> q' out. t (q,a) = (q',out)"
    using Cons
    by auto
  then obtain q' out where
    q: "t (q,a) = (q',out)"
    using Cons
    by fastforce
  then have "\<exists> os. ot = out # os"
    using Cons   unfolding outs_run_mealy_def
    by (auto split: prod.splits option.splits)
  then obtain os where
    ot: "ot = out # os"
    by auto
  then have "outs_run_mealy t q' i = os \<Longrightarrow> outs_run_mealy g (f q') i = os"
    using Cons assms 
    by blast
  then have "outs_run_mealy t q (a # i) = (out # os) \<Longrightarrow> outs_run_mealy g (f q) (a # i) = (out # os)"
    using a q split_outs_run_mealy   unfolding outs_run_mealy_def
    by (auto split: prod.splits option.splits)
  then show ?case
    using Cons q a ot
    by argo
qed


definition apart_mealy :: "('s,'in,'out) mealy \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
"apart_mealy m q p \<equiv> (case m of
    (q_0,t) \<Rightarrow> \<exists> i x y. outs_run_mealy t p i = x \<and> outs_run_mealy t q i = y \<and> x \<noteq> y)"


fun apart_machines :: "('s,'in,'out) trans \<Rightarrow> 's \<Rightarrow> ('s2,'in,'out) trans \<Rightarrow> 's2 \<Rightarrow> bool" where
"apart_machines t q f p = (\<exists> i. outs_run_mealy t q i \<noteq> outs_run_mealy f p i)"

lemma simulation_apart:
  assumes "func_sim_mealy f (q_0,t) (p_0,g)" and
    "apart_mealy (q_0,t) q q'" 
  shows "\<not> eq_mealy (p_0,g) (f q) (p_0,g) (f q')"
proof
  assume "eq_mealy (p_0,g) (f q) (p_0,g) (f q')"
  then have c: "(\<forall> is. outs_run_mealy g (f q) is = outs_run_mealy g (f q') is)"
    unfolding eq_mealy_def
    by fastforce
  have "\<exists> w x y. outs_run_mealy t q w = x \<and> outs_run_mealy t q' w = y \<and> x \<noteq> y"
    using assms (2)
    unfolding apart_mealy_def
    apply simp
    by metis
  then obtain w x y where
    w: "outs_run_mealy t q w = x \<and> outs_run_mealy t q' w = y \<and> x \<noteq> y"
    by blast
  then have a: "outs_run_mealy g (f q) w = x"
    using assms sim_subset
    by fast
  have b: "outs_run_mealy g (f q') w = y"
    using w assms sim_subset
    by meson
  have d: "x \<noteq> y"
    using w
    by simp
  then show False
    using a b c d
    by force
qed





end
