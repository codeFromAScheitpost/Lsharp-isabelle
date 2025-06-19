theory observation_tree
  imports "./mealy"
begin
sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]


datatype ('input,'output) obs_tree = Node "('input :: finite) list \<times> ('input \<Rightarrow> (('input,'output) obs_tree \<times> 'output) option)"


fun otree_star :: "('input,'output) obs_tree \<Rightarrow> ('input :: finite) list \<Rightarrow> (('input,'output) obs_tree \<times> 'output list) option" where
"otree_star ot [] = Some (ot, [])" |
"otree_star (Node (acc,t)) (i # is) = (case t i of
    Some (n,op) \<Rightarrow> (case (otree_star n is) of
      Some (ot,ops) \<Rightarrow> Some (ot,op # ops) |
      None \<Rightarrow> None) |
    None \<Rightarrow> None)"


fun out_star :: "('input,'output) obs_tree \<Rightarrow> ('input :: finite) list \<Rightarrow> ('output list) option" where
"out_star ot [] = Some []" |
"out_star (Node (acc,t)) (i # is) = (case t i of
    Some (n,op) \<Rightarrow>
    (case (out_star n is) of
      Some ops \<Rightarrow> Some (op # ops) |
      None \<Rightarrow> None) |
    None \<Rightarrow> None)"

definition func_sim :: "('state,'input,'output) mealy \<Rightarrow> ('input,'output) obs_tree \<Rightarrow> (('input :: finite) list \<Rightarrow> 'state) \<Rightarrow> bool" where
"func_sim m T f = (case m of
    (q_0,t) \<Rightarrow> ((f [] = q_0) \<and> (\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow>
      trans_star t (f acc) is = (f (acc @ is),(drop (length acc) ops)))))"


fun apart :: "(('input :: finite),'output) obs_tree \<Rightarrow> ('input,'output) obs_tree \<Rightarrow> bool" where
"apart (Node t1) (Node t2) = (\<exists> i x n n2 y. otree_star (Node t1) i = Some (n,x) \<and>
    otree_star (Node t2) i = Some (n2,y) \<and> x \<noteq> y)"

fun apart_text :: "(('input :: finite),'output) obs_tree \<Rightarrow> 'input list \<Rightarrow> 'input list \<Rightarrow> bool" where
"apart_text q_0 t1 t2 = (\<exists> i x y. out_star q_0 (t1 @ i) = Some x \<and>
    out_star q_0 (t2 @ i) = Some y \<and>
    drop (length t1) x \<noteq> drop (length (t2)) y)"

fun isolated :: "(('input :: finite),'output) obs_tree \<Rightarrow> 'input list set \<Rightarrow> 'input list \<Rightarrow> bool" where
"isolated q_0 S f = (\<forall> s \<in> S. apart_text q_0 s f)"

fun apart_witness :: "('input :: finite) list \<Rightarrow> ('input,'output) obs_tree \<Rightarrow> 'input list \<Rightarrow> 'input list \<Rightarrow> bool" where
"apart_witness is q_0 t1 t2 = (\<exists> x y. out_star q_0 (t1 @ is) = Some x \<and>
    out_star q_0 (t2 @ is) = Some y \<and>
    drop (length t1) x \<noteq> drop (length t2) y)"


fun output_query :: "('state,('input :: finite),'output) mealy \<Rightarrow> 'input list \<Rightarrow> 'output list" where
"output_query (q_0,t) is = trans_star_output t q_0 is"


fun process_output_query :: "('input,'output) obs_tree \<Rightarrow> ('input :: finite) list \<Rightarrow> 'output list \<Rightarrow> ('input,'output) obs_tree" where
"process_output_query q [] [] = q" |
"process_output_query q i [] = undefined" |
"process_output_query q [] _ = undefined" |
"process_output_query (Node (acc,t)) (i # is) (op # ops) = (case t i of
    None \<Rightarrow> (Node (acc,(\<lambda> j. if j = i
      then Some (process_output_query (Node (acc @ [i],(\<lambda> k. None))) is ops,op)
      else t j))) |
    Some (tree,out) \<Rightarrow> (Node (acc,(\<lambda> j. if j = i
      then Some ((process_output_query tree is ops),out)
      else t j))))"


type_synonym ('input,'output) state = "('input list set \<times> 'input list set \<times> ('input,'output) obs_tree)"


fun sapart :: "(('input :: finite),'output) state \<Rightarrow> bool" where
"sapart (S,F,T) = (\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart_text T s1 s2)"

fun invar :: "('state,('input :: finite),'output) mealy \<Rightarrow> (('input :: finite),'output) state \<Rightarrow> bool" where
"invar m (S,F,T) = ((\<forall> e. \<not> (e \<in> S \<and> e \<in> F) \<and>
      finite S \<and> finite F \<and>
      (e \<in> S \<or> e \<in> F \<longrightarrow> out_star T e \<noteq> None)) \<and>
    sapart (S,F,T) \<and>
    (\<forall> i. out_star T i \<noteq> None \<longrightarrow> out_star T i = Some (output_query m i)) \<and>
    (\<forall> f \<in> F. \<exists> s \<in> S. \<exists> i. f = s @ [i]))"

fun transfunc :: "(('input :: finite),'output) state \<Rightarrow> ('input list,'input,'output) transition \<Rightarrow> bool" where
"transfunc (S,F,T) t =
    (\<forall> s \<in> S. \<forall> i. (case otree_star T s of
      Some (Node (acc,tran),op) \<Rightarrow> (case tran i of
        Some (n,out) \<Rightarrow>
        (if (s @ [i]) \<in> S
          then t (s,i) = (s @ [i],out)
          else (\<exists> y \<in> S. \<not> apart_text T y (s @ [i]) \<and> t (s,i) = (y,out))))))"


inductive algo_step :: "('state,('input :: finite),'output) mealy \<Rightarrow>
    'input list set \<times> 'input list set \<times> ('input,'output) obs_tree \<Rightarrow>
    'input list set \<times> 'input list set \<times> ('input,'output) obs_tree \<Rightarrow>
    bool" where
rule1: "\<lbrakk>f \<in> F; \<forall> s \<in> S. apart_text T s f\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S \<union> {f},F - {f},T)" |

rule2: "\<lbrakk>s \<in> S; (out_star T (s @ [i]) = None);
      output_query m (s @ [i]) = out\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S,F \<union> {s @ [i]},process_output_query T (s @ [i]) out)" |

rule3: "\<lbrakk>s1 \<in> S; s2 \<in> S;f \<in> F;
      \<not> apart_text T f s1;
      \<not> apart_text T f s2;
      apart_witness w T s1 s2;
      output_query m (f @ w) = out\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S,F,process_output_query T (f @ w) out)" |

rule4: "\<lbrakk>\<forall> i. \<not> isolated T S (s @ [i]);
      \<forall> s \<in> S. \<forall> i. out_star T (s @ [i]) \<noteq> None;
      fs \<in> F;
      s \<in> S;
      \<not> apart_text T s fs;
      drop (length s) (trans_star_output f q_0 (s @ inp)) \<noteq>
      drop (length fs) (trans_star_output f q_0 (fs @ inp));
      output_query (q_0,f) (s @ inp) = outs;
      output_query (q_0,f) (fs @ inp) = outf\<rbrakk> \<Longrightarrow>
    algo_step (q_0,f) (S,F,T) (S,F,process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)"


fun norm_fst :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_fst (S,F,T) = ((card S * (card S + 1)) div 2)"

fun norm_snd :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_snd (S,F,T) = card {(q,i). q \<in> S \<and> out_star T (q @ [i]) \<noteq> None}"

fun norm_trd :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_trd (S,F,T) = card {(q,p). q \<in> S \<and> p \<in> F \<and> apart_text T q p}"


fun norm_set :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_set st = norm_fst st + norm_snd st + norm_trd st"

locale Mealy =
  fixes m :: "('state :: finite,'input :: finite,'output) mealy" and
    I :: "'input set" and
    Q :: "'state set"
  assumes mdef: "m = (q_0,t)" and
    univI: "I = UNIV" and
    univQ: "Q = UNIV"
begin


section "apart"


lemma apart_sim:
  assumes "apart_text T p q" and
    "func_sim (q_0,t) T f"
  shows "f q \<noteq> f p"
proof
  assume as: "f q = f p"
  then have a: "\<forall> is ops. out_star T (q @ is) =
      Some ops \<longrightarrow> trans_star t (f q) is = (f (q @ is),(drop (length q) ops))"
    using assms
    unfolding func_sim_def
    by blast
  have b: "\<forall> is ops. out_star T (p @ is) =
      Some ops \<longrightarrow> trans_star t (f p) is = (f (p @ is),(drop (length p) ops))"
    using assms
    unfolding func_sim_def as
    by simp
  have "(\<exists> i x y. out_star T (q @ i) = Some x \<and> out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq>
      drop (length p) y)"
    using assms
    by fastforce
  then show False
    using a b as
    by fastforce
qed


lemma apart_none:
  assumes "\<not> apart_text T f s1" and
    "\<not> apart_text T f s2" and
    "apart_witness w T s1 s2"
  shows "out_star T (f @ w) = None"
proof (rule ccontr)
  assume ass: "out_star T (f @ w) \<noteq> None"
  obtain x where
    x: "out_star T (s1 @ w) = Some x"
    using assms
    by auto
  obtain y where
    y: "out_star T (s2 @ w) = Some y"
    using assms
    by auto
  have neq: "drop (length s2) y \<noteq> drop (length s1) x"
    using assms x y
    by fastforce
  then obtain z where
    z: "out_star T (f @ w) = Some z"
    using ass
    by blast
  then have a: "drop (length f) z = drop (length s1) x"
    using z x assms
    by simp
  then have b: "drop (length f) z = drop (length s2) y"
    using z y assms
    by simp
  show False
    using a b neq
    by simp
qed


lemma not_none_not_both_apart:
  assumes "out_star T (f @ w) = Some z" and
    "apart_witness w T s1 s2"
  shows "apart_text T f s1 \<or> apart_text T f s2"
    by (metis apart_none assms option.discI)


section "output_query"


lemma output_query_length:
  assumes "output_query m iss = os"
  shows "length iss = length os"
proof -
  obtain q_0 t where
    m: "m = (q_0,t)"
    by fastforce
  then have "output_query (q_0,t) iss = os \<Longrightarrow> length iss = length os"
    using trans_star_length
    apply (simp split: prod.splits option.splits)
    using trans_star_output_state
    by fastforce
  then show ?thesis
    using m assms
    by blast
qed


lemma card_diff: "finite A \<Longrightarrow> card (A - B) \<le> card A"
  unfolding card_def
  by (metis Diff_subset card_def card_mono)


section "Star"


lemma otree_eq_out: "(case otree_star (Node (l,r)) i of
    None \<Rightarrow> out_star (Node (l,r)) i = None |
    Some (n,out) \<Rightarrow> out_star (Node (l,r)) i = Some out)"
proof (induction i arbitrary: l r)
  case Nil
  then show ?case
    by auto
next
  case (Cons a i)
  then show ?case proof (cases "r a")
    case None
    then show ?thesis
      by simp
  next
    case (Some b)
    then obtain l2 r2 o2 where
      b: "b = (Node (l2,r2),o2)"
      by (metis obs_tree.exhaust surj_pair)
    then have one: "otree_star (Node (l,r)) (a # i) = (case otree_star (Node (l2,r2)) i of
        None \<Rightarrow> None |
        Some (node,out) \<Rightarrow> Some (node,o2 # out))"
      using Some
      by simp
    have two: "out_star (Node (l,r)) (a # i) = (case out_star (Node (l2,r2)) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some b
      by simp
    have "(case otree_star (Node (l2,r2)) i of
        None \<Rightarrow> out_star (Node (l2,r2)) i = None |
        Some (n,out) \<Rightarrow> out_star (Node (l2,r2)) i = Some out)"
      using Cons
      by simp
    then show ?thesis
      using one two
      apply (cases "otree_star (Node (l2,r2)) i")
      by auto
  qed
qed


lemma out_eq_otree: "\<exists> node. (case out_star (Node (l,r)) i of
    None \<Rightarrow> otree_star (Node (l,r)) i = None |
    Some out \<Rightarrow> otree_star (Node (l,r)) i = Some (node,out))"
proof (induction i arbitrary: l r)
  case Nil
  then show ?case
    by auto
next
  case (Cons a i)
  then show ?case proof (cases "r a")
    case None
    then show ?thesis
      by simp
  next
    case (Some b)
    then obtain l2 r2 o2 where
      b: "b = (Node (l2,r2),o2)"
      by (metis obs_tree.exhaust surj_pair)
    then have one: "out_star (Node (l,r)) (a # i) = (case out_star (Node (l2,r2)) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some
      by simp
    have two: "out_star (Node (l,r)) (a # i) = (case out_star (Node (l2,r2)) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some b
      by simp
    have three: "otree_star (Node (l,r)) (a # i) = (case otree_star (Node (l2,r2)) i of
        None \<Rightarrow> None |
        Some (node,out) \<Rightarrow> Some (node,o2 # out))"
      using Some b
      by simp
    have "\<exists> node. (case out_star (Node (l2,r2)) i of
        None \<Rightarrow> otree_star (Node (l2,r2)) i = None |
        Some out \<Rightarrow> otree_star (Node (l2,r2)) i = Some (node,out))"
      using Cons
      by simp
    then show ?thesis
      using one two three
      apply (cases "out_star (Node (l2,r2)) i")
      by auto
  qed
qed


lemma otree_induct_helper: "t i = (Some (tree,out)) \<Longrightarrow> length op = length acc \<Longrightarrow>
    otree_star (process_output_query tree acc op) acc = Some (lt,lout) \<Longrightarrow>
    otree_star (process_output_query (Node (acc_n,t)) (i # acc) (out # op)) (i # acc) = Some (lt,out # lout)"
  by (induction acc) auto


lemma output_induct_helper: "t i = (Some (tree,out)) \<Longrightarrow> length op = length acc \<Longrightarrow>
    out_star (process_output_query tree acc op) acc = Some lout \<Longrightarrow>
    out_star (process_output_query (Node (acc_n,t)) (i # acc) (out # op)) (i # acc) = Some (out # lout)"
  by (induction acc) auto


lemma otree_induct_helper_none: "t i = None \<Longrightarrow> length op = length acc \<Longrightarrow>
    otree_star (process_output_query (Node (acc_n @ [i],Map.empty)) acc op) acc = Some (lt,lout) \<Longrightarrow>
    otree_star (process_output_query (Node (acc_n,t)) (i # acc) (out # op)) (i # acc) = Some (lt,out # lout)"
  by (induction acc) auto


lemma output_induct_helper_none: "t i = None \<Longrightarrow> length op = length acc \<Longrightarrow>
    out_star (process_output_query (Node (acc_n @ [i],Map.empty)) acc op) acc = Some lout \<Longrightarrow>
    out_star (process_output_query (Node (acc_n,t)) (i # acc) (out # op)) (i # acc) = Some (out # lout)"
  by (induction acc) auto


lemma otree_split: "otree_star (Node (l,r)) (a # acc) = Some (tr1,out1) \<Longrightarrow> r a \<noteq> None"
  by (auto split: prod.splits option.splits)


lemma out_split: "out_star (Node (l,r)) (a # acc) = Some (out1) \<Longrightarrow> r a \<noteq> None"
  by (auto split: prod.splits option.splits)


lemma otree_star_split_none:
  assumes "t i = None" and
    "otree_star (Node (accq,tq)) acc = Some (Node (ac,t),ops)"
  shows "otree_star (Node (accq,tq)) (acc @ [i]) = None"
using assms proof (induction acc arbitrary: ops accq tq ac)
  case Nil
  then show ?case
    by simp
next
  case (Cons a acc)
  then show ?case proof (cases "tq a")
    case None
    then show ?thesis
      using Cons
      by auto
  next
    case (Some b)
    obtain tr on where
      b: "b = (tr,on)"
      by fastforce
    then have apart_i: "otree_star (Node (accq,tq)) ((a # acc @ [i])) =
        (case otree_star tr (acc @ [i]) of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some
      by auto
    then have apart: "otree_star (Node (accq,tq)) ((a # acc)) =
        (case otree_star tr acc of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some b
      by auto

    then have "otree_star tr acc \<noteq> None"
      using Some Cons b
      by (metis option.distinct(1) option.simps(4))

    then obtain opl where
      opl: "otree_star tr acc = Some (Node (ac,t),opl)"
      using Some Cons b apart
      by fastforce
    obtain ntq nac where
      ntq: "tr = Node (nac,ntq)"
      using b Some Cons
      by (metis obs_tree.exhaust surj_pair)
    then have "otree_star (Node (nac,ntq)) (acc @ [i]) = None"
      using Cons opl
      by blast
    then show ?thesis
      using Cons b Some apart opl ntq apart_i
      by auto
  qed
qed


lemma otree_star_split:
  assumes "t i = Some (tree,op)" and
    "otree_star (Node (accq,tq)) acc = Some (Node (ac,t),ops)"
  shows "otree_star (Node (accq,tq)) (acc @ [i]) = Some (tree,ops @ [op])"
using assms proof (induction acc arbitrary: ops accq tq ac)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons a acc)
  then show ?case proof (cases "tq a")
    case None
    then show ?thesis
      using Cons
      by auto
  next
    case (Some b)
    obtain tr on where
      b: "b = (tr,on)"
      by fastforce
    then have apart_i: "otree_star (Node (accq,tq)) (a # acc @ [i]) =
        (case otree_star tr (acc @ [i]) of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some
      by auto
    then have apart: "otree_star (Node (accq,tq)) ((a # acc)) =
        (case otree_star tr acc of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some b
      by auto
    then have "otree_star tr acc \<noteq> None"
      using Some Cons b
      by (metis option.distinct(1) option.simps(4))
    then obtain opl where
      opl: "otree_star tr acc = Some (Node (ac,t),opl)"
      using Some Cons b apart
      by fastforce
    obtain ntq nac where
      ntq: "tr = Node (nac,ntq)"
      using b Some Cons
      by (metis obs_tree.exhaust surj_pair)
    then have "otree_star (Node (nac,ntq)) (acc @ [i]) = Some (tree,opl @ [op])"
      using Cons opl
      by blast
    then show ?thesis
      using Cons b Some apart opl ntq apart_i
      by auto
  qed
qed


section "process Output Query"


lemma process_op_query_not_none: "length ip = length op \<Longrightarrow> otree_star (process_output_query (Node (acc,t)) ip op) ip \<noteq> None"
proof (induction ip arbitrary: op t acc)
  case Nil
  then show ?case
    by auto
next
  case (Cons a ip)
  obtain ofs os where
    ofs: "op = os # ofs"
    using Cons
    apply simp
    by (meson Suc_length_conv)
  then show ?case proof (cases "t a")
    case None
    have "otree_star (process_output_query (Node (acc @ [a],(\<lambda> is. None))) ip ofs) ip \<noteq> None"
      using Cons ofs
      by auto
    then obtain lt lout where
      "otree_star (process_output_query (Node (acc @ [a],(\<lambda> is. None))) ip ofs) ip = Some (lt,lout)"
      by fast
    then have "otree_star (process_output_query (Node (acc,t)) (a # ip) op) (a # ip) = Some (lt,os # lout)"
      using Cons ofs None otree_induct_helper_none
      by auto
    then show ?thesis
      by auto
  next
    case (Some b)
    then show ?thesis proof (cases b)
      case (Pair tree c)
      have "otree_star (process_output_query tree ip ofs) ip \<noteq> None"
        using Cons ofs
        apply simp
        by (metis obs_tree.exhaust surj_pair)
      then obtain lt lout where
        "otree_star (process_output_query tree ip ofs) ip = Some (lt,lout)"
        by fast
      then have "otree_star (process_output_query (Node (acc,t)) (a # ip) op) (a # ip) = Some (lt,c # lout)"
        using Cons ofs Some Pair otree_induct_helper
        by auto
      then show ?thesis
        by auto
    qed
  qed
qed


lemma output_query_different: "length op = length ip \<Longrightarrow> i \<noteq> ac \<Longrightarrow>
    (case process_output_query (Node (acc,t)) (i # ip) (os # op) of
      (Node (accs,ts)) \<Rightarrow> ts ac = t ac)"
  by (auto split: prod.splits option.splits)


lemma otree_star_output_query_different:
  assumes "ac \<noteq> i" and
    "length ip = length op" and
    "t ac = Some (tree,outies)"
  shows "otree_star (process_output_query (Node (acc,t)) (i # ip) (os # op)) (ac # list) =
      (case otree_star tree list of
        Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
        None \<Rightarrow> None)"
proof -
  have "(case process_output_query (Node (acc,t)) (i # ip) (os # op) of
      (Node (accs,ts)) \<Rightarrow> ts ac = t ac)"
    using assms output_query_different[of op ip i ac]
    by auto
  then show ?thesis
    using assms(3)
    by (auto split: prod.splits option.splits)
qed


lemma output_query_retains_some:
  assumes "length ip = length op" and
    "otree_star q_0 acc \<noteq> None"
  shows "otree_star (process_output_query q_0 ip op) acc \<noteq> None"
using assms proof (induction ip arbitrary: op acc q_0)
  case Nil
  then show ?case
    by simp
next
  case a: (Cons a ip)
  obtain os ops where
    os: "op = os # ops"
    using a
    apply simp
    by (meson Suc_length_conv)
  then show ?case proof (cases acc)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons ac list)
    then show ?thesis proof (cases q_0)
      case (Node x)
      then show ?thesis proof (cases x)
        case (Pair l r)
        then show ?thesis using a proof (cases "a = ac")
          case True
          then show ?thesis proof (cases "r ac")
            case None
            then have "otree_star (q_0) (ac # list) = None"
              using Pair Node
              by auto
            then show ?thesis
              using a Cons
              by simp
          next
            case (Some c)
            then obtain tree outies where
              outies: "r ac = Some (tree,outies)"
              using Pair Node Cons a Some
              by fastforce
            then have h2: "otree_star (process_output_query q_0 (a # ip) (os # ops)) (ac # list) =
                (case otree_star (process_output_query tree ip ops) list of
                  Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                  None \<Rightarrow> None)"
              using Some True Pair Node Cons a otree_star_output_query_different
              by auto
            have h1: "otree_star q_0 (ac # list) = (case otree_star tree list of
                Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                None \<Rightarrow> None)"
              using outies Pair Node
              by auto
            have "otree_star q_0 (ac # list) \<noteq> None"
              using a Cons
              by blast
            then have "otree_star tree list \<noteq> None"
              using a h1
              by (metis option.simps(4))
            then have "otree_star (process_output_query tree ip ops) list \<noteq> None"
              using a os
              by force
            then show ?thesis
              using h2 os Cons
              by force
          qed
        next
          case False
          then show ?thesis proof (cases "r ac")
            case None
            then have "otree_star q_0 (ac # list) = None"
              using Pair Node
              by auto
            then show ?thesis
              using a Cons
              by simp
          next
            case (Some c)
            then obtain tree outies where
              outies: "r ac = Some (tree,outies)"
              using Pair Node Cons a Some
              by fastforce
            then have h2: "otree_star (process_output_query q_0 (a # ip) (os # ops)) (ac # list) =
                (case otree_star tree list of
                  Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                  None \<Rightarrow> None)"
              using Some False Pair Node Cons a otree_star_output_query_different
              apply simp
              by (auto split: prod.splits option.splits)
            have h1: "otree_star q_0 (ac # list) = (case otree_star tree list of
                Some (n,opl) \<Rightarrow>
                Some (n,outies # opl) |
                None \<Rightarrow> None)"
              using outies Pair Node
              by auto
            have "otree_star q_0 (ac # list) \<noteq> None"
              using a Cons
              by blast
            then have "otree_star tree list \<noteq> None"
              using h1
              by (metis option.simps(4))
            then show ?thesis
              using h2 Cons a
              by (simp add: h1 os)
          qed
        qed
      qed
    qed
  qed
qed


lemma output_query_retains_some_output:
  assumes "length ip = length op" and
    "out_star q_0 acc \<noteq> None"
  shows "out_star (process_output_query q_0 ip op) acc \<noteq> None"
proof -
  obtain l r where
    lr: "q_0 = Node (l,r)"
    using obs_tree.exhaust
    by auto
  then have "otree_star q_0 acc \<noteq> None"
    using out_eq_otree[of l r acc] assms
    by auto
  then have ot: "otree_star (process_output_query q_0 ip op) acc \<noteq> None"
    using output_query_retains_some assms
    by blast
  obtain l2 r2 where
    "(process_output_query q_0 ip op) = Node (l2,r2)"
    using obs_tree.exhaust
    by auto
  then have "out_star (process_output_query q_0 ip op) acc \<noteq> None"
    using otree_eq_out[of l2 r2 acc] ot
    by auto
  then show ?thesis
    by simp
qed


lemma process_op_query_not_none_output:
  assumes "length ip = length op"
  shows "out_star (process_output_query (Node (acc,t)) ip op) ip \<noteq> None"
proof -
  have ot: "otree_star (process_output_query (Node (acc,t)) ip op) ip \<noteq> None"
    using output_query_retains_some assms process_op_query_not_none
    by blast
  obtain l2 r2 where
    "(process_output_query (Node (acc,t)) ip op) = Node (l2,r2)"
    using obs_tree.exhaust
    by auto
  then have "out_star (process_output_query (Node (acc,t)) ip op) ip \<noteq> None"
    using otree_eq_out[of l2 r2 acc] ot
    by (smt (verit) option.simps(4) out_eq_otree)
  then show ?thesis
    by simp
qed


lemma output_query_retains_some_specific:
  assumes "length ip = length op" and
    "otree_star (Node (l,r)) acc = Some (tr1,out1)" and
    "otree_star (process_output_query (Node (l,r)) ip op) acc = Some (tr2,out2)"
  shows "out1 = out2"
using assms proof (induction acc arbitrary: ip op l r tr1 tr2 out1 out2)
  case Nil
  then show ?case
    by simp
next
  case c: (Cons a acc)
  then show ?case proof (cases ip)
    case Nil
    then have "op = []"
      using c
      by simp
    then show ?thesis
      using Nil c
      by force
  next
    case (Cons i ilist)
    then obtain ops olist where
      op: "op = ops # olist"
      using c
      by (metis Suc_length_conv)
    obtain l2 r2 outs where
      ra: "r a = Some (Node (l2,r2),outs)"
      using c otree_split option.exhaust
      by (metis obs_tree.exhaust old.prod.exhaust)
    then show ?thesis proof (cases "i = a")
      case True
      then have "otree_star (process_output_query (Node (l,r)) ip op) (a # acc) =
          otree_star (process_output_query (Node (l,r)) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = otree_star (case r i of
          None \<Rightarrow> (Node (l,(\<lambda> j. if j = i
            then Some (process_output_query (Node (acc @ [i],(\<lambda> k. None))) ilist olist,ops)
            else r j))) |
          Some (tree,out) \<Rightarrow> (Node (l,(\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j)))) (a # acc)"
        using True ra
        by simp
      also have "\<dots> = otree_star (Node (l,(\<lambda> j. if j = i
          then Some ((process_output_query (Node (l2,r2)) ilist olist,outs))
          else r j))) (a # acc)"
        using ra
        by (simp add: True)
      also have "\<dots> = (case otree_star (process_output_query (Node (l2,r2)) ilist olist) acc of
          Some (node,output) \<Rightarrow> Some (node,outs # output) |
          None \<Rightarrow> None)"
        using ra True
        by auto
      finally have calc1: "otree_star (process_output_query (Node (l,r)) ip op) (a # acc) =
          (case otree_star (process_output_query (Node (l2,r2)) ilist olist) acc of
            Some (node,output) \<Rightarrow> Some (node,outs # output) |
            None \<Rightarrow> None)"
        by blast
      have "otree_star (process_output_query (Node (l2,r2)) ilist olist) acc \<noteq> None"
        using calc1 c Cons True
        by (metis not_Some_eq option.simps(4))
      then obtain node1 outputs1 where
        n1: "otree_star (process_output_query (Node (l2,r2)) ilist olist) acc = Some (node1,outputs1)"
        by fast
      have calc2: "otree_star (Node (l,r)) (a # acc) = (case otree_star (Node (l2,r2)) acc of
          Some (node,output) \<Rightarrow> Some (node,outs # output) |
          None \<Rightarrow> None)"
        using c ra True
        by simp
      then have "otree_star (Node (l2,r2)) acc \<noteq> None"
        using c
        by (metis not_Some_eq option.simps(4))
      then obtain node2 outputs2 where
        n2: "otree_star (Node (l2,r2)) acc = Some (node2,outputs2)"
        by auto
      have "outputs1 = outputs2"
        using c.IH n1 n2 c(2) op Cons append1_eq_conv length_Cons
        by fastforce
      then show ?thesis
        using calc1 calc2 Cons c True
        by (simp add: n1 n2)
    next
      case False
      then have "otree_star (process_output_query (Node (l,r)) ip op) (a # acc) =
          otree_star (process_output_query (Node (l,r)) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = otree_star (case r i of
          None \<Rightarrow> (Node (l,(\<lambda> j. if j = i
            then Some (process_output_query (Node (l @ [i],(\<lambda> k. None))) ilist olist,ops)
            else r j))) |
          Some (tree,out) \<Rightarrow> (Node (l,(\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j)))) (a # acc)"
        using False ra
        by simp
      also have "\<dots> = (case otree_star (Node (l2,r2)) acc of
          Some (node,output) \<Rightarrow> Some (node,outs # output) |
          None \<Rightarrow> None)"
        using ra
        apply (cases "r i")
        using False
        by auto
      also have "\<dots> = otree_star (Node (l,r)) (a # acc)"
        using ra
        by simp
      finally show ?thesis
        using c Cons
        by force
    qed
  qed
qed


lemma output_query_retains_some_specific_output:
  assumes "length ip = length op" and
    "out_star (Node (l,r)) acc = Some (out1)"
  shows "Some out1 = out_star (process_output_query (Node (l,r)) ip op) acc"
using assms proof (induction acc arbitrary: ip op l r out1)
  case Nil
  then show ?case
    by simp
next
  case c: (Cons a acc)
  then show ?case proof (cases ip)
    case Nil
    then have "op = []"
      using c
      by simp
    then show ?thesis
      using Nil c
      by force
  next
    case (Cons i ilist)
    then obtain ops olist where
      op: "op = ops # olist"
      using c
      by (metis Suc_length_conv)
    obtain l2 r2 outs where
      ra: "r a = Some (Node (l2,r2),outs)"
      using c out_split option.exhaust
      by (metis obs_tree.exhaust old.prod.exhaust)
    then show ?thesis proof (cases "i = a")
      case True

      then have "out_star (process_output_query (Node (l,r)) ip op) (a # acc) =
          out_star (process_output_query (Node (l,r)) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = out_star (case r i of
          None \<Rightarrow> (Node (l,(\<lambda> j. if j = i
            then Some ((process_output_query (Node (acc @ [i],(\<lambda> k. None))) ilist olist),ops)
            else r j))) |
          Some (tree,out) \<Rightarrow> (Node (l,(\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j)))) (a # acc)"
        using True ra
        by simp
      also have "\<dots> = out_star (Node (l,(\<lambda> j. if j = i
          then Some ((process_output_query (Node (l2,r2)) ilist olist,outs))
          else r j))) (a # acc)"
        using ra
        by (simp add: True)
      also have "\<dots> = (case out_star (process_output_query (Node (l2,r2)) ilist olist) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using ra True
        by auto
      finally have calc1: "out_star (process_output_query (Node (l,r)) ip op) (a # acc) =
          (case out_star (process_output_query (Node (l2,r2)) ilist olist) acc of
            Some output \<Rightarrow> Some (outs # output) |
            None \<Rightarrow> None)"
        by blast
      have "out_star (process_output_query (Node (l2,r2)) ilist olist) acc \<noteq> None"
        using calc1 c(3) Cons True output_query_retains_some_output
        by (metis c.prems(1) option.discI option.simps(4))
      then obtain outputs1 where
        n1: "out_star (process_output_query (Node (l2,r2)) ilist olist) acc = Some (outputs1)"
        by fast
      have calc2: "out_star (Node (l,r)) (a # acc) = (case out_star (Node (l2,r2)) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using c ra True
        by simp
      then have "out_star (Node (l2,r2)) acc \<noteq> None"
        using c
        by (metis not_Some_eq option.simps(4))
      then obtain outputs2 where
        n2: "out_star (Node (l2,r2)) acc = Some (outputs2)"
        by auto
      have "outputs1 = outputs2"
        using c.IH n1 n2 c(2) op Cons append1_eq_conv length_Cons
        by fastforce
      then show ?thesis
        using calc1 calc2 Cons c True
        by (simp add: n1 n2)
    next
      case False
      then have "out_star (process_output_query (Node (l,r)) ip op) (a # acc) =
          out_star (process_output_query (Node (l,r)) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = out_star (case r i of
            None \<Rightarrow> (Node (l,(\<lambda> j. if j = i
              then Some (process_output_query (Node (l @ [i],(\<lambda> k. None))) ilist olist,ops)
              else r j))) |
            Some (tree,out) \<Rightarrow> (Node (l,(\<lambda> j. if j = i
              then Some ((process_output_query tree ilist olist),out)
              else r j))))
          (a # acc)"
        using False ra
        by simp
      also have "\<dots> = (case out_star (Node (l2,r2)) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using ra
        apply (cases "r i")
        using False
        by auto
      also have "\<dots> = out_star (Node (l,r)) (a # acc)"
        using ra
        by simp
      finally show ?thesis
        using c Cons
        by force
    qed
  qed
qed


lemma op_query_output_not_equal:
  assumes "i \<noteq> j"
  shows "out_star (process_output_query (Node (acc,t)) (i # is) (op # ops)) (j # js) = out_star (Node (acc,t)) (j # js)"
proof -
  have "(process_output_query (Node (acc,t)) (i # is) (op # ops)) = (case t i of
      None \<Rightarrow> (Node (acc,(\<lambda> j. if j = i
        then Some (process_output_query (Node (acc @ [i],(\<lambda> k. None))) is ops,op)
        else t j))) |
      Some (tree,out) \<Rightarrow> (Node (acc,(\<lambda> j. if j = i
        then Some ((process_output_query tree is ops),out)
        else t j))))"
    by simp
  then show ?thesis proof (cases "t i")
    case None
    then have eq: "(process_output_query (Node (acc,t)) (i # is) (op # ops)) =
        (Node (acc,(\<lambda> j. if j = i
          then Some (process_output_query (Node (acc @ [i],(\<lambda> k. None))) is ops,op)
          else t j)))"
      by simp
    have "out_star (Node (acc,(\<lambda> j. if j = i
          then Some (process_output_query (Node (acc @ [i],(\<lambda> k. None))) is ops,op)
          else t j))) (j # js) =
        out_star (Node (acc,t)) (j # js)"
      using assms
      by auto
    then show ?thesis
      using eq
      by argo
  next
    case (Some a)
    obtain tree out where
      "a = (tree,out)"
      by fastforce
    then have eq: "(process_output_query (Node (acc,t)) (i # is) (op # ops)) =
        (Node (acc,(\<lambda> j. if j = i
          then Some ((process_output_query tree is ops),out)
          else t j)))"
      using Some
      by fastforce
    have "out_star (Node (acc,(\<lambda> j. if j = i
          then Some ((process_output_query tree is ops),out)
          else t j))) (j # js) =
        out_star (Node (acc,t)) (j # js)"
      using assms
      by auto
    then show ?thesis
      using eq
      by argo
  qed
qed


lemma substring_different_query:
  assumes "(out_star T i = None)" and
    "length j = length out" and
    "out_star (process_output_query T j out) i \<noteq> None"
  shows "\<exists> y. j = i @ y"
using assms proof (induction i arbitrary: out j T)
  case Nil
  then show ?case
    by blast
next
  case (Cons a i)
  obtain acc t where
    node: "T = Node (acc,t)"
    using obs_tree.exhaust
    by auto
  have lenj: "length j = length out"
    using Cons output_query_length
    by blast

  then show ?case proof (cases "j = []")
    case True
    then show ?thesis
      using Cons lenj
      by auto
  next
    case False
    then obtain jfront js where
      j: "j = jfront # js"
      using list.exhaust
      by auto
    then obtain op os where
      out: "out = op # os"
      using list.exhaust lenj
      by (metis False length_greater_0_conv)
    have induc_two: "length js = length os"
      using lenj j out
      by auto
    then show ?thesis proof (cases "jfront = a")
      case eq: True
      then show ?thesis proof (cases "t jfront")
        case None

        have proc: "(process_output_query T (jfront # js) (op # os)) =
            (Node (acc,(\<lambda> j. if j = jfront
              then Some (process_output_query (Node (acc @ [jfront],(\<lambda> k. None))) js os,op)
              else t j)))"
          using node None
          by auto
        then have "out_star (process_output_query T (jfront # js) (op # os)) (a # i) =
            out_star (Node (acc,(\<lambda> j. if j = jfront
              then Some (process_output_query (Node (acc @ [jfront],(\<lambda> k. None))) js os,op)
              else t j))) (a # i)"
          by force
        also have b: "\<dots> = (case (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (acc @ [jfront],(\<lambda> k. None))) js os,op)
              else t j) a of
            Some (n,op) \<Rightarrow>
            (case (out_star n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None)"
          by auto
        also have c: "\<dots> =
            (case (out_star (process_output_query (Node (acc @ [jfront],(\<lambda> k. None))) js os) i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None)"
          using eq
          by auto

        have induc_three: "(out_star (process_output_query (Node (acc @ [jfront],(\<lambda> k. None))) js os) i) \<noteq> None"
          using calculation Cons proc
          by (metis c j option.simps(4) out)
        then show ?thesis proof (cases "i = []")
          case True
          then show ?thesis
            by (simp add: eq j)
        next
          case False
          obtain ifront "is" where
            "i = ifront # is"
            using False list.exhaust
            by auto
          then have "(out_star (Node (acc @ [jfront],(\<lambda> k. None))) i) = (case (\<lambda> k. None) ifront of
              Some (n,op) \<Rightarrow>
              (case (out_star n is) of
                Some ops \<Rightarrow> Some (op # ops) |
                None \<Rightarrow> None) |
              None \<Rightarrow> None)"
            by simp
          then have induc_one: "(out_star (Node (acc @ [jfront],(\<lambda> k. None))) i) = None"
            by auto
          show ?thesis
            using Cons.IH[of "(Node (acc @ [jfront],(\<lambda> k. None)))" js os]
            using induc_one induc_two induc_three eq j
            by auto
        qed
      next
        case (Some b)
        obtain atree aout where
          atree: "b = (atree,aout)"
          by (metis surj_pair)
        then have proc: "(process_output_query T (jfront # js) (op # os)) =
            Node (acc,(\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j))"
          using node Some
          by auto
        then have "out_star (process_output_query T (jfront # js) (op # os)) (a # i) =
            out_star (Node (acc,(\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j))) (a # i)"
          by argo
        also have "\<dots> = (case (\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j) a of
            Some (n,op) \<Rightarrow>
            (case (out_star n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None)"
          by simp
        also have c: "\<dots> =
            (case (out_star (process_output_query atree js os) i) of
              Some ops \<Rightarrow> Some (aout # ops) |
              None \<Rightarrow> None)"
          using eq
          by auto
        finally have induc_three: "out_star (process_output_query atree js os) i \<noteq> None"
          using Cons
          by (metis j option.simps(4) out)
        have "(case t a of
            Some (n,op) \<Rightarrow> (case (out_star n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None) = None"
          using Cons node
          by auto
        then have "(case (out_star atree i) of
            Some ops \<Rightarrow> Some (aout # ops) |
            None \<Rightarrow> None) = None"
          using Some atree eq
          by auto
        then have induc_one: "out_star atree i = None"
          using not_None_eq
          by fastforce
        then show ?thesis
          using induc_one induc_two induc_three Cons j
          by (simp add: eq)
      qed
    next
      case False
      then show ?thesis
        using op_query_output_not_equal j node out Cons
        by metis
    qed
  qed
qed


lemma output_query_keeps_invar_aux:
  assumes "(out_star T i = None)" and
    "trans_star_output t q_0 j = out" and
    "T' = process_output_query T j out" and
    "\<forall> k y. out_star T k = Some y \<longrightarrow> trans_star_output t q_0 k = y"
  shows "(out_star T' i \<noteq> None \<longrightarrow> out_star T' i = Some (trans_star_output t q_0 i))"
proof (cases "out_star T' i = None")
  case True
  then show ?thesis
    by blast
next
  case False
  have lenj: "length j = length out"
    using assms(2) trans_star_length trans_star_output_state
    by fast
  then have subs: "\<exists> y. j = i @ y"
    using substring_different_query False assms
    by blast
  then show ?thesis using assms lenj proof (induction i arbitrary: q_0 j out T T')
    case Nil
    then show ?case
      by simp
  next
    case (Cons a i)
    obtain acc f where
      T: "T = Node (acc,f)"
      using obs_tree.exhaust
      by auto
    obtain acc' f' where
      T': "T' = Node (acc',f')"
      using obs_tree.exhaust
      by auto
    obtain b js where
      j: "j = b # js"
      using Cons
      by auto
    obtain op os where
      out: "out = op # os"
      using Cons
      by (metis j length_Suc_conv)
    obtain q' out' where
      q': "t (q_0,a) = (q',out')"
      by fastforce
    have eq: "b = a"
      using subs j Cons
      by auto

    have ih_prem1: "\<exists> y. js = i @ y"
      using Cons.prems(1) j
      by auto
    have ih_prem3: "trans_star_output t q' js = os"
      using Cons.prems(3) eq j out q'
      by auto
    have ih_prem5: "length js = length os"
      using Cons.prems(6) j out
      by auto

    show ?case proof (cases "f a")
      case None
      have query: "process_output_query (Node (acc,f)) (b # js) (op # os) = (Node (acc,(\<lambda> k. if k = b
          then Some (process_output_query (Node (acc @ [b],(\<lambda> k. None))) js os,op)
          else f k)))"
        using Cons None eq
        by auto
      have "out_star T' (a # i) = out_star (process_output_query (Node (acc,f)) (b # js) (op # os)) (a # i)"
        using Cons j out T
        by argo
      also have "\<dots> = out_star (Node (acc,(\<lambda> k. if k = b
          then Some (process_output_query (Node (acc @ [b],(\<lambda> k. None))) js os,op)
          else f k))) (a # i)"
        using query
        by argo
      also have "\<dots> = (case (\<lambda> k. if k = b
            then Some (process_output_query (Node (acc @ [b],(\<lambda> k. None))) js os,op)
            else f k) a of
          Some (n,op) \<Rightarrow>
          (case (out_star n i) of
            Some ops \<Rightarrow> Some (op # ops) |
            None \<Rightarrow> None) |
          None \<Rightarrow> None)"
        by simp
      also have "\<dots> = (case (out_star (process_output_query (Node (acc @ [b],(\<lambda> k. None))) js os) i) of
          Some ops \<Rightarrow> Some (op # ops) |
          None \<Rightarrow> None)"
        by (simp add: eq)

      then show ?thesis proof (cases "i")
        case Nil
        then show ?thesis
          using Cons.prems(3) Cons.prems(4) T q' eq j out query
          by auto
      next
        case (Cons c list)
        have ih_prem2: "out_star (Node (acc @ [b],\<lambda> k. None)) i = None"
          using Cons
          by fastforce
        obtain T'' where
          T'': "T'' = process_output_query (Node (acc @ [b],\<lambda> k. None)) js os"
          by simp
        have ih_prem4: "\<forall> k y. out_star (Node (acc @ [b],\<lambda> k. None)) k = Some y \<longrightarrow> trans_star_output t q' k = y"
          by (metis Cons.prems(5) eq list.exhaust out_split out_star.simps(1) trans_star_output.simps(1))
        have "(out_star T'' i) \<noteq> None \<longrightarrow>
            (out_star T'' i) = Some (trans_star_output t q' i)"
          using Cons.IH[of js "(Node (acc @ [b],(\<lambda> k. None)))" q' os T''] ih_prem1 ih_prem2 ih_prem3
          using ih_prem4 T'' ih_prem5
          by blast
        then have "(out_star (process_output_query (Node (acc @ [b],\<lambda> k. None)) js os) i) \<noteq> None \<longrightarrow>
            (out_star (process_output_query (Node (acc @ [b],\<lambda> k. None)) js os) i) = Some (trans_star_output t q' i)"
          using T''
          by blast
        then show ?thesis
          using Cons.prems(3) calculation eq j out q'
          by auto
      qed
    next
      case (Some c)
      obtain nextnode nextout where
        nextnode: "c = (nextnode,nextout)"
        by fastforce
      have query: "process_output_query (Node (acc,f)) (b # js) (op # os) =
          (Node (acc,(\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j)))"
        using eq nextnode Some
        by auto
      then have a: "out_star (process_output_query (Node (acc,f)) (b # js) (op # os)) (a # i) =
          out_star (Node (acc,(\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j))) (a # i)"
        by presburger
      also have b: "\<dots> = (case (\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j) a of
          Some (n,op) \<Rightarrow> (case (out_star n i) of
            Some ops \<Rightarrow> Some (op # ops) |
            None \<Rightarrow> None) |
          None \<Rightarrow> None)"
        by simp
      also have c: "\<dots> = (case (out_star (process_output_query nextnode js os) i) of
          Some ops \<Rightarrow> Some (nextout # ops) |
          None \<Rightarrow> None)"
        by (simp add: eq)
      have "out_star T (a # i) = (case (out_star nextnode i) of
          Some ops \<Rightarrow> Some (nextout # ops) |
          None \<Rightarrow> None)"
        using T nextnode Some
        by auto
      then have ih_prem2: "out_star nextnode i = None"
        using Cons
        by (metis not_None_eq option.simps(5))
      obtain T'' where
        T'': "T'' = process_output_query nextnode js os"
        by simp
      have alt_nextout: "out_star T [a] = Some [nextout]"
        using Some nextnode T
        by simp
      have alt_out': "trans_star_output t q_0 [a] = [out']"
        using q'
        by simp
      have "out_star T [a] \<noteq> None \<longrightarrow> Some (trans_star_output t q_0 [a]) = out_star T [a]"
        using Cons
        by fastforce
      then have nextout_eq_out': "nextout = out'"
        using alt_out' alt_nextout
        by simp
      have part: "\<forall> k. out_star T (a # k) =
          (case (out_star nextnode k) of
            Some ops \<Rightarrow> Some (nextout # ops) |
            None \<Rightarrow> None)"
        using T Some nextnode
        by auto
      have part2: "\<forall> k. trans_star_output t q_0 (a # k) = out' # trans_star_output t q' k"
        using q'
        by simp
      have "\<forall> k y. out_star T (a # k) = Some (out' # y) \<longrightarrow> trans_star_output t q_0 (a # k) = (out' # y)"
        using Cons
        by fastforce
      then have ih_prem4: "\<forall> k y. out_star nextnode k = Some y \<longrightarrow> trans_star_output t q' k = y"
        using part q' part2 nextout_eq_out'
        by auto

      have "(out_star (process_output_query nextnode js os) i) \<noteq> None \<longrightarrow>
          out_star (process_output_query nextnode js os) i = Some (trans_star_output t q' i)"
        using Cons.IH[of js nextnode q' os "(process_output_query nextnode js os)"]
      ih_prem1 ih_prem2 ih_prem3 ih_prem4 ih_prem5 T'' nextnode Some
        by argo
      then show ?thesis
        using Cons.prems(4) T c calculation j nextout_eq_out' option.simps(4) out part2
        by auto
    qed
  qed
qed


lemma output_query_keeps_invar:
  assumes "(out_star T i = None)" and
    "output_query m j = out" and
    "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
  shows "(out_star (process_output_query T j out) i \<noteq> None \<longrightarrow> out_star (process_output_query T j out) i = Some (output_query m i))"
proof -
  obtain t q_0 where
    "m = (q_0,t)"
    by fastforce
  then have "\<forall> is. output_query m is = trans_star_output t q_0 is"
    by simp
  then show ?thesis
    by (metis (mono_tags,lifting) assms output_query_keeps_invar_aux)
qed


lemma proc_output_query_retains_apart:
  assumes "length ip = length op" and
    "apart_text T s1 s2"
  shows "apart_text (process_output_query T ip op) s1 s2"
    using output_query_retains_some_specific_output assms
    by (smt (verit,ccfv_SIG) apart_text.simps length_0_conv process_output_query.elims process_output_query.simps(1))


lemma proc_output_query_retains_sapart:
  assumes "length ip = length op" and
    "sapart (S,F,T)"
  shows "sapart (S,F,(process_output_query T ip op))"
    using proc_output_query_retains_apart assms
    by (metis sapart.simps)


section "norm"


lemma norm_max:
  assumes "invar m (S,F,T)" and
    "finite S"
  shows "norm_set (S,F,T) \<le>
      (card S * (card S + 1)) div 2 + (card S * card I) + (card S * (card S * card I))"
proof -
  have fst: "norm_fst (S,F,T) = (card S * (card S + 1) div 2)"
    by simp
  have fin_snd: "finite (S \<times> I)"
    using assms
    by auto
  have "{(q,i). q \<in> S \<and> out_star T (q @ [i]) \<noteq> None} \<subseteq> (S \<times> I)"
    using univI
    by blast
  then have "norm_snd (S,F,T) \<le> (card (S \<times> I))"
    using fin_snd card_mono
    by auto
  then have snd: "norm_snd (S,F,T) \<le> card S * card I"
    by (simp add: card_cartesian_product)
  have fin_trd: "finite ((\<lambda> (s,i). s @ [i]) ` (S \<times> I))"
    using fin_snd univI
    by blast
  have "(\<forall> f \<in> F. \<exists> s \<in> S. \<exists> i. f = s @ [i])"
    using assms
    by auto
  then have pre: "F \<subseteq> {s @ [i] |
      s i. s \<in> S \<and> i \<in> I}"
    using assms univI
    by blast
  have f_image: "{s @ [i] |
      s i. s \<in> S \<and> i \<in> I} = (\<lambda> (s,i). s @ [i]) ` (S \<times> I)"
    by fast
  then have card_pre: "card F \<le> card ((\<lambda> (s,i). s @ [i]) ` (S \<times> I))"
    using fin_trd pre card_mono
    by fastforce
  have "inj_on (\<lambda> (s,i). s @ [i]) (S \<times> I)"
    unfolding inj_on_def
    by (auto split: prod.splits)
  then have "card ((\<lambda> (s,i). s @ [i]) ` (S \<times> I)) = card (S \<times> I)"
    using card_image
    by blast
  then have card_f_less_cross: "card F \<le> card (S \<times> I)"
    using card_pre
    by argo
  have subs_trd: "{(q,p). q \<in> S \<and> p \<in> F \<and> apart_text T q p} \<subseteq> (S \<times> F)"
    by blast
  have "finite (S \<times> F)"
    using assms f_image finite_subset pre
    by fastforce
  then have "norm_trd (S,F,T) \<le> card (S \<times> F)"
    using subs_trd card_mono
    by fastforce
  then have trd: "norm_trd (S,F,T) \<le> (card S * (card S * card I))"
    by (metis (full_types) card_cartesian_product card_f_less_cross dual_order.trans mult_le_mono2)
  then show ?thesis
    using fst snd trd
    by force
qed


lemma func_sim_of_output_query:
  assumes "\<forall> inp x. out_star T inp = Some x \<longrightarrow> output_query m inp = x"
  shows "\<exists> f. func_sim m T f"
proof -
  obtain q_0 transmealy where
    m: "m = (q_0,transmealy)"
    by fastforce
  have "\<exists> f. \<forall> i. f i = fst (trans_star transmealy q_0 i)"
    by auto
  then obtain f where
    f: "\<forall> i. f i = fst (trans_star transmealy q_0 i)"
    by auto
  then have one: "f [] = q_0"
    by auto
  have b: "\<forall> inp out. out_star T inp = Some out \<longrightarrow> out = snd (trans_star transmealy q_0 inp)"
    using assms m
    by (simp add: trans_star_output_state)
  have c: "(\<forall> acc is ops.
      trans_star transmealy (fst (trans_star transmealy q_0 acc)) is =
      (fst (trans_star transmealy q_0 (acc @ is)),drop (length acc) (snd (trans_star transmealy q_0 (acc @ is)))))"
    using trans_star_two_nested
    by fast
  then have "(\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow> ops = output_query m (acc @ is))"
    using assms
    by simp
  then have "(\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow> trans_star transmealy (f acc) is =
        (f (acc @ is),(drop (length acc) ops))) =
      (\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow> ops = output_query m (acc @ is) \<longrightarrow>
        trans_star transmealy (f acc) is = (f (acc @ is),(drop (length acc) ops)))"
    by presburger
  also have "\<dots> = (\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow> ops = output_query m (acc @ is) \<longrightarrow>
      trans_star transmealy (fst (trans_star transmealy q_0 acc)) is =
      (fst (trans_star transmealy q_0 (acc @ is)),(drop (length acc) ops)))"
    using f
    by presburger
  also have "\<dots> = (\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow> ops =
      snd (trans_star transmealy q_0 (acc @ is)) \<longrightarrow>
      trans_star transmealy (fst (trans_star transmealy q_0 acc)) is =
      (fst (trans_star transmealy q_0 (acc @ is)),(drop (length acc) (snd (trans_star transmealy q_0 (acc @ is))))))"
    using b
    by (simp add: trans_star_two_nested)
  finally have calc: "(\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow>
      trans_star transmealy (f acc) is = (f (acc @ is),(drop (length acc) ops)))"
    using c
    by presburger
  have "func_sim m T f"
    unfolding func_sim_def
    apply (simp add: one m)
    using calc
    by auto
  then show ?thesis
    by auto
qed


lemma max_size_S_aux:
  assumes "func_sim m T f" and
    "sapart (S,F,T)" and
    "finite S"
  shows "card S \<le> card (UNIV :: 'state set)"
proof (rule ccontr)
  assume ass: "\<not> card S \<le> card (UNIV :: 'state set)"
  then have gt: "card S > card (UNIV :: 'state set)"
    by simp
  obtain c where
    c: "card (UNIV :: 'state set) = c"
    by simp
  have "\<forall> s \<in> S. f s \<in> (UNIV :: 'state set)"
    by simp
  have "card S \<ge> card (image f S)"
    using assms
    by (simp add: card_image_le)
  have "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart_text T s1 s2"
    using assms
    by simp
  then have "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> (f s1) \<noteq> (f s2)"
    by (metis apart_sim assms(1) old.prod.exhaust)
  then have "inj f"
    by (meson ass assms(3) finite_UNIV inj_on_def inj_on_iff_card_le top_greatest)
  then have "card S = card (image f S)"
    by (simp add: card_image subset_inj_on)
  then show False
    by (metis ass card_mono finite_UNIV top_greatest)
qed


lemma max_size_S:
  assumes "invar (m :: (('state,'input,'output) mealy)) (S,F,T)"
  shows "card S \<le> card (UNIV :: 'state set)"
proof -
  have "\<exists> f. func_sim m T f"
    using assms
    by (metis func_sim_of_output_query invar.simps not_Some_eq option.sel)
  then obtain f where
    a: "func_sim m T f"
    by auto
  have b: "sapart (S,F,T)"
    using assms
    by auto
  have c: "finite S"
    using assms
    by force
  then show ?thesis
    using max_size_S_aux a b c
    by blast
qed


section "algo_step"


lemma algo_step_keeps_invar:
  assumes "algo_step m ((S :: 'input list set),F,T) (S',F',T')" and
    "invar m (S,F,T)"
  shows "invar m (S',F',T')"
using assms proof (induction rule: algo_step.induct)
  case (rule1 f F S T m)
  then show ?case
    by fastforce
next
  case (rule2 s S T i mnew out F)
  have mnew: "m = mnew"
    by (metis mdef output_query.elims)
  have lens: "length (s @ [i]) = length out"
    using rule2 output_query_length
    by (metis case_prodE case_prodI2 mdef)
  have "\<forall> e. (e \<in> S \<or> e \<in> F \<longrightarrow> out_star T e \<noteq> None)"
    using rule2
    by auto
  then have a: "\<forall> e. (e \<in> S \<or> e \<in> F \<union> {s @ [i]} \<longrightarrow> out_star (process_output_query T (s @ [i]) out) e \<noteq> None)"
    using lens out_star.elims output_query_retains_some_output process_op_query_not_none_output
    by (metis Un_empty_right Un_insert_right insert_iff not_Cons_self2)
  have b: "sapart (S,F,process_output_query T (s @ [i]) out)"
    using lens rule2 proc_output_query_retains_sapart invar.simps
    by blast
  have "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
    using rule2 mnew
    by force
  then have c: "(\<forall> j. out_star (process_output_query T (s @ [i]) out) j \<noteq> None \<longrightarrow>
      out_star (process_output_query T (s @ [i]) out) j = Some (output_query m j))"
    using rule2 output_query_keeps_invar[of T "s @ [i]" "s @ [i]" out] mnew
    by (smt (verit) invar.simps lens out_star.elims output_query_keeps_invar output_query_retains_some_specific_output)
  show ?case
    using rule2 a b c mnew
    by auto
  text \<open>this is very slow, manual proving of the s@[i] rule should improve performance\<close>
next
  case (rule3 s1 S s2 f F T w mnew out)
  have mnew: "m = mnew"
    by (metis mdef output_query.elims)
  have lens: "length (f @ w) = length out"
    using rule3 output_query_length mnew
    by blast
  have b: "sapart (S,F,process_output_query T (f @ w) out)"
    using lens rule3 proc_output_query_retains_sapart invar.simps
    by blast
  have "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
    using rule3 mnew
    by fastforce
  then have c: "(\<forall> j. out_star (process_output_query T (f @ w) out) j \<noteq> None \<longrightarrow>
      out_star (process_output_query T (f @ w) out) j = Some (output_query m j))"
    using rule3 output_query_keeps_invar mnew
    by (smt (verit,del_insts) invar.simps lens out_star.elims output_query_retains_some_specific_output)
  then show ?case
    using rule3 b c mnew
    by (smt (verit,del_insts) invar.simps lens output_query_retains_some_output)
next
  case (rule4 T S s fs F f q_0 inp outs outf)
  have mdef2: "m = (q_0,f)"
    by (simp add: mdef)
  have lens: "length (s @ inp) = length outs"
    using rule4 output_query_length mdef2
    by blast
  have lenf: "length (fs @ inp) = length outf"
    using rule4 output_query_length mdef2
    by blast
  have b: "sapart (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf))"
    using lens lenf rule4 proc_output_query_retains_sapart invar.simps
    by metis
  have "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query (q_0,f) k = y"
    using rule4
    by auto
  then have "(\<forall> j. out_star (process_output_query T (s @ inp) outs) j \<noteq> None \<longrightarrow>
      out_star (process_output_query T (s @ inp) outs) j = Some (output_query (q_0,f) j))"
    using rule4 output_query_keeps_invar mdef2
    by (smt (verit,del_insts) invar.simps lens out_star.elims output_query_retains_some_specific_output)
  then have c: "(\<forall> j. out_star (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) j \<noteq> None \<longrightarrow>
      out_star (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) j = Some (output_query (q_0,f) j))"
    using rule4 output_query_keeps_invar[of "process_output_query T (s @ inp) outs" _"fs @ inp" "outf"]
    using mdef2
    by (smt (verit) lenf option.discI option.inject out_star.elims output_query_retains_some_specific_output process_output_query.simps(1))
  then show ?case
    using rule4 c b
    by (smt (verit,del_insts) invar.simps lenf lens output_query_retains_some_output)
qed


theorem algo_step_increases_norm:
  assumes "algo_step m ((S :: 'input list set),F,T) (S',F',T')" and
    "invar m (S,F,T)"
  shows "norm_set (S,F,T) < norm_set (S',F',T')"
using assms proof (induction m "(S,F,T)" "(S',F',T')" rule: algo_step.induct)
  case (rule1 f m)
  have finS: "finite S"
    using rule1(6)
    by simp
  have finI: "finite I"
    by fastforce
  have finF: "finite F"
    using rule1(6)
    by simp
  have "norm_fst (S,F,T) \<le> norm_fst (S \<union> {f},F - {f},T)"
    by (simp add: add_mono card_insert_le div_le_mono mult_le_mono)
  have "f \<notin> S"
    using rule1
    by auto
  then have "norm_fst (S,F,T) + (card S + 1) \<le> norm_fst (S \<union> {f},F - {f},T)"
    using finS
    by auto
  then have fst: "norm_fst (S,F,T) + (card S + 1) \<le> norm_fst (S',F',T')"
    using rule1
    by fast

  have finp: "finite ({q. q \<in> S \<union> {f}} \<times> {i. i \<in> I})"
    using finS finI
    by simp
  have "{(q,i). q \<in> S \<union> {f} \<and> i \<in> I} = {q. q \<in> S \<union> {f}} \<times> {i. i \<in> I}"
    using finS finI
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<union> {f} \<and> i \<in> I}"
    using finp
    by argo
  have "{(q,i). (q = f \<or> q \<in> S) \<and> (\<exists> a b. out_star T (q @ [i]) = Some b)} \<subseteq>
      {(q,i). q \<in> S \<union> {f} \<and> i \<in> I}"
    using univI
    by auto
  then have fin2: "finite {(q,i). (q = f \<or> q \<in> S) \<and> (\<exists> a b. out_star T (q @ [i]) = Some b)}"
    using finp2 finite_subset
    by fast
  have "{(q,i). q \<in> S \<and> (\<exists> b. out_star T (q @ [i]) = Some b)} \<subseteq>
      {(q,i). (q = f \<or> q \<in> S) \<and> (\<exists> b. out_star T (q @ [i]) = Some b)}"
    by blast
  then have "norm_snd (S,F,T) \<le> norm_snd (S \<union> {f},F - {f},T)"
    using fin2 card_mono
    by fastforce
  then have snd: "norm_snd (S,F,T) \<le> norm_snd (S',F',T')"
    using rule1
    by fast

  have finSF: "finite {(q,p). (q \<in> S \<or> q = f) \<and> p \<in> F}"
    using finS finF
    by simp
  have "{(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<subseteq>
      {(q,p). (q \<in> S \<or> q = f) \<and> p \<in> F}"
    by blast
  then have fin3: "finite {(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and>
      (\<exists> i x. (out_star T (q @ i) = Some x) \<and> (\<exists> y. out_star T (p @ i) = Some y \<and>
        drop (length q) x \<noteq> drop (length p) y))}"
    using finSF finite_subset
    by fast
  have "{(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> (\<exists> i x. (out_star T (q @ i) = Some x)
        \<and> (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<supseteq>
      {(q,p). (q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    by blast
  also have c1: "\<dots> \<supseteq> {(q,p). (q \<in> S) \<and> p \<in> F \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
      (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} - {(p,q). p \<in> S \<and> q = f}"
    by auto
  have "finite {(p,q). p \<in> S \<and> q = f}"
    using rule1
    by simp
  then have le1: "card {(q,p). (q \<in> S) \<and> p \<in> F \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} - card {(p,q). p \<in> S \<and> q = f}
      \<le> card ({(q,p). (q \<in> S) \<and> p \<in> F \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
          (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} - {(p,q). p \<in> S \<and> q = f})"
    using diff_card_le_card_Diff
    by blast
  have le2: "card ({(q,p). (q \<in> S) \<and> p \<in> F \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} - {(p,q). p \<in> S \<and> q = f}) \<le>
      card ({(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))})"
    using calculation fin3 card_mono c1
    by meson
  have "norm_trd (S \<union> {f},F - {f},T) \<ge> card {(q,p). (q \<in> S) \<and> p \<in> F \<and>
      (\<exists> i x. (out_star T (q @ i) = Some x) \<and> (\<exists> y. out_star T (p @ i) = Some y \<and>
        drop (length q) x \<noteq> drop (length p) y))} - card {(p,q). p \<in> S \<and> q = f}"
    using le1 le2
    by simp
  then have "norm_trd (S \<union> {f},F - {f},T) \<ge> norm_trd (S,F,T) - card {(p,q). p \<in> S \<and> q = f}"
    by simp
  then have "norm_trd (S \<union> {f},F - {f},T) \<ge> norm_trd (S,F,T) - card S"
    using rule1
    by fastforce
  then have trd: "norm_trd (S,F,T) - card S \<le> norm_trd (S',F',T')"
    using rule1
    by fast

  then show ?case
    using fst snd trd
    by simp
next
  case (rule2 s i mnew out)
  have mnew: "m = mnew"
    by (metis mdef old.prod.exhaust)
  have finS: "finite S"
    using rule2
    by simp
  have finS': "finite S'"
    using rule2
    by simp
  have finI: "finite I"
    by fastforce
  have finF: "finite F"
    using rule2
    by simp
  then have finF': "finite F'"
    using rule2
    by blast
  have fst: "norm_fst (S,F,T) = norm_fst (S',F',T')"
    using rule2
    by fastforce

  have lens: "length (s @ [i]) = length out"
    using output_query_length rule2.hyps(3) mnew
    by blast
  then have a: "out_star T' (s @ [i]) \<noteq> None"
    using process_op_query_not_none_output rule2
    by (metis obs_tree.exhaust old.prod.exhaust)
  have retain: "\<forall> is. out_star T is \<noteq> None \<longrightarrow> out_star T' is \<noteq> None"
    using rule2 lens output_query_retains_some_output
    by blast
  have "{q \<in> S. \<forall> i. \<exists> a b. q \<noteq> s \<and> otree_star T' (q @ [i]) = Some (a,b)} \<subseteq> S"
    by force
  have finp: "finite ({q. q \<in> S} \<times> {i. i \<in> I})"
    using finS finI
    by simp
  have "{(q,i). q \<in> S \<and> i \<in> I} = {q. q \<in> S} \<times> {i. i \<in> I}"
    using finS finI
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp
    by argo
  have "{(q,i'). \<not> (q = s \<and> i' = i) \<and> (q \<in> S) \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)} \<subseteq>
      {(q,i). q \<in> S \<and> i \<in> I}"
    using univI
    by auto
  then have fin2: "finite {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}"
    using finp2 finite_subset
    by fast
  have "{(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T (q @ [i']) = Some b)} \<subseteq>
      {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}"
    using retain
    by auto
  then have lep: "card {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T (q @ [i']) = Some b)} \<le>
      card {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}"
    using card_mono fin2
    by fastforce
  have "{(q,i'). q = s \<and> i' = i \<and> (\<exists> b. out_star T (q @ [i']) = Some b)} = {}"
    using rule2
    by fastforce
  then have same: "{(q,i). q \<in> S \<and> (\<exists> b. out_star T (q @ [i]) = Some b)} =
      {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T (q @ [i']) = Some b)}"
    by auto
  have nin: "(s,i) \<notin> {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}"
    by blast
  have "{(q,i'). (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)} = {(s,i)}"
    using a rule2
    by fast
  then have union: "{(q,i'). q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)} =
      {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)} \<union> {(s,i)}"
    by force
  then have gt: "card ({(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)} \<union> {(s,i)}) =
      card ({(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}) + 1"
    using fin2 nin
    by simp
  have "card {(q,i'). q \<in> S \<and> (\<exists> b. out_star T (q @ [i']) = Some b)} \<le> card {(q,i').
      \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}"
    using lep same
    by argo
  then have "card {(q,i'). q \<in> S \<and> (\<exists> b. out_star T (q @ [i']) = Some b)} <
      card {(q,i'). q \<in> S \<and> (\<exists> b. out_star T' (q @ [i']) = Some b)}"
    using gt union
    by presburger
  then have "norm_snd (S,F,T) < norm_snd (S,F',T')"
    by simp
  then have snd: "norm_snd (S,F,T) < norm_snd (S',F',T')"
    using rule2
    by simp

  have fincross: "finite (S' \<times> F')"
    using finS' finF'
    by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (out_star T' (q @ i) = Some x) \<and>
      (\<exists> y. out_star T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (out_star T' (q @ i) =
      Some x) \<and> (\<exists> y. out_star T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    using fincross
    by (simp add: finite_subset)
  obtain l r where
    lr: "T = Node (l,r)"
    using obs_tree.exhaust
    by auto
  have front: "\<forall> p x i2. out_star (Node (l,r)) (p @ i2) = Some x \<longrightarrow>
      out_star (process_output_query (Node (l,r)) (s @ [i]) out) (p @ i2) = Some x"
    using rule2(6) lens output_query_retains_some_specific_output[of "s @ [i]" out l r]
    by presburger
  have one: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (out_star T' (q @ i) = Some x) \<and>
        (\<exists> y. out_star T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<supseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    using rule2(6) lens front lr
    by blast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<subseteq>
      {(q,p). q \<in> S \<and> p \<in> F \<union> {s @ [i]} \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and>
        (\<exists> y. out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    by force
  then have subs3: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (out_star T' (q @ i) = Some x) \<and>
        (\<exists> y. out_star T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<supseteq>
      {(q,p). q \<in> S \<and> p \<in> F \<and> (\<exists> i x. (out_star T (q @ i) = Some x) \<and> (\<exists> y. out_star T (p @ i) = Some y \<and>
          drop (length q) x \<noteq> drop (length p) y))}"
    using one rule2
    by blast
  then have trd: "norm_trd (S,F,T) \<le> norm_trd (S',F',T')"
    using fin3 card_mono
    by fastforce

  then show ?case
    using fst snd trd
    by simp
next
  case (rule3 s1 s2 f w mnew out)
  have mnew: "m = mnew"
    by (metis mdef old.prod.exhaust)
  have fst: "norm_fst (S,F,T) = norm_fst (S',F',T')"
    using rule3
    by fastforce

  have lens: "length (f @ w) = length out"
    using output_query_length rule3(7) mnew
    by blast
  have retain: "\<forall> is. out_star T is \<noteq> None \<longrightarrow> out_star T' is \<noteq> None"
    using rule3 lens output_query_retains_some_output
    by blast
  then have retain_specific: "\<forall> is x. out_star T is = Some x \<longrightarrow> out_star T' is = Some x"
    using output_query_retains_some_specific_output rule3 lens
    by (smt (verit) not_none_not_both_apart out_star.elims)
  have finp: "finite ({q. q \<in> S} \<times> {i. i \<in> I})"
    using rule3
    by simp
  have "{(q,i). q \<in> S \<and> i \<in> I} = {q. q \<in> S} \<times> {i. i \<in> I}"
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp
    by argo
  have "{(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)} \<subseteq> {(q,i). q \<in> S \<and> i \<in> I}"
    using rule3 mnew univI
    by auto
  then have fin2: "finite {(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)}"
    using finp2 finite_subset
    by fast
  have "{(q,i). q \<in> S \<and> (\<exists> y. out_star T (q @ [i]) = Some y)} \<subseteq>
      {(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)}"
    using retain rule3
    by fast
  then have "card {(q,i). q \<in> S \<and> (\<exists> y. out_star T (q @ [i]) = Some y)} \<le>
      card {(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)}"
    using fin2 card_mono
    by auto
  then have snd: "norm_snd (S,F,T) \<le> norm_snd (S',F',T')"
    by auto

  have fincross: "finite (S' \<times> F')"
    using rule3
    by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart_text T' q p} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart_text T' q p}"
    using fincross finite_subset
    by fast
  have split: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart_text T' q p} =
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p}
      \<union> {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p}"
    using rule3
    by fast
  then have fin3_subs: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p}"
    using fin3 finite_subset
    by simp
  obtain z where
    z: "out_star T' (f @ w) = Some z"
    using rule3 lens
    by (metis not_None_eq obs_tree.exhaust process_op_query_not_none_output surj_pair)
  have "apart_witness w T' s1 s2"
    using retain_specific rule3
    by auto
  then have apart_or: "apart_text T' s1 f \<or> apart_text T' s2 f"
    using not_none_not_both_apart rule3 z
    by (smt (z3) apart_text.elims(3) apart_witness.simps)
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p} \<inter>
      {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p} = {}"
    by blast
  then have card_splitup: "card {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart_text T' q p} =
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p} +
      card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p})"
    using rule3 split fin3 card_Un_disjoint
    by fastforce
  have fin_subs_part: "finite {(q,p). ((q = s2 \<or> q = s1) \<and> p = f)}"
    by simp
  have "{(q,p). ((q = s2 \<or> q = s1) \<and> p = f)} \<supseteq> {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p}"
    by fast
  then have fin_part_three: "finite {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p}"
    using fin_subs_part finite_subset
    by fast
  have union: "{(q,p). ((q = s2) \<and> p = f) \<and> apart_text T' q p} \<union> {(q,p). ((q = s1) \<and> p = f) \<and> apart_text T' q p} =
      {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p}"
    by fast
  have "({(q,p). ((q = s2) \<and> p = f) \<and> apart_text T' q p} = {(s2,f)}) \<or>
      ({(q,p). ((q = s1) \<and> p = f) \<and> apart_text T' q p} = {(s1,f)})"
    using apart_or
    by force
  then have "(card {(q,p). ((q = s2) \<and> p = f) \<and> apart_text T' q p} = 1) \<or> (card {(q,p). ((q = s1) \<and> p = f) \<and>
      apart_text T' q p} = 1)"
    by force
  then have card_not_zero: "card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p}) \<ge> 1"
    using union
    by (metis (no_types,lifting) Un_upper1 Un_upper2 card_mono fin_part_three)
  have equal_first_half: "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T q p} = {(q,p). q \<in> S \<and> p \<in> F \<and> apart_text T q p}"
    using rule3
    by auto
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T q p} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p}"
    apply simp
    using retain_specific rule3
    by blast
  then have "{(q,p). q \<in> S \<and> p \<in> F \<and> apart_text T q p} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p}"
    using equal_first_half
    by argo
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart_text T q p} \<le>
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p}"
    using fin3_subs card_mono
    by meson
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart_text T q p} <
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart_text T' q p} +
      card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart_text T' q p})"
    using card_not_zero
    by simp
  then have trd: "norm_trd (S,F,T) < norm_trd (S',F',T')"
    using card_splitup
    by auto

  show ?case
    using fst snd trd
    by fastforce

next
  case (rule4 s fs f q_0 inp outs outf)
  have mnew: "m = (q_0,f)"
    by (simp add: mdef)
  then have fst: "norm_fst (S,F,T) = norm_fst (S',F',T')"
    using rule4
    by auto

  have lens: "length (s @ inp) = length outs"
    using output_query_length rule4 mnew
    by blast
  have lenf: "length (fs @ inp) = length outf"
    using output_query_length rule4 mnew
    by blast
  have retain: "\<forall> is. out_star T is \<noteq> None \<longrightarrow> out_star T' is \<noteq> None"
    using rule4 lens lenf output_query_retains_some_output
    by blast
  then have retain_specific: "\<forall> is x. out_star T is = Some x \<longrightarrow> out_star T' is = Some x"
    using output_query_retains_some_specific_output rule4 lens lenf
    by (smt (verit,ccfv_SIG) out_star.elims out_star.simps(1))
  have finp: "finite ({q. q \<in> S} \<times> {i. i \<in> I})"
    using rule4
    by simp
  have "{(q,i). q \<in> S \<and> i \<in> I} = {q. q \<in> S} \<times> {i. i \<in> I}"
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp
    by argo
  have "{(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)} \<subseteq> {(q,i). q \<in> S \<and> i \<in> I}"
    using rule4 mnew univI
    by auto
  then have fin2: "finite {(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)}"
    using finp2 finite_subset
    by fast
  have "{(q,i). q \<in> S \<and> (\<exists> y. out_star T (q @ [i]) = Some y)} \<subseteq>
      {(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)}"
    using retain rule4
    by fast
  then have "card {(q,i). q \<in> S \<and> (\<exists> y. out_star T (q @ [i]) = Some y)} \<le>
      card {(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)}"
    using fin2 card_mono
    by auto
  then have snd: "norm_snd (S,F,T) \<le> norm_snd (S',F',T')"
    by auto

  have invar: "invar (q_0,f) (S',F',T')"
    using rule4 algo_step_keeps_invar algo_step.rule4 mnew
    by meson
  have "\<exists> x. out_star T' (s @ inp) = Some x"
    by (metis lenf lens not_Some_eq obs_tree.exhaust old.prod.exhaust
    output_query_retains_some_output process_op_query_not_none_output rule4.hyps(11))
  then obtain new_outs where
    new_outs: "out_star T' (s @ inp) = Some new_outs"
    by fast
  have "\<exists> y. out_star T' (fs @ inp) = Some y"
    using process_op_query_not_none_output
    by (metis lenf not_Some_eq obs_tree.exhaust old.prod.exhaust rule4.hyps(11))
  then obtain new_outf where
    new_outf: "out_star T' (fs @ inp) = Some new_outf"
    by fast
  have query_s: "new_outs = (output_query (q_0,f) (s @ inp))"
    using invar new_outs
    by auto
  have query_fs: "new_outf = (output_query (q_0,f) (fs @ inp))"
    using invar new_outf
    by auto
  have "drop (length s) (output_query (q_0,f) (s @ inp)) \<noteq>
      drop (length fs) (output_query (q_0,f) (fs @ inp))"
    using rule4
    by (metis output_query.simps)
  then have "drop (length s) new_outs \<noteq> drop (length fs) new_outf"
    using rule4 query_s query_fs
    by argo
  then have apart_s_fs: "apart_text T' s fs"
    using new_outs new_outf
    by auto
  have fincross: "finite (S' \<times> F')"
    using rule4
    by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart_text T' q p} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart_text T' q p}"
    using fincross finite_subset
    by fast
  have one_elem: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart_text T' q p} = {(s,fs)}"
    using apart_s_fs rule4
    by fast
  have union: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (apart_text T' q p)} =
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p} \<union>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart_text T' q p}"
    by fast
  then have finite_subs: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p} \<and>
      finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart_text T' q p}"
    using fin3
    by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s) \<and> p = fs) \<and> apart_text T' q p} \<inter> {(s,fs)} = {}"
    by blast
  then have card_splitup: "card {(q,p). q \<in> S' \<and> p \<in> F' \<and> (apart_text T' q p)} =
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p} +
      card {(s,fs)}"
    using fin3 union one_elem finite_subs card_Un_disjoint[of "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p}" "{(s,fs)}"]
    by argo
  have removed: "{(q,p). q \<in> S \<and> p \<in> F \<and> (apart_text T q p)} =
      {(q,p). q \<in> S \<and> p \<in> F \<and> \<not> (q = s \<and> p = fs) \<and> (apart_text T q p)}"
    using rule4
    by fast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> (q = s \<and> p = fs) \<and> (apart_text T q p)} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p}"
    using retain_specific rule4
    by (smt (verit,ccfv_SIG) Pair_inject apart_text.simps case_prodE case_prodI2 mem_Collect_eq subsetI)
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> (apart_text T q p)} \<le>
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p}"
    using fin3 card_mono removed finite_subs
    by force
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> (apart_text T q p)} <
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart_text T' q p} + card {(s,fs)}"
    by simp
  then have trd: "norm_trd (S,F,T) < norm_trd (S',F',T')"
    using card_splitup
    by simp

  show ?case
    using fst snd trd
    by simp
qed

end
end
