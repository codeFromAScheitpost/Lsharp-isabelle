theory Lsharp
  imports "./MealyMachine"
begin
sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]


text \<open>this Theory proofs the correctness and runtime of a modified version of the L# Algorythm proposed by
  Frits Vandraager et. al. it defines the proposed rules as a transition system to achieve this goal.\<close>


datatype ('input,'output) obs_tree = Node "'input \<Rightarrow> (('input,'output) obs_tree \<times> 'output) option"


fun otree_star :: "('input,'output) obs_tree \<Rightarrow> ('input :: finite) list \<Rightarrow> (('input,'output) obs_tree \<times> 'output list) option" where
"otree_star ot [] = Some (ot, [])" |
"otree_star (Node t) (i # is) = (case t i of
    Some (n,op) \<Rightarrow> (case (otree_star n is) of
      Some (ot,ops) \<Rightarrow> Some (ot,op # ops) |
      None \<Rightarrow> None) |
    None \<Rightarrow> None)"


fun out_star :: "('input,'output) obs_tree \<Rightarrow> ('input :: finite) list \<Rightarrow> ('output list) option" where
"out_star ot [] = Some []" |
"out_star (Node t) (i # is) = (case t i of
    Some (n,op) \<Rightarrow>
    (case (out_star n is) of
      Some ops \<Rightarrow> Some (op # ops) |
      None \<Rightarrow> None) |
    None \<Rightarrow> None)"

definition func_sim :: "('state,'input,'output) mealy \<Rightarrow> ('input,'output) obs_tree \<Rightarrow> (('input :: finite) list \<Rightarrow> 'state) \<Rightarrow> bool" where
"func_sim m T f = (case m of
    (q_0,t) \<Rightarrow> ((f [] = q_0) \<and> (\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow>
      trans_star t (f acc) is = (f (acc @ is),(drop (length acc) ops)))))"

fun apart :: "(('input :: finite),'output) obs_tree \<Rightarrow> 'input list \<Rightarrow> 'input list \<Rightarrow> bool" where
"apart q_0 t1 t2 = (\<exists> i x y. out_star q_0 (t1 @ i) = Some x \<and>
    out_star q_0 (t2 @ i) = Some y \<and>
    drop (length t1) x \<noteq> drop (length (t2)) y)"

fun isolated :: "(('input :: finite),'output) obs_tree \<Rightarrow> 'input list set \<Rightarrow> 'input list \<Rightarrow> bool" where
"isolated q_0 S f = (\<forall> s \<in> S. apart q_0 s f)"

fun apart_witness :: "('input,'output) obs_tree \<Rightarrow> 'input list \<Rightarrow> 'input list \<Rightarrow> ('input :: finite) list \<Rightarrow> bool" where
"apart_witness q_0 t1 t2 is = (\<exists> x y. out_star q_0 (t1 @ is) = Some x \<and>
    out_star q_0 (t2 @ is) = Some y \<and>
    drop (length t1) x \<noteq> drop (length t2) y)"


fun output_query :: "('state,('input :: finite),'output) mealy \<Rightarrow> 'input list \<Rightarrow> 'output list" where
"output_query (q_0,t) is = trans_star_output t q_0 is"


fun process_output_query :: "('input,'output) obs_tree \<Rightarrow> ('input :: finite) list \<Rightarrow> 'output list \<Rightarrow> ('input,'output) obs_tree" where
"process_output_query q [] [] = q" |
"process_output_query q i [] = undefined" |
"process_output_query q [] _ = undefined" |
"process_output_query (Node t) (i # is) (op # ops) = (case t i of
    None \<Rightarrow> (Node (\<lambda> j. if j = i
      then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
      else t j)) |
    Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
      then Some ((process_output_query tree is ops),out)
      else t j)))"
text \<open>@{const process_output_query} adds new knowledge about the original mealy machine to the Tree\<close>

type_synonym ('input,'output) state = "'input list set \<times> 'input list set \<times> ('input,'output) obs_tree"

type_synonym ('input,'output) state_list = "'input list list \<times> 'input list list \<times> ('input,'output) obs_tree"


fun sapart :: "(('input :: finite),'output) state \<Rightarrow> bool" where
"sapart (S,F,T) = (\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart T s1 s2)"

fun in_F :: "(('input :: finite),'output) state \<Rightarrow> 'input list \<Rightarrow> bool" where
"in_F (S,F,T) f = ((\<exists> s \<in> S. \<exists> i. f = s @ [i]) \<and> f \<notin> S \<and> out_star T f \<noteq> None)"
text \<open>in the original paper the definition of the Frontier F is rather implicit we use @{term "Collect (in_F (S,F,T))"}
  as our F in many cases\<close>

definition invar :: "('state,('input :: finite),'output) mealy \<Rightarrow> (('input :: finite),'output) state \<Rightarrow> bool" where
"invar m st = (case st of
    (S,F,T) \<Rightarrow>
    (\<forall> e. \<not> (e \<in> S \<and> e \<in> F)) \<and>
    (\<forall> e \<in> S. out_star T e \<noteq> None) \<and>
    finite S \<and> finite F \<and>
    sapart (S,F,T) \<and>
    (\<forall> i. out_star T i \<noteq> None \<longrightarrow> out_star T i = Some (output_query m i)) \<and>
    (\<forall> f \<in> F. in_F (S,F,T) f) \<and>
    (\<forall> f. in_F (S,F,T) f \<longrightarrow> f \<in> F) \<and>
    [] \<in> S \<and> (\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)))"


fun hypothesis :: "(('input :: finite),'output) state \<Rightarrow> ('input list,'input,'output) transition \<Rightarrow> bool" where
"hypothesis (S,F,T) t =
    (\<forall> s \<in> S. \<forall> i. \<exists> tran op n out. (otree_star T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> S
        then t (s,i) = (s @ [i],out)
        else (\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out))))"


fun norm_fst :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_fst (S,F,T) = ((card S * (card S + 1)) div 2)"

fun norm_snd :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_snd (S,F,T) = card {(q,i). q \<in> S \<and> out_star T (q @ [i]) \<noteq> None}"

fun norm_trd :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm_trd (S,F,T) = card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p}"


fun norm :: "(('input :: finite),'output) state \<Rightarrow> nat" where
"norm st = norm_fst st + norm_snd st + norm_trd st"
text \<open>the norm is the same proposed by Vandraager et al.\<close>

locale Mealy =
  fixes m :: "('state :: finite,'input :: finite,'output) mealy" and
    I :: "'input set" and
    Q :: "'state set" and
    difference_query :: "('state,'input,'output) mealy \<Rightarrow> 'input list \<Rightarrow> 'input list \<Rightarrow> 'input list option" and
    updateF :: "('input,'output) obs_tree \<Rightarrow> 'input list list \<Rightarrow> 'input list list \<Rightarrow> 'input list list" and
    find1 :: "('input,'output) obs_tree \<Rightarrow> 'input list list \<Rightarrow> 'input list list \<Rightarrow> 'input list option" and
    find2 :: "('input,'output) obs_tree \<Rightarrow> 'input list list \<Rightarrow> 'input list list \<Rightarrow> 'input list option" and
    find3 :: "('input,'output) obs_tree \<Rightarrow> 'input list list \<Rightarrow> 'input list list \<Rightarrow> 'input list option" and
    find4 :: "('input,'output) obs_tree \<Rightarrow> 'input list list \<Rightarrow> 'input list list \<Rightarrow> ('input list \<times> 'input list) option"
  assumes
  univI: "I = UNIV" and
  univQ: "Q = UNIV" and
  difference_query_def: "\<forall> x q_0 f s fs.(difference_query (q_0,f) s fs = Some x) \<longrightarrow> (drop (length s) (trans_star_output f q_0 (s @ x)) \<noteq>
      drop (length fs) (trans_star_output f q_0 (fs @ x)))" and
  difference_query_def_none: "\<forall> q_0 f s fs.(difference_query (q_0,f) s fs = None) \<longleftrightarrow> (\<nexists> x.(drop (length s) (trans_star_output f q_0 (s @ x)) \<noteq>
      drop (length fs) (trans_star_output f q_0 (fs @ x))))" and
  updateF_def: "\<forall> S F T. set (updateF T S F) = {fnew. in_F (set S,set F,T) fnew}" and
  find1_def: "\<forall> x S F T. (find1 T S F = Some x) \<longrightarrow> (x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x))" and
  find1_def_none: "\<forall> S F T. (find1 T S F = None) \<longleftrightarrow> (\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x))" and
  find2_def: "\<forall> x S F T.(find2 T S F = Some x) \<longrightarrow> (\<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> out_star T x = None)" and
  find2_def_none: "\<forall> S F T.(find2 T S F = None) \<longleftrightarrow> (\<nexists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> out_star T x = None)" and
  find3_def: "\<forall> x S F T. (find3 T S F = Some x) \<longrightarrow> (\<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2 \<and>
      apart_witness T s1 s2 w)" and
  find3_def_none: "\<forall> S F T. (find3 T S F = None) \<longleftrightarrow> (\<nexists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2 \<and>
      apart_witness T s1 s2 w)" and
  find4_def: "\<forall> x y S F T.(find4 T S F = Some (x,y)) \<longrightarrow>
      (\<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        difference_query m s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)" and
  find4_def_none: "\<forall> S F T.(find4 T S F = None) \<longleftrightarrow>
      (\<nexists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        difference_query m s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
begin

text \<open>this locale is helpful for proving the algorythm.
  \<^item> we fix m as our mealy machine as it will not change.
  \<^item> we assert that m can only have a finite number of states, and these states are reprisented as a finite datatype.
  \<^item> we fix \<open>Q\<close> as the finite Universe of the states datatype.
\<^item> we fix \<open>I\<close> as the finite Universe of the input datatype both \<open>I\<close> and \<open>Q\<close> are helpfull only to the readability of the proof.
  \<^item> we fix \<open>difference_query\<close> as a query that returns None if the two states given are not apart and an example if they are.
  \<^item> we fix \<open>updateF\<close> and find functions as functions that would be implemented for an executebale version of the algorythm.\<close>


inductive algo_step :: "('state,'input,'output) mealy \<Rightarrow>
    ('input,'output) state \<Rightarrow>
    ('input,'output) state \<Rightarrow>
    bool" where
rule1: "\<lbrakk>f \<in> F; \<forall> s \<in> S. apart T s f\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S \<union> {f},{fnew. in_F (S \<union> {f},F,T) fnew},T)" |

rule2: "\<lbrakk>s \<in> S; (out_star T (s @ [i]) = None);
      output_query m (s @ [i]) = out\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S,F \<union> {s @ [i]},process_output_query T (s @ [i]) out)" |

rule3: "\<lbrakk>s1 \<in> S; s2 \<in> S; s1 \<noteq> s2; f \<in> F;
      \<not> apart T f s1;
      \<not> apart T f s2;
      apart_witness T s1 s2 w;
      output_query m (f @ w) = out\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S,F,process_output_query T (f @ w) out)" |

rule4: "\<lbrakk>\<forall> s1 \<in> S. \<forall> i. out_star T (s1 @ [i]) \<noteq> None;
      \<forall> f1 \<in> F. \<not> (isolated T S f1);
      fs \<in> F;
      s \<in> S;
      \<not> apart T s fs;
      difference_query m s fs = Some inp;
      output_query m (s @ inp) = outs;
      output_query m (fs @ inp) = outf\<rbrakk> \<Longrightarrow>
    algo_step m (S,F,T) (S,F,process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)"
text \<open>rule4 differs from the original definition by Vandraager et. al. as he compares two whole mealy machines
  while we complare only two states. this difference removes the need of further counterexample processing.\<close>


section \<open>invar\<close>


lemma invars:
  assumes "invar m (S,F,T)"
  shows "\<forall> e. \<not> (e \<in> S \<and> e \<in> F)" and
    "\<forall> e \<in> S. out_star T e \<noteq> None" and
    "finite S" and
    "finite F" and
    "sapart (S,F,T)" and
    "\<forall> i. out_star T i \<noteq> None \<longrightarrow> out_star T i = Some (output_query m i)" and
    "\<forall> f \<in> F. in_F (S,F,T) f" and
    "\<forall> f. in_F (S,F,T) f \<longrightarrow> f \<in> F" and
    "[] \<in> S" and
    "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
      using assms
      unfolding invar_def
      by blast +


lemma is_invar:
  assumes "\<forall> e. \<not> (e \<in> S \<and> e \<in> F)" and
    "\<forall> e \<in> S. out_star T e \<noteq> None" and
    "finite S" and
    "finite F" and
    "sapart (S,F,T)" and
    "\<forall> i. out_star T i \<noteq> None \<longrightarrow> out_star T i = Some (output_query m i)" and
    "\<forall> f \<in> F. in_F (S,F,T) f" and
    "\<forall> f. in_F (S,F,T) f \<longrightarrow> f \<in> F" and
    "[] \<in> S" and
    "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
  shows "invar m (S,F,T)"
    using assms
    unfolding invar_def
    by blast


lemma out_star_map_empty:
  assumes "i \<noteq> []"
  shows "out_star (Node (\<lambda> x. None)) i = None"
    using assms
    apply (induction i)
    apply simp
    by force


lemma empty_is_invar: "invar m ({[]},{},Node Map.empty)"
text \<open>@{term "({[]},{},Node Map.empty)"} is the starting point for our algorythm\<close>
proof -
  have a: "\<forall> i. i \<noteq> [] \<longrightarrow> out_star (Node (\<lambda> x. None)) i = None"
    using out_star_map_empty
    by blast
  have "output_query m [] = []"
    by (induction m) auto
  then have "out_star (Node (\<lambda> x. None)) [] = Some (output_query m [])"
    by simp
  then have b: "\<forall> i. (\<exists> y. out_star (Node (\<lambda> x. None)) i = Some y) \<longrightarrow> out_star (Node (\<lambda> x. None)) i = Some (output_query m i)"
    using a
    by (metis option.distinct(1))
  then show ?thesis
    unfolding invar_def
    by auto
qed


section \<open>in_F\<close>


lemma finiteF:
  assumes "finite S"
  shows "finite {f. in_F ((S,F,T) :: ('input,'output) state) f}"
proof -
  have fincross: "finite (S \<times> I)"
    using assms univI
    by fastforce
  have eq_img: "{s @ [i] |
      s i. s \<in> S \<and> i \<in> I} = (\<lambda> (s,i). s @ [i]) ` (S \<times> I)"
    by fast
  have eq_different: "{s @ [i] |
      s i. s \<in> S \<and> i \<in> I} = {f. (\<exists> s \<in> S. \<exists> i. f = s @ [i])}"
    using univI
    by blast
  have "{f. (\<exists> s \<in> S. \<exists> i. f = s @ [i])} \<supseteq> {f. in_F (S,F,T) f}"
    by auto
  then have "finite {f. in_F (S,F,T) f}"
    using assms eq_img fincross finite_subset eq_different
    by auto
  then show ?thesis
    using assms
    by simp
qed


section \<open>Star\<close>


lemma otree_eq_out: "case otree_star (Node r) i of
    None \<Rightarrow> out_star (Node r) i = None |
    Some (n,out) \<Rightarrow> out_star (Node r) i = Some out"
proof (induction i arbitrary: r)
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
    then obtain r2 o2 where
      b: "b = (Node r2,o2)"
      by (metis obs_tree.exhaust surj_pair)
    then have one: "otree_star (Node r) (a # i) = (case otree_star (Node r2) i of
        None \<Rightarrow> None |
        Some (node,out) \<Rightarrow> Some (node,o2 # out))"
      using Some
      by simp
    have two: "out_star (Node r) (a # i) = (case out_star (Node r2) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some b
      by simp
    have "case otree_star (Node r2) i of
        None \<Rightarrow> out_star (Node r2) i = None |
        Some (n,out) \<Rightarrow> out_star (Node r2) i = Some out"
      using Cons
      by simp
    then show ?thesis
      using one two
      apply (cases "otree_star (Node r2) i")
      by auto
  qed
qed


lemma out_eq_otree: "\<exists> node. (case out_star (Node r) i of
    None \<Rightarrow> otree_star (Node r) i = None |
    Some out \<Rightarrow> otree_star (Node r) i = Some (node,out))"
proof (induction i arbitrary: r)
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
    then obtain r2 o2 where
      b: "b = (Node r2,o2)"
      by (metis obs_tree.exhaust surj_pair)
    then have one: "out_star (Node r) (a # i) = (case out_star (Node r2) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some
      by simp
    have two: "out_star (Node r) (a # i) = (case out_star (Node r2) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some b
      by simp
    have three: "otree_star (Node r) (a # i) = (case otree_star (Node r2) i of
        None \<Rightarrow> None |
        Some (node,out) \<Rightarrow> Some (node,o2 # out))"
      using Some b
      by simp
    have "\<exists> node. (case out_star (Node r2) i of
        None \<Rightarrow> otree_star (Node r2) i = None |
        Some out \<Rightarrow> otree_star (Node r2) i = Some (node,out))"
      using Cons
      by simp
    then show ?thesis
      using one two three
      apply (cases "out_star (Node r2) i")
      by auto
  qed
qed


lemma otree_induct_helper: "t i = (Some (tree,out)) \<Longrightarrow> length op = length acc \<Longrightarrow>
    otree_star (process_output_query tree acc op) acc = Some (lt,lout) \<Longrightarrow>
    otree_star (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (lt,out # lout)"
  by (induction acc) auto


lemma output_induct_helper: "t i = (Some (tree,out)) \<Longrightarrow> length op = length acc \<Longrightarrow>
    out_star (process_output_query tree acc op) acc = Some lout \<Longrightarrow>
    out_star (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (out # lout)"
  by (induction acc) auto


lemma otree_induct_helper_none: "t i = None \<Longrightarrow> length op = length acc \<Longrightarrow>
    otree_star (process_output_query (Node Map.empty) acc op) acc = Some (lt,lout) \<Longrightarrow>
    otree_star (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (lt,out # lout)"
  by (induction acc) auto


lemma output_induct_helper_none: "t i = None \<Longrightarrow> length op = length acc \<Longrightarrow>
    out_star (process_output_query (Node Map.empty) acc op) acc = Some lout \<Longrightarrow>
    out_star (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (out # lout)"
  by (induction acc) auto


lemma otree_split: "otree_star (Node r) (a # acc) = Some (tr1,out1) \<Longrightarrow> r a \<noteq> None"
  by (auto split: prod.splits option.splits)


lemma out_split: "out_star (Node r) (a # acc) = Some (out1) \<Longrightarrow> r a \<noteq> None"
  by (auto split: prod.splits option.splits)


lemma otree_star_split_none:
  assumes "t i = None" and
    "otree_star (Node tq) acc = Some (Node t,ops)"
  shows "otree_star (Node tq) (acc @ [i]) = None"
using assms proof (induction acc arbitrary: ops tq)
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
    then have apart_i: "otree_star (Node tq) ((a # acc @ [i])) =
        (case otree_star tr (acc @ [i]) of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some
      by auto
    then have apart: "otree_star (Node tq) ((a # acc)) =
        (case otree_star tr acc of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some b
      by auto
    then have "otree_star tr acc \<noteq> None"
      using Some Cons b
      by (metis option.distinct(1) option.simps(4))
    then obtain opl where
      opl: "otree_star tr acc = Some (Node t,opl)"
      using Some Cons b apart
      by fastforce
    obtain ntq where
      ntq: "tr = Node ntq"
      using b Some Cons
      by (metis obs_tree.exhaust)
    then have "otree_star (Node ntq) (acc @ [i]) = None"
      using Cons opl
      by blast
    then show ?thesis
      using Cons b Some apart opl ntq apart_i
      by auto
  qed
qed


lemma otree_star_split:
  assumes "t i = Some (tree,op)" and
    "otree_star (Node tq) acc = Some (Node t,ops)"
  shows "otree_star (Node tq) (acc @ [i]) = Some (tree,ops @ [op])"
using assms proof (induction acc arbitrary: ops tq)
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
    then have apart_i: "otree_star (Node tq) (a # acc @ [i]) =
        (case otree_star tr (acc @ [i]) of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some
      by auto
    then have apart: "otree_star (Node tq) ((a # acc)) =
        (case otree_star tr acc of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some b
      by auto
    then have "otree_star tr acc \<noteq> None"
      using Some Cons b
      by (metis option.distinct(1) option.simps(4))
    then obtain opl where
      opl: "otree_star tr acc = Some (Node t,opl)"
      using Some Cons b apart
      by fastforce
    obtain ntq where
      ntq: "tr = Node ntq"
      using b Some Cons
      by (metis obs_tree.exhaust)
    then have "otree_star (Node ntq) (acc @ [i]) = Some (tree,opl @ [op])"
      using Cons opl
      by blast
    then show ?thesis
      using Cons b Some apart opl ntq apart_i
      by auto
  qed
qed


lemma out_star_substring_not_none:
  assumes "out_star T (p @ k) \<noteq> None"
  shows "out_star T p \<noteq> None"
using assms proof (induction p arbitrary: T)
  case Nil
  then show ?case
    by simp
next
  case (Cons i "is")
  obtain t where
    t: "T = Node t"
    using obs_tree.exhaust
    by blast
  then show ?case proof(cases "t i")
    case None
    then show ?thesis
      using Cons t
      by auto
  next
    case (Some a)
    obtain node out where
      a: "a = (node,out)"
      by fastforce
    then have "out_star T ((i # is) @ k) = (case out_star node (is @ k) of
        Some newout \<Rightarrow> Some (out # newout) |
        None \<Rightarrow> None)"
      using Some t
      by simp
    then have "out_star node (is @ k) \<noteq> None"
      using Cons t
      by (metis option.simps(4))
    then have not_none: "out_star node is \<noteq> None"
      using Cons
      by blast
    have "out_star T (i # is) = (case out_star node is of
        Some newout \<Rightarrow> Some (out # newout) |
        None \<Rightarrow> None)"
      using Some t a
      by auto
    then have "out_star T (i # is) \<noteq> None"
      using not_none
      by auto
    then show ?thesis
      by blast
  qed
qed


lemma otree_star_substring_not_none:
  assumes "otree_star T (p @ k) \<noteq> None"
  shows "otree_star T p \<noteq> None"
    using assms out_eq_otree otree_eq_out
    by (metis (mono_tags,lifting) obs_tree.exhaust option.simps(4) out_star_substring_not_none)


lemma otree_star_not_none_split:
  assumes "otree_star T (s @ [i]) \<noteq> None"
  shows "\<exists> trans out. otree_star T s = Some (Node trans,out) \<and> trans i \<noteq> None"
proof(rule ccontr)
  assume ass: "\<not> (\<exists> trans out. otree_star T s = Some (Node trans,out) \<and> trans i \<noteq> None)"
  have "\<exists> trans out. otree_star T s = Some (Node trans,out)"
    using assms
    by (metis not_Some_eq obs_tree.exhaust otree_star_substring_not_none surj_pair)
  then obtain trans out where
    trans: "otree_star T s = Some (Node trans,out)"
    by blast
  then have "trans i = None"
    using ass
    by blast
  then have "otree_star T (s @ [i]) = None"
    by (metis local.trans obs_tree.exhaust otree_star_split_none)
  then show False
    using assms
    by simp
qed


section \<open>hypothesis\<close>


lemma trans_ex_aux:
  assumes "t = (\<lambda> (s,i). (case otree_star T s of
      None \<Rightarrow> ([],none) |
      Some (Node tran,op) \<Rightarrow> (case tran i of
        None \<Rightarrow> ([],none) |
        Some (n,out) \<Rightarrow> (f (s @ [i]),out))))" and
  "\<exists> node out n op. otree_star T s = Some (Node node,out) \<and> node i = Some (n,op)"
  shows "\<exists> node out n op. otree_star T s = Some (Node node,out) \<and> node i = Some (n,op) \<and> t (s,i) = (f (s @ [i]),op)"
    using assms
    by auto


lemma exists_hypothesis:
  assumes "invar m (S,F,T)" and
    "\<not> (\<exists> f \<in> F. \<forall> s \<in> S. apart T s f)" and
    "\<not> (\<exists> s \<in> S. EX i. (out_star T (s @ [i]) = None))"
  shows "\<exists> t. hypothesis (S,F,T) t"
proof -
  have inf: "\<forall> f. in_F (S,F,T) f \<longrightarrow> f \<in> F"
    using assms(1) invars
    by presburger
  have notning_none: "\<forall> s \<in> S. \<forall> i. out_star T (s @ [i]) \<noteq> None"
    using assms
    by meson
  then have nothing_none_otree: "\<forall> s \<in> S. \<forall> i. otree_star T (s @ [i]) \<noteq> None"
    by (smt (verit) case_optionE option.discI otree_eq_out otree_star.elims)
  then have a: "\<forall> s \<in> S. otree_star T s \<noteq> None"
    using otree_star_substring_not_none
    by blast
  then have "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> in_F (S,F,T) (s @ [i])"
    using notning_none
    by fastforce
  then have "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> (s @ [i]) \<in> F"
    using inf
    by blast
  then have re: "\<forall> s \<in> S. \<forall> i. s @ [i] \<in> S \<or> s @ [i] \<in> F"
    by blast
  then have "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> (\<exists> s2 \<in> S. \<not> apart T s2 (s @ [i]))"
    using assms
    by blast
  then have "\<exists> f. \<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> f (s @ [i]) \<in> S \<and> \<not> apart T (f (s @ [i])) (s @ [i])"
    by (metis re assms(2))
  then obtain fone where
    fone: "\<forall> s \<in> S. \<forall> i. (s @ [i] \<notin> S \<longrightarrow> fone (s @ [i]) \<in> S \<and> \<not> apart T (fone (s @ [i])) (s @ [i]))"
    by blast
  then obtain f where
    f: "f = (\<lambda> i. (if i \<in> S
        then i
        else fone i))"
    by simp
  then have fsmame: "\<forall> inp \<in> S. f inp = inp"
    by simp
  then have fofnotinS: "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> \<not> apart T (f (s @ [i])) (s @ [i]) \<and> (f (s @ [i])) \<in> S"
    using f fone
    by auto
  have exists: "\<forall> s \<in> S. \<forall> i. \<exists> node out. otree_star T s = Some (Node node,out) \<and> node i \<noteq> None"
    using otree_star_not_none_split nothing_none_otree
    by blast
  obtain none where
    "none \<in> (UNIV :: 'output set)"
    by simp
  have "\<forall> s \<in> S. \<forall> i. \<exists> node outs out n. otree_star T s = Some (Node node,outs) \<and> node i = Some (n,out)"
    using exists
    by fast
  have "\<exists> t. t = (\<lambda> (s,i). (case otree_star T s of
      None \<Rightarrow> ([],none) |
      Some (Node tran,op) \<Rightarrow> (case tran i of
        None \<Rightarrow> ([],none) |
        Some (n,out) \<Rightarrow> (if s @ [i] \<in> S
          then (s @ [i],out)
          else (f (s @ [i]),out)))))"
    by simp
  then obtain t where
    thelp: "t = (\<lambda> (s,i). (case otree_star T s of
        None \<Rightarrow> ([],none) |
        Some (Node tran,op) \<Rightarrow> (case tran i of
          None \<Rightarrow> ([],none) |
          Some (n,out) \<Rightarrow> (f (s @ [i]),out))))"
    by fast
  then have tdef: "\<forall> s \<in> S. \<forall> i. \<exists> node out n op.
      (otree_star T s = Some (Node node,out)) \<and> (node i = Some (n,op) \<and> t (s,i) = (f (s @ [i]),op))"
    using exists trans_ex_aux thelp
    by fast
  then have "\<forall> s \<in> S. \<forall> i. \<exists> tran op n out.
      otree_star T s = Some (Node tran,op) \<and>
      tran i = Some (n,out) \<and> (if s @ [i] \<in> S
        then t (s,i) = (s @ [i],out)
        else \<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out))"
    using f fone
    by fastforce
  then have "hypothesis (S,F,T) t"
    by simp
  then show ?thesis
    by blast
qed


lemma hypothesis_split_in_S:
  assumes "hypothesis (S,F,T) t" and
    "s \<in> S" and
    "otree_star T s = Some (Node tran,op)" and
    "tran i = Some (n,out)" and
    "s @ [i] \<in> S"
  shows "t (s,i) = (s @ [i],out)"
proof -
  have "\<exists> tran op n out. (otree_star T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> S
        then t (s,i) = (s @ [i],out)
        else (\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)))"
    using assms(1,2)
    by simp
  then have "t (s,i) = (s @ [i],out)"
    using assms
    by auto
  then show ?thesis
    by simp
qed


lemma hypothesis_split_notin_S:
  assumes "hypothesis (S,F,T) t" and
    "s \<in> S" and
    "otree_star T s = Some (Node tran,op)" and
    "tran i = Some (n,out)" and
    "s @ [i] \<notin> S"
  shows "\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)"
proof -
  have "\<exists> tran op n out. (otree_star T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> S
        then t (s,i) = (s @ [i],out)
        else (\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)))"
    using assms(1,2)
    by fastforce
  then have "\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)"
    using assms
    by auto
  then show ?thesis
    by simp
qed


section \<open>apart\<close>


lemma apart_sim:
  assumes "apart T p q" and
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
  have "\<exists> i x y. out_star T (q @ i) = Some x \<and> out_star T (p @ i) = Some y \<and> drop (length q) x \<noteq>
      drop (length p) y"
    using assms
    by fastforce
  then show False
    using a b as
    by fastforce
qed


lemma apart_none:
  assumes "\<not> apart T f s1" and
    "\<not> apart T f s2" and
    "apart_witness T s1 s2 w"
  shows "out_star T (f @ w) = None"
  text \<open>this lemma is useful as we know we can change the output for @{term "out_star T (f @ w)"} in rule2\<close>
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
    "apart_witness T s1 s2 w"
  shows "apart T f s1 \<or> apart T f s2"
    by (metis apart_none assms option.discI)


lemma exsist_witness:
  assumes "apart T s1 s2"
  shows "\<exists> w. apart_witness T s1 s2 w"
proof -
  have "\<exists> i x y. out_star T (s1 @ i) = Some x \<and>
      out_star T (s2 @ i) = Some y \<and>
      drop (length s1) x \<noteq> drop (length (s2)) y"
    using assms
    by auto
  then obtain w where
    "\<exists> x y. out_star T (s1 @ w) = Some x \<and>
        out_star T (s2 @ w) = Some y \<and>
        drop (length s1) x \<noteq> drop (length (s2)) y"
    by blast
  then have "apart_witness T s1 s2 w"
    by simp
  then show ?thesis
    by fast
qed


section \<open>output_query\<close>


lemma output_query_length:
  assumes "output_query m iss = os"
  shows "length iss = length os"
  text \<open>we base our process_output_query proofs on the length of input and output being the same, to combine this lemma is needed\<close>
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


section \<open>process Output Query\<close>


lemma process_op_query_not_none:
"length ip = length op \<Longrightarrow> otree_star (process_output_query (Node t) ip op) ip \<noteq> None"
proof (induction ip arbitrary: op t)
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
    have "otree_star (process_output_query (Node Map.empty) ip ofs) ip \<noteq> None"
      using Cons ofs
      by auto
    then obtain lt lout where
      "otree_star (process_output_query (Node Map.empty) ip ofs) ip = Some (lt,lout)"
      by fast
    then have "otree_star (process_output_query (Node t) (a # ip) op) (a # ip) = Some (lt,os # lout)"
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
      then have "otree_star (process_output_query (Node t) (a # ip) op) (a # ip) = Some (lt,c # lout)"
        using Cons ofs Some Pair otree_induct_helper
        by auto
      then show ?thesis
        by auto
    qed
  qed
qed


lemma output_query_different: "length op = length ip \<Longrightarrow> i \<noteq> ac \<Longrightarrow>
    (case process_output_query (Node t) (i # ip) (os # op) of
      (Node ts) \<Rightarrow> ts ac = t ac)"
  by (auto split: prod.splits option.splits)


lemma otree_star_output_query_different:
  assumes "ac \<noteq> i" and
    "length ip = length op" and
    "t ac = Some (tree,outies)"
  shows "otree_star (process_output_query (Node t) (i # ip) (os # op)) (ac # list) =
      (case otree_star tree list of
        Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
        None \<Rightarrow> None)"
proof -
  have "case process_output_query (Node t) (i # ip) (os # op) of
      (Node ts) \<Rightarrow> ts ac = t ac"
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
  text \<open>this lemma is important as it shows that if a input is not none before the processing of a query it will stay that way after,
    this is useful to prove that parts of the norm does not decrease.\<close>
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
      case (Node r)
      then show ?thesis using a proof (cases "a = ac")
        case True
        then show ?thesis proof (cases "r ac")
          case None
          then have "otree_star (q_0) (ac # list) = None"
            using Node
            by auto
          then show ?thesis
            using a Cons
            by simp
        next
          case (Some c)
          then obtain tree outies where
            outies: "r ac = Some (tree,outies)"
            using Node Cons a Some
            by fastforce
          then have h2: "otree_star (process_output_query q_0 (a # ip) (os # ops)) (ac # list) =
              (case otree_star (process_output_query tree ip ops) list of
                Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                None \<Rightarrow> None)"
            using Some True Node Cons a otree_star_output_query_different
            by auto
          have h1: "otree_star q_0 (ac # list) = (case otree_star tree list of
              Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
              None \<Rightarrow> None)"
            using outies Node
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
            using Node
            by auto
          then show ?thesis
            using a Cons
            by simp
        next
          case (Some c)
          then obtain tree outies where
            outies: "r ac = Some (tree,outies)"
            using Node Cons a Some
            by fastforce
          then have h2: "otree_star (process_output_query q_0 (a # ip) (os # ops)) (ac # list) =
              (case otree_star tree list of
                Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                None \<Rightarrow> None)"
            using Some False Node Cons a otree_star_output_query_different
            apply simp
            by (auto split: prod.splits option.splits)
          have h1: "otree_star q_0 (ac # list) = (case otree_star tree list of
              Some (n,opl) \<Rightarrow>
              Some (n,outies # opl) |
              None \<Rightarrow> None)"
            using outies Node
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


lemma output_query_retains_some_output:
  assumes "length ip = length op" and
    "out_star q_0 acc \<noteq> None"
  shows "out_star (process_output_query q_0 ip op) acc \<noteq> None"
proof -
  obtain r where
    lr: "q_0 = Node r"
    using obs_tree.exhaust
    by auto
  then have "otree_star q_0 acc \<noteq> None"
    using out_eq_otree[of r acc] assms
    by auto
  then have ot: "otree_star (process_output_query q_0 ip op) acc \<noteq> None"
    using output_query_retains_some assms
    by blast
  obtain r2 where
    "(process_output_query q_0 ip op) = Node r2"
    using obs_tree.exhaust
    by auto
  then have "out_star (process_output_query q_0 ip op) acc \<noteq> None"
    using otree_eq_out[of r2 acc] ot
    by auto
  then show ?thesis
    by simp
qed


lemma process_op_query_not_none_output:
  assumes "length ip = length op"
  shows "out_star (process_output_query (Node t) ip op) ip \<noteq> None"
proof -
  have ot: "otree_star (process_output_query (Node t) ip op) ip \<noteq> None"
    using output_query_retains_some assms process_op_query_not_none
    by blast
  obtain r2 where
    "(process_output_query (Node t) ip op) = Node r2"
    using obs_tree.exhaust
    by auto
  then have "out_star (process_output_query (Node t) ip op) ip \<noteq> None"
    using otree_eq_out[of r2] ot
    by (smt (verit) option.simps(4) out_eq_otree)
  then show ?thesis
    by simp
qed


lemma output_query_retains_some_specific:
  assumes "length ip = length op" and
    "otree_star (Node r) acc = Some (tr1,out1)" and
    "otree_star (process_output_query (Node r) ip op) acc = Some (tr2,out2)"
  shows "out1 = out2"
  text \<open>this is a stronger version of output_query_retains_some mostly used to prove that the invariant holds \<close>
using assms proof (induction acc arbitrary: ip op r tr1 tr2 out1 out2)
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
    obtain r2 outs where
      ra: "r a = Some (Node r2,outs)"
      using c otree_split option.exhaust
      by (metis obs_tree.exhaust old.prod.exhaust)
    then show ?thesis proof (cases "i = a")
      case True
      then have "otree_star (process_output_query (Node r) ip op) (a # acc) =
          otree_star (process_output_query (Node r) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = otree_star (case r i of
          None \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some (process_output_query (Node (\<lambda> k. None)) ilist olist,ops)
            else r j)) |
          Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j))) (a # acc)"
        using True ra
        by simp
      also have "\<dots> = otree_star (Node (\<lambda> j. if j = i
          then Some ((process_output_query (Node r2) ilist olist,outs))
          else r j)) (a # acc)"
        using ra
        by (simp add: True)
      also have "\<dots> = (case otree_star (process_output_query (Node r2) ilist olist) acc of
          Some (node,output) \<Rightarrow> Some (node,outs # output) |
          None \<Rightarrow> None)"
        using ra True
        by auto
      finally have calc1: "otree_star (process_output_query (Node r) ip op) (a # acc) =
          (case otree_star (process_output_query (Node r2) ilist olist) acc of
            Some (node,output) \<Rightarrow> Some (node,outs # output) |
            None \<Rightarrow> None)"
        by blast
      have "otree_star (process_output_query (Node r2) ilist olist) acc \<noteq> None"
        using calc1 c Cons True
        by (metis not_Some_eq option.simps(4))
      then obtain node1 outputs1 where
        n1: "otree_star (process_output_query (Node r2) ilist olist) acc = Some (node1,outputs1)"
        by fast
      have calc2: "otree_star (Node r) (a # acc) = (case otree_star (Node r2) acc of
          Some (node,output) \<Rightarrow> Some (node,outs # output) |
          None \<Rightarrow> None)"
        using c ra True
        by simp
      then have "otree_star (Node r2) acc \<noteq> None"
        using c
        by (metis not_Some_eq option.simps(4))
      then obtain node2 outputs2 where
        n2: "otree_star (Node r2) acc = Some (node2,outputs2)"
        by auto
      have "outputs1 = outputs2"
        using c.IH n1 n2 c(2) op Cons append1_eq_conv length_Cons
        by fastforce
      then show ?thesis
        using calc1 calc2 Cons c True
        by (simp add: n1 n2)
    next
      case False
      then have "otree_star (process_output_query (Node r) ip op) (a # acc) =
          otree_star (process_output_query (Node r) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = otree_star (case r i of
          None \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some (process_output_query (Node (\<lambda> k. None)) ilist olist,ops)
            else r j)) |
          Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j))) (a # acc)"
        using False ra
        by simp
      also have "\<dots> = (case otree_star (Node r2) acc of
          Some (node,output) \<Rightarrow> Some (node,outs # output) |
          None \<Rightarrow> None)"
        using ra
        apply (cases "r i")
        using False
        by auto
      also have "\<dots> = otree_star (Node r) (a # acc)"
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
    "out_star (Node r) acc = Some (out1)"
  shows "Some out1 = out_star (process_output_query (Node r) ip op) acc"
using assms proof (induction acc arbitrary: ip op r out1)
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
    obtain r2 outs where
      ra: "r a = Some (Node r2,outs)"
      using c out_split option.exhaust
      by (metis obs_tree.exhaust old.prod.exhaust)
    then show ?thesis proof (cases "i = a")
      case True
      then have "out_star (process_output_query (Node r) ip op) (a # acc) =
          out_star (process_output_query (Node r) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = out_star (case r i of
          None \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some ((process_output_query (Node (\<lambda> k. None)) ilist olist),ops)
            else r j)) |
          Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j))) (a # acc)"
        using True ra
        by simp
      also have "\<dots> = out_star (Node (\<lambda> j. if j = i
          then Some ((process_output_query (Node r2) ilist olist,outs))
          else r j)) (a # acc)"
        using ra
        by (simp add: True)
      also have "\<dots> = (case out_star (process_output_query (Node r2) ilist olist) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using ra True
        by auto
      finally have calc1: "out_star (process_output_query (Node r) ip op) (a # acc) =
          (case out_star (process_output_query (Node r2) ilist olist) acc of
            Some output \<Rightarrow> Some (outs # output) |
            None \<Rightarrow> None)"
        by blast
      have "out_star (process_output_query (Node r2) ilist olist) acc \<noteq> None"
        using calc1 c(3) Cons True output_query_retains_some_output
        by (metis c.prems(1) option.discI option.simps(4))
      then obtain outputs1 where
        n1: "out_star (process_output_query (Node r2) ilist olist) acc = Some (outputs1)"
        by fast
      have calc2: "out_star (Node r) (a # acc) = (case out_star (Node r2) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using c ra True
        by simp
      then have "out_star (Node r2) acc \<noteq> None"
        using c
        by (metis not_Some_eq option.simps(4))
      then obtain outputs2 where
        n2: "out_star (Node r2) acc = Some (outputs2)"
        by auto
      have "outputs1 = outputs2"
        using c.IH n1 n2 c(2) op Cons append1_eq_conv length_Cons
        by fastforce
      then show ?thesis
        using calc1 calc2 Cons c True
        by (simp add: n1 n2)
    next
      case False
      then have "out_star (process_output_query (Node r) ip op) (a # acc) =
          out_star (process_output_query (Node r) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op
        by presburger
      also have "\<dots> = out_star (case r i of
            None \<Rightarrow> (Node (\<lambda> j. if j = i
              then Some (process_output_query (Node (\<lambda> k. None)) ilist olist,ops)
              else r j)) |
            Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
              then Some ((process_output_query tree ilist olist),out)
              else r j)))
          (a # acc)"
        using False ra
        by simp
      also have "\<dots> = (case out_star (Node r2) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using ra
        apply (cases "r i")
        using False
        by auto
      also have "\<dots> = out_star (Node r) (a # acc)"
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
  shows "out_star (process_output_query (Node t) (i # is) (op # ops)) (j # js) = out_star (Node t) (j # js)"
proof -
  have "(process_output_query (Node t) (i # is) (op # ops)) = (case t i of
      None \<Rightarrow> (Node (\<lambda> j. if j = i
        then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
        else t j)) |
      Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
        then Some ((process_output_query tree is ops),out)
        else t j)))"
    by simp
  then show ?thesis proof (cases "t i")
    case None
    then have eq: "(process_output_query (Node t) (i # is) (op # ops)) =
        (Node (\<lambda> j. if j = i
          then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
          else t j))"
      by simp
    have "out_star (Node (\<lambda> j. if j = i
          then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
          else t j)) (j # js) =
        out_star (Node t) (j # js)"
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
    then have eq: "(process_output_query (Node t) (i # is) (op # ops)) =
        (Node (\<lambda> j. if j = i
          then Some ((process_output_query tree is ops),out)
          else t j))"
      using Some
      by fastforce
    have "out_star (Node (\<lambda> j. if j = i
          then Some ((process_output_query tree is ops),out)
          else t j)) (j # js) =
        out_star (Node t) (j # js)"
      using assms
      by auto
    then show ?thesis
      using eq
      by argo
  qed
qed


lemma substring_different_query:
  assumes "out_star T i = None" and
    "length j = length out" and
    "out_star (process_output_query T j out) i \<noteq> None"
  shows "\<exists> y. j = i @ y"
using assms proof (induction i arbitrary: out j T)
  case Nil
  then show ?case
    by blast
next
  case (Cons a i)
  obtain t where
    node: "T = Node t"
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
            (Node (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
              else t j))"
          using node None
          by auto
        then have "out_star (process_output_query T (jfront # js) (op # os)) (a # i) =
            out_star (Node (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
              else t j)) (a # i)"
          by force
        also have b: "\<dots> = (case (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
              else t j) a of
            Some (n,op) \<Rightarrow>
            (case (out_star n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None)"
          by auto
        also have c: "\<dots> =
            (case (out_star (process_output_query (Node (\<lambda> k. None)) js os) i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None)"
          using eq
          by auto

        have induc_three: "(out_star (process_output_query (Node (\<lambda> k. None)) js os) i) \<noteq> None"
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
          then have "(out_star (Node (\<lambda> k. None)) i) = (case (\<lambda> k. None) ifront of
              Some (n,op) \<Rightarrow>
              (case (out_star n is) of
                Some ops \<Rightarrow> Some (op # ops) |
                None \<Rightarrow> None) |
              None \<Rightarrow> None)"
            by simp
          then have induc_one: "(out_star (Node (\<lambda> k. None)) i) = None"
            by auto
          show ?thesis
            using Cons.IH[of "Node (\<lambda> k. None)" js os] induc_one induc_two induc_three eq j
            by auto
        qed
      next
        case (Some b)
        obtain atree aout where
          atree: "b = (atree,aout)"
          by (metis surj_pair)
        then have proc: "(process_output_query T (jfront # js) (op # os)) =
            Node (\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j)"
          using node Some
          by auto
        then have "out_star (process_output_query T (jfront # js) (op # os)) (a # i) =
            out_star (Node (\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j)) (a # i)"
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
  assumes "out_star T i = None" and
    "trans_star_output t q_0 j = out" and
    "T' = process_output_query T j out" and
    "\<forall> k y. out_star T k = Some y \<longrightarrow> trans_star_output t q_0 k = y"
  shows "out_star T' i \<noteq> None \<longrightarrow> out_star T' i = Some (trans_star_output t q_0 i)"
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
    obtain f where
      T: "T = Node f"
      using obs_tree.exhaust
      by auto
    obtain f' where
      T': "T' = Node f'"
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
      have query: "process_output_query (Node f) (b # js) (op # os) = (Node (\<lambda> k. if k = b
          then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
          else f k))"
        using Cons None eq
        by auto
      have "out_star T' (a # i) = out_star (process_output_query (Node f) (b # js) (op # os)) (a # i)"
        using Cons j out T
        by argo
      also have "\<dots> = out_star (Node (\<lambda> k. if k = b
          then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
          else f k)) (a # i)"
        using query
        by argo
      also have "\<dots> = (case (\<lambda> k. if k = b
            then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
            else f k) a of
          Some (n,op) \<Rightarrow>
          (case (out_star n i) of
            Some ops \<Rightarrow> Some (op # ops) |
            None \<Rightarrow> None) |
          None \<Rightarrow> None)"
        by simp
      also have "\<dots> = (case (out_star (process_output_query (Node (\<lambda> k. None)) js os) i) of
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
        have ih_prem2: "out_star (Node (\<lambda> k. None)) i = None"
          using Cons
          by fastforce
        obtain T'' where
          T'': "T'' = process_output_query (Node (\<lambda> k. None)) js os"
          by simp
        have ih_prem4: "\<forall> k y. out_star (Node (\<lambda> k. None)) k = Some y \<longrightarrow> trans_star_output t q' k = y"
          by (metis Cons.prems(5) list.exhaust out_split out_star.simps(1) trans_star_output.simps(1))
        have "(out_star T'' i) \<noteq> None \<longrightarrow>
            (out_star T'' i) = Some (trans_star_output t q' i)"
          using Cons.IH[of js "Node (\<lambda> k. None)" q' os T''] ih_prem1 ih_prem2 ih_prem3
          using ih_prem4 T'' ih_prem5
          by blast
        then have "(out_star (process_output_query (Node (\<lambda> k. None)) js os) i) \<noteq> None \<longrightarrow>
            (out_star (process_output_query (Node (\<lambda> k. None)) js os) i) = Some (trans_star_output t q' i)"
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
      have query: "process_output_query (Node f) (b # js) (op # os) =
          (Node (\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j))"
        using eq nextnode Some
        by auto
      then have a: "out_star (process_output_query (Node f) (b # js) (op # os)) (a # i) =
          out_star (Node (\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j)) (a # i)"
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
        using Cons.IH[of js nextnode q' os "process_output_query nextnode js os"]
      ih_prem1 ih_prem2 ih_prem3 ih_prem4 ih_prem5 T'' nextnode Some
        by argo
      then show ?thesis
        using Cons.prems(4) T c calculation j nextout_eq_out' option.simps(4) out part2
        by auto
    qed
  qed
qed


lemma output_query_keeps_invar:
  assumes "out_star T i = None" and
    "output_query m j = out" and
    "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
  shows "out_star (process_output_query T j out) i \<noteq> None \<longrightarrow> out_star (process_output_query T j out) i = Some (output_query m i)"
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
    "apart T s1 s2"
  shows "apart (process_output_query T ip op) s1 s2"
    using output_query_retains_some_specific_output assms
    by (smt (verit,ccfv_SIG) apart.simps length_0_conv process_output_query.elims process_output_query.simps(1))


lemma proc_output_query_retains_sapart:
  assumes "length ip = length op" and
    "sapart (S,F,T)"
  shows "sapart (S,F,(process_output_query T ip op))"
    using proc_output_query_retains_apart assms
    by (metis sapart.simps)


section \<open>norm\<close>


lemma norm_max:
  assumes "invar m (S,F,T)"
  shows "norm (S,F,T) \<le>
      (card S * (card S + 1)) div 2 + (card S * card I) + (card S * (card S * card I))"
  text \<open>this shows that the norm is always smaller as some term that only changes though the size of \<open>S\<close>\<close>
proof -
  have fst: "norm_fst (S,F,T) = (card S * (card S + 1) div 2)"
    by simp
  have fin_snd: "finite (S \<times> I)"
    using assms invars(3)
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
  have "\<forall> f \<in> F. \<exists> s \<in> S. \<exists> i. f = s @ [i]"
    using assms
    by (smt (verit) in_F.simps invars)
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
  have subs_trd: "{(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<subseteq> (S \<times> F)"
    by blast
  have "finite (S \<times> F)"
    using assms invars(3,4)
    by blast
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
  have c: "\<forall> acc is ops.
      trans_star transmealy (fst (trans_star transmealy q_0 acc)) is =
      (fst (trans_star transmealy q_0 (acc @ is)),drop (length acc) (snd (trans_star transmealy q_0 (acc @ is))))"
    using trans_star_two_nested
    by fast
  then have "\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow> ops = output_query m (acc @ is)"
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
  finally have calc: "\<forall> acc is ops. out_star T (acc @ is) = Some ops \<longrightarrow>
      trans_star transmealy (f acc) is = (f (acc @ is),(drop (length acc) ops))"
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
  have "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart T s1 s2"
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
  shows "card S \<le> card Q"
  text \<open>this shows that \<open>S\<close> also has an upper bound, this not at maximum accuracy,
    as we know @{term "card S"} is smaller than the number of equivalence classes of \<open>m\<close>\<close>
proof -
  have "\<exists> f. func_sim m T f"
    using assms
    using func_sim_of_output_query invars(6) by fastforce
  then obtain f where
    a: "func_sim m T f"
    by auto
  have b: "sapart (S,F,T)"
    using assms invars
    by presburger
  have c: "finite S"
    using assms invars
    by blast
  then show ?thesis
    using max_size_S_aux a b c univQ
    by blast
qed


theorem max_norm_total:
  assumes "invar m (S,F,T)"
  shows "norm (S,F,T) \<le> (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))"
  text  \<open>this theorem is equivalent to theorem 3.9 in the L# Paper.\<close>
proof (rule ccontr)
  assume "\<not> norm (S,F,T) \<le> (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))"
  then have "(card S * (card S + 1) div 2 + card S * card I + card S * (card S * card I)) >
      (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))"
    using norm_max assms
    by force
  then have "card S > card Q"
    using assms
    by (metis add_le_cancel_right add_mono div_le_mono linorder_not_le mult_le_mono mult_le_mono1)
  then show False
    using max_size_S assms
    by fastforce
qed


lemma norm_trd_subs:
  assumes "F \<subseteq> Fnew" and
    "finite Fnew" and
    "finite S"
  shows "norm_trd (S,F,T) \<le> norm_trd (S,Fnew,T)"
using assms proof -
  have fin_start: "finite {(q,p). q \<in> S \<and> p \<in> Fnew}"
    using assms
    by auto
  have "{(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p} \<subseteq> {(q,p). q \<in> S \<and> p \<in> Fnew}"
    by blast
  then have finite: "finite {(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p}"
    using fin_start finite_subset
    by blast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<subseteq> {(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p}"
    using assms
    by blast
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<le>
      card{(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p}"
    using finite card_mono
    by blast
  then show ?thesis
    by auto
qed


section \<open>algo_step\<close>


lemma sapart_extends:
  assumes "sapart (S,F,T)" and
    "\<forall> s \<in> S. apart T s f"
  shows "sapart (S \<union> {f},F2,T)"
proof -
  have a: "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart T s1 s2"
    using assms
    by simp
  have b: "\<forall> s1 \<in> S. s1 \<noteq> f \<longrightarrow> apart T f s1"
    using assms
    by fastforce
  have c: "\<forall> s1 \<in> S. s1 \<noteq> f \<longrightarrow> apart T s1 f"
    using assms
    by fastforce
  show ?thesis
    using a b c
    by auto
qed


lemma substr_not_s:
  assumes "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)" and
    "x \<notin> S" and
    "s = x @ y"
  shows "s \<notin> S"
using assms proof (induction y arbitrary: s rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc y ys)
  then have "x @ ys \<notin> S"
    by blast
  then have "x @ ys @ [y] \<notin> S"
    using snoc
    by (metis Nil_is_append_conv append1_eq_conv append_assoc)
  then show ?case
    by (simp add: snoc.prems(3))
qed


lemma substring_in_s:
  assumes "[] \<in> S" and
    "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)" and
    "s \<in> S" and
    "s = x @ y"
  shows "x \<in> S"
    using substr_not_s assms
    by blast


lemma algo_step_keeps_invar:
  assumes "algo_step m (S,F,T) (S',F',T')" and
    "invar m (S,F,T)"
  shows "invar m (S',F',T')"
  text \<open>this lemma shows that algo steep keeps the invariant, this proof works over each rule and proves each part of the invariant seperatly.\<close>
using assms proof (induction rule: algo_step.induct)
  case (rule1 f F S T)
  have finS: "finite (S \<union> {f})"
    using rule1 invars
    by fast
  then have finF: "finite {fnew. in_F (S \<union> {f},F,T) fnew}"
    using finiteF
    by presburger

  have a: "\<forall> e. \<not> (e \<in> S \<union> {f} \<and> e \<in> {fnew. in_F (S \<union> {f},F,T) fnew})"
    by force
  have b: "\<forall> e \<in> S \<union> {f}. out_star T e \<noteq> None"
    using rule1 invars
    by (metis UnE in_F.simps singletonD)
  have c: "sapart (S \<union> {f},{fnew. in_F (S \<union> {f},F,T) fnew},T)"
    using rule1 sapart_extends invars
    by metis
  have d: "\<forall> i. out_star T i \<noteq> None \<longrightarrow> out_star T i = Some (output_query m i)"
    using rule1 invars
    by metis
  have e: "\<forall> fs \<in> {fnew. in_F (S \<union> {f},F,T) fnew}. in_F (S \<union> {f},F,T) fs"
    by blast
  have f: "\<forall> fs. in_F (S \<union> {f},F,T) fs \<longrightarrow> fs \<in> {fnew. in_F (S \<union> {f},F,T) fnew}"
    by fast
  have g: "[] \<in> S \<union> {f}"
    using rule1 invars
    by fast
  have "\<forall> s \<in> S \<union> {f}. s = [] \<or> (\<exists> s2 \<in> S \<union> {f}. \<exists> i. s2 @ [i] = s)"
    using rule1 invars
    by (metis Un_iff in_F.simps singleton_iff)
  then show ?case
    using finF finS a b c d e f g is_invar[of "S \<union> {f}" "{fnew. in_F (S \<union> {f},F,T) fnew}" T]
    by auto
next
  case (rule2 s S T i out F)
  have finiteS: "finite S"
    using rule2 invars
    by blast
  have finiteF: "finite (F \<union> {s @ [i]})"
    using rule2 invars
    by blast
  have lens: "length (s @ [i]) = length out"
    using rule2 output_query_length
    by blast
  have a: "\<forall> e. \<not> (e \<in> S \<and> e \<in> (F \<union> {s @ [i]}))"
    using rule2 invars
    by blast
  have out_starS: "\<forall> e \<in> S. out_star T e \<noteq> None"
    using rule2
    by (metis invars(2))
  then have b: "\<forall> e \<in> S. out_star (process_output_query T (s @ [i]) out) e \<noteq> None"
    using lens output_query_retains_some_output
    by metis
  have c: "sapart (S,(F \<union> {s @ [i]}),process_output_query T (s @ [i]) out)"
    using lens rule2 proc_output_query_retains_sapart invars
    by (metis sapart.simps)
  have "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
    using rule2
    by (metis invars(6) option.discI option.inject)
  then have d: "\<forall> j. out_star (process_output_query T (s @ [i]) out) j \<noteq> None \<longrightarrow>
      out_star (process_output_query T (s @ [i]) out) j = Some (output_query m j)"
    using rule2 output_query_keeps_invar[of T "s @ [i]" "s @ [i]" out]
    by (smt (verit) invars lens out_star.elims output_query_keeps_invar output_query_retains_some_specific_output)
  have e_fst: "\<forall> f \<in> F. in_F (S,F,(process_output_query T (s @ [i]) out)) f"
    by (metis in_F.simps invars(1,7) lens output_query_retains_some_output rule2.prems)
  have e_snd: "in_F (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) (s @ [i])"
    using rule2 out_starS
    by (smt (verit) in_F.simps lens out_star.elims process_op_query_not_none_output)
  have e: "\<forall> f \<in> F \<union> {s @ [i]}. in_F (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) f"
    using e_fst e_snd
    by fastforce
  have s_not_none: "out_star T s \<noteq> None"
    using out_starS rule2
    by blast
  then have subs_s_not_None: "\<forall> is. \<exists> y. is @ y = s \<longrightarrow> out_star T is \<noteq> None"
    using out_star_substring_not_none
    by fast
  then have something: "\<forall> is. (\<exists> y. is @ y = s @ [i]) \<and> \<not> (\<exists> y. is @ y = s) \<longrightarrow> is = s @ [i]"
    by (metis append_self_conv butlast_append butlast_snoc)
  have "\<forall> is. out_star T is = None \<and> out_star (process_output_query T (s @ [i]) out) is \<noteq> None \<longrightarrow> (\<exists> y. is @ y = (s @ [i]))"
    using substring_different_query lens
    by metis
  then have only_si_different: "\<forall> is. out_star T is = None \<and> out_star (process_output_query T (s @ [i]) out) is \<noteq> None \<longrightarrow> is = (s @ [i])"
    using subs_s_not_None something
    by (metis out_star_substring_not_none s_not_none)
  have finF: "\<forall> f. in_F (S,F,T) f \<longrightarrow> f \<in> F"
    using rule2 invars
    by fast
  then have "{f. in_F (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) f} \<supseteq> {f. in_F (S,F,T) f} \<union> {s @ [i]}"
    by (smt (verit) Un_iff e mem_Collect_eq subsetI)
  have "\<forall> f. in_F (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) f \<longrightarrow> in_F (S,F \<union> {s @ [i]},T) f \<or> f = (s @ [i])" apply simp
    using only_si_different
    by fastforce
  then have f: "\<forall> f. in_F (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) f \<longrightarrow> f \<in> (F \<union> {s @ [i]})"
    using finF
    by auto
  have g: "[] \<in> S"
    using rule2 invars
    by fast
  have h: "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
    using rule2 invars
    by metis
  show ?case
    using a b finiteF finiteS c d e f g h is_invar
    by blast
next
  case (rule3 s1 S s2 f F T w out)
  have lens: "length (f @ w) = length out"
    using rule3 output_query_length
    by blast
  have finS: "finite S"
    using rule3 invars
    by blast
  have finF: "finite F"
    using rule3 invars
    by fast

  have a: "\<forall> e. \<not> (e \<in> S \<and> e \<in> F)"
    using rule3
    by (meson invars)
  have b: "\<forall> e \<in> S. out_star (process_output_query T (f @ w) out) e \<noteq> None"
    using rule3
    by (metis invars(2) lens output_query_retains_some_output)

  have c: "sapart (S,F,process_output_query T (f @ w) out)"
    using lens rule3 proc_output_query_retains_sapart invars
    by metis
  have helper: "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
    using rule3
    by (metis invars(6) option.discI option.inject)
  then have d: "\<forall> j. out_star (process_output_query T (f @ w) out) j \<noteq> None \<longrightarrow>
      out_star (process_output_query T (f @ w) out) j = Some (output_query m j)"
    using rule3 output_query_keeps_invar
    by (smt (verit,del_insts) invars lens out_star.elims output_query_retains_some_specific_output)

  have e: "\<forall> fs \<in> F. in_F (S,F,(process_output_query T (f @ w) out)) fs"
    using rule3 invars
    by (metis Mealy.output_query_retains_some_output Mealy_axioms in_F.simps lens)
  have "\<forall> fs. in_F (S,F,T) fs \<longrightarrow> fs \<in> F"
    using invars(8) rule3.prems(1)
    by auto
  have "\<forall> fs. in_F (S,F,T) fs \<longrightarrow> in_F (S,F,(process_output_query T (f @ w) out)) fs"
    using e invars(8) rule3.prems(1)
    by blast
  have notnone_subs: "\<forall> s \<in> S. \<forall> i. out_star T (s @ [i]) = None \<and> out_star (process_output_query T (f @ w) out) (s @ [i]) \<noteq> None \<longrightarrow> (\<exists> y. (s @ [i] @ y = (f @ w)))"
    using substring_different_query[of T _ "f @ w" out] lens
    by (metis append_assoc)
  have "\<forall> y. f @ y \<notin> S"
    using a invars(10) rule3.hyps(4) rule3.prems(1)
    by (meson substr_not_s)
  then have ins_subs_f: "\<forall> s \<in> S.(\<exists> y. s @ y = f @ w) \<longrightarrow> (\<exists> y. s @ y = f)"
    by (metis append_eq_append_conv2)
  then have "\<forall> s \<in> S. \<forall> i. \<exists> y. s @ [i] @ y = f @ w \<longrightarrow> otree_star T (s @ [i]) \<noteq> None"
    by (metis append_assoc append_self_conv2 list.distinct(1))
  then have "\<forall> s \<in> S. \<forall> i. out_star T (s @ [i]) = None \<and> out_star (process_output_query T (f @ w) out) (s @ [i]) \<noteq> None \<longrightarrow> \<not> (\<exists> y. s @ [i] @ y = f @ w)"
    by (metis (no_types,opaque_lifting) Cons_eq_appendI append_eq_append_conv2 in_F.simps ins_subs_f
    invars(7) list.inject neq_Nil_conv out_star_substring_not_none rule3.hyps(4) rule3.prems(1) same_append_eq)
  then have "\<forall> s \<in> S. \<forall> i. out_star T (s @ [i]) = None \<longrightarrow> out_star (process_output_query T (f @ w) out) (s @ [i]) = None"
    using notnone_subs
    by blast
  then have "\<forall> fs. in_F (S,F,(process_output_query T (f @ w) out)) fs \<longrightarrow> in_F (S,F,T) fs"
    by fastforce
  then have f: "\<forall> fs. in_F (S,F,(process_output_query T (f @ w) out)) fs \<longrightarrow> fs \<in> F"
    using rule3 invars(8)
    by blast
  have ins: "[] \<in> S"
    using rule3 invars
    by fast
  have g: "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
    using rule3 invars
    by metis
  show ?case
    using a b finS finF c d e f g ins is_invar[of S F "process_output_query T (f @ w) out"]
    by blast
next
  case (rule4 S T F fs s inp outs outf)
  have lens: "length (s @ inp) = length outs"
    using rule4 output_query_length
    by blast
  have lenf: "length (fs @ inp) = length outf"
    using rule4 output_query_length
    by blast
  have a: "\<forall> e. \<not> (e \<in> S \<and> e \<in> {fnew. in_F (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)) fnew})"
    by force
  have b: "\<forall> e \<in> S. out_star (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) e \<noteq> None"
    using rule4
    by (metis lenf lens out_star_substring_not_none output_query_retains_some_output)

  have c: "sapart (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf))"
    using lens lenf rule4 proc_output_query_retains_sapart invars
    by metis
  have "\<forall> k y. out_star T k = Some y \<longrightarrow> output_query m k = y"
    using rule4
    by (metis invars(6) option.discI option.inject)
  then have "\<forall> j. out_star (process_output_query T (s @ inp) outs) j \<noteq> None \<longrightarrow>
      out_star (process_output_query T (s @ inp) outs) j = Some (output_query m j)"
    using rule4 output_query_keeps_invar
    by (smt (verit,del_insts) invars lens out_star.elims output_query_retains_some_specific_output)
  then have d: "\<forall> j. out_star (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) j \<noteq> None \<longrightarrow>
      out_star (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) j = Some (output_query m j)"
    using rule4 output_query_keeps_invar[of "process_output_query T (s @ inp) outs" _"fs @ inp" "outf"]
    by (smt (verit) lenf option.discI option.inject out_star.elims output_query_retains_some_specific_output process_output_query.simps(1))
  have never_none: "\<forall> ses \<in> S. \<forall> i. out_star T (ses @ [i]) \<noteq> None"
    using rule4
    by blast
  have feq_aux: "\<forall> f \<in> F. f \<in> {fs. in_F (S,F,T) fs}"
    using rule4 invars
    by (metis mem_Collect_eq)
  have "\<forall> f \<in> {fs. in_F (S,F,T) fs}. f \<in> F"
    using rule4 invars
    by (metis mem_Collect_eq)
  then have feq: "F = {f. in_F (S,F,T) f}"
    using feq_aux
    by blast
  have inf_eq: "{f. in_F (S,F,T) f} = {f. ((\<exists> s \<in> S. \<exists> i. f = s @ [i]) \<and> f \<notin> S)}"
    using never_none
    by auto
  have infnew_eq: "{f. ((\<exists> s \<in> S. \<exists> i. f = s @ [i]) \<and> f \<notin> S)} =
      {f. in_F (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)) f}"
    using never_none output_query_retains_some_output
    by (metis (mono_tags,lifting) in_F.simps lenf lens)
  then have e: "\<forall> f \<in> F. in_F (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)) f"
    using feq inf_eq
    by auto
  have f: "\<forall> f. in_F (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)) f
      \<longrightarrow> f \<in> {fnew. in_F (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)) fnew}"
    using inf_eq infnew_eq
    by fast
  then show ?case
    using rule4 a b c d e f is_invar
    by (smt (verit) feq inf_eq infnew_eq invars)
qed


theorem algo_step_increases_norm:
  assumes "algo_step m ((S :: 'input list set),F,T) (S',F',T')" and
    "invar m (S,F,T)"
  shows "norm (S,F,T) < norm (S',F',T')"
  text \<open>this theorem is equivalent to Theorem 3.8 in the original L# Paper
    for each rule this proof is divided into three parts, for two of the norms it shows that they are not smaller
for one that it is bigger, this is similar to the proof of the original Paper.
  since we argue about cardinalities we work a lot with card_mono\<close>
using assms proof (induction "(S,F,T)" "(S',F',T')" rule: algo_step.induct)
  case (rule1 f)
  have finS: "finite S"
    using rule1 invars
    by blast
  have finI: "finite I"
    by fastforce
  have finF: "finite F"
    using rule1 invars
    by fast
  have "norm_fst (S,F,T) \<le> norm_fst (S \<union> {f},Collect (in_F (S \<union> {f},F,T)),T)"
    by (simp add: add_mono card_insert_le div_le_mono mult_le_mono)
  have "f \<notin> S"
    using rule1 invars
    by metis
  then have "norm_fst (S,F,T) + (card S + 1) \<le> norm_fst (S \<union> {f},Collect (in_F (S \<union> {f},F,T)),T)"
    using finS
    by auto
  then have fst: "norm_fst (S,F,T) + (card S + 1) \<le> norm_fst (S',F',T')"
    using rule1
    by argo

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
  then have "norm_snd (S,F,T) \<le> norm_snd (S \<union> {f},Collect (in_F (S \<union> {f},F,T)),T)"
    using fin2 card_mono
    by fastforce
  then have snd: "norm_snd (S,F,T) \<le> norm_snd (S',F',T')"
    using rule1
    by fast

  have finSF: "finite {(q,p). (q \<in> S \<or> q = f) \<and> p \<in> F}"
    using finS finF
    by simp
  have "{(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p} \<subseteq>
      {(q,p). (q \<in> S \<or> q = f) \<and> p \<in> F}"
    by blast
  then have fin3: "finite {(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p}"
    using finSF finite_subset
    by fast
  have "{(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p} \<supseteq>
      {(q,p). (q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p}"
    by blast
  also have c1: "\<dots> \<supseteq> {(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - {(p,q). p \<in> S \<and> q = f}"
    by auto
  have s_cross_eq: "{(p,q). p \<in> S \<and> q = f} = (S \<times> {f})"
    using rule1
    by blast
  then have "card (S \<times> {f}) = card S * card {f}"
    using card_cartesian_product
    by fast
  then have "card (S \<times> {f}) = card S"
    by force
  then have card_eq: "card {(p,q). p \<in> S \<and> q = f} = card S"
    using rule1 s_cross_eq
    by argo
  have "\<forall> fs \<in> F. f \<noteq> fs \<longrightarrow> (in_F (S,F,T) fs)"
    using rule1 invars
    by meson
  then have "\<forall> fs \<in> F. f \<noteq> fs \<longrightarrow> (in_F (S \<union> {f},F,T) fs)"
    by fastforce
  then have fminus_subs: "F - {f} \<subseteq> Collect (in_F (S \<union> {f},F,T))"
    by fast
  have "(S \<times> {f}) = {(p,q). p \<in> S \<and> q = f}"
    by simp
  then have "finite {(p,q). p \<in> S \<and> q = f}"
    using finS
    by simp
  then have le1: "card {(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - card {(p,q). p \<in> S \<and> q = f}
      \<le> card ({(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - {(p,q). p \<in> S \<and> q = f})"
    using diff_card_le_card_Diff
    by blast
  have le2: "card ({(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - {(p,q). p \<in> S \<and> q = f}) \<le>
      card ({(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p})"
    using calculation fin3 card_mono c1
    by meson
  have "norm_trd (S \<union> {f},F - {f},T) \<ge> card {(q,p). (q \<in> S) \<and> p \<in> F \<and>
      apart T q p} - card {(p,q). p \<in> S \<and> q = f}"
    using le1 le2
    by simp
  then have "norm_trd (S \<union> {f},F - {f},T) \<ge> norm_trd (S,F,T) - card {(p,q). p \<in> S \<and> q = f}"
    by simp
  then have "norm_trd (S \<union> {f},F - {f},T) \<ge> norm_trd (S,F,T) - card S"
    using rule1 card_eq
    by argo
  then have "norm_trd (S \<union> {f},Collect (in_F (S \<union> {f},F,T)),T) \<ge> norm_trd (S,F,T) - card S"
    using norm_trd_subs fminus_subs
    by (smt (verit) dual_order.trans finS finite.emptyI finite.insertI finiteF infinite_Un)
  then have trd: "norm_trd (S,F,T) - card S \<le> norm_trd (S',F',T')"
    using rule1
    by fast

  then show ?case
    using fst snd trd
    by simp
next
  case (rule2 s i out)
  have finS: "finite S"
    using rule2 invars
    by blast
  have finS': "finite S'"
    using rule2 invars
    by blast
  have finI: "finite I"
    by fastforce
  have finF: "finite F"
    using rule2 invars
    by blast
  then have finF': "finite F'"
    using rule2
    by blast
  have fst: "norm_fst (S,F,T) = norm_fst (S',F',T')"
    apply simp
    using rule2(4)
    by fastforce

  have lens: "length (s @ [i]) = length out"
    using output_query_length rule2.hyps(3)
    by blast
  then have a: "out_star T' (s @ [i]) \<noteq> None"
    using process_op_query_not_none_output rule2
    by (metis obs_tree.exhaust)
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
    by (smt (verit) all_not_in_conv case_prodE mem_Collect_eq not_None_eq)
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
    using rule2(4)
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
  obtain r where
    lr: "T = Node r"
    using obs_tree.exhaust
    by auto
  have front: "\<forall> p x i2. out_star (Node r) (p @ i2) = Some x \<longrightarrow>
      out_star (process_output_query (Node r) (s @ [i]) out) (p @ i2) = Some x"
    using rule2(6) lens output_query_retains_some_specific_output[of "s @ [i]" out r]
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
  case (rule3 s1 s2 f w out)
  have fst: "norm_fst (S,F,T) = norm_fst (S',F',T')"
    using rule3(9)
    by fastforce

  have lens: "length (f @ w) = length out"
    using output_query_length rule3
    by blast
  have retain: "\<forall> is. out_star T is \<noteq> None \<longrightarrow> out_star T' is \<noteq> None"
    using rule3 lens output_query_retains_some_output
    by blast
  then have retain_specific: "\<forall> is x. out_star T is = Some x \<longrightarrow> out_star T' is = Some x"
    using output_query_retains_some_specific_output rule3 lens
    by (smt (verit) not_none_not_both_apart out_star.elims)
  have "finite S"
    using rule3(12) invars
    by blast
  then have finp: "finite (S \<times> I)"
    using univI
    by simp

  have "{(q,i). q \<in> S \<and> i \<in> I} = S \<times> I"
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp
    by argo
  have "{(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)} \<subseteq> {(q,i). q \<in> S \<and> i \<in> I}"
    using rule3 univI
    by fast
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
    by (meson finite_SigmaI invars)
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p}"
    using fincross finite_subset
    by fast
  then have split: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} =
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}
      \<union> {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    using rule3
    by fast
  then have fin3_subs: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    using fin3 finite_subset
    by simp
  obtain z where
    z: "out_star T' (f @ w) = Some z"
    using rule3 lens
    by (metis not_None_eq obs_tree.exhaust process_op_query_not_none_output)
  have "apart_witness T' s1 s2 w"
    using retain_specific rule3(7)
    by auto
  then have apart_or: "apart T' s1 f \<or> apart T' s2 f"
    using not_none_not_both_apart rule3 z
    by (smt (z3) apart.elims(3) apart_witness.simps)
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p} \<inter>
      {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p} = {}"
    by blast
  then have card_splitup: "card {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} =
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p} +
      card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p})"
    using split fin3 card_Un_disjoint
    by fastforce
  have fin_subs_part: "finite {(q,p). ((q = s2 \<or> q = s1) \<and> p = f)}"
    by simp
  have "{(q,p). ((q = s2 \<or> q = s1) \<and> p = f)} \<supseteq> {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    by fast
  then have fin_part_three: "finite {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    using fin_subs_part finite_subset
    by fast
  have union: "{(q,p). ((q = s2) \<and> p = f) \<and> apart T' q p} \<union> {(q,p). ((q = s1) \<and> p = f) \<and> apart T' q p} =
      {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    by fast
  have "({(q,p). ((q = s2) \<and> p = f) \<and> apart T' q p} = {(s2,f)}) \<or>
      ({(q,p). ((q = s1) \<and> p = f) \<and> apart T' q p} = {(s1,f)})"
    using apart_or
    by force
  then have "(card {(q,p). ((q = s2) \<and> p = f) \<and> apart T' q p} = 1) \<or> (card {(q,p). ((q = s1) \<and> p = f) \<and>
      apart T' q p} = 1)"
    by force
  then have card_not_zero: "card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}) \<ge> 1"
    using union
    by (metis (no_types,lifting) Un_upper1 Un_upper2 card_mono fin_part_three)
  have equal_first_half: "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T q p} = {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p}"
    using rule3(5,6)
    by auto
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T q p} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    apply simp
    using retain_specific rule3
    by blast
  then have "{(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    using equal_first_half
    by argo
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<le>
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    using fin3_subs card_mono
    by meson
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} <
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p} +
      card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p})"
    using card_not_zero
    by simp
  then have trd: "norm_trd (S,F,T) < norm_trd (S',F',T')"
    using card_splitup
    by auto

  show ?case
    using fst snd trd
    by fastforce
next
  case (rule4 fs s inp outs outf)
  then have fst: "norm_fst (S,F,T) = norm_fst (S',F',T')"
    using rule4(8,9)
    by auto

  have lens: "length (s @ inp) = length outs"
    using output_query_length rule4
    by blast
  have lenf: "length (fs @ inp) = length outf"
    using output_query_length rule4
    by blast
  have retain: "\<forall> is. out_star T is \<noteq> None \<longrightarrow> out_star T' is \<noteq> None"
    using rule4 lens lenf output_query_retains_some_output
    by blast
  then have retain_specific: "\<forall> is x. out_star T is = Some x \<longrightarrow> out_star T' is = Some x"
    using output_query_retains_some_specific_output rule4 lens lenf
    by (smt (verit,ccfv_SIG) out_star.elims out_star.simps(1))
  have finp: "finite ({q. q \<in> S} \<times> {i. i \<in> I})"
    using rule4
    by (metis Collect_mem_eq finite_SigmaI finite_code invars(3))
  have "{(q,i). q \<in> S \<and> i \<in> I} = {q. q \<in> S} \<times> {i. i \<in> I}"
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp
    by argo
  have "{(q,i). q \<in> S' \<and> (\<exists> y. out_star T' (q @ [i]) = Some y)} \<subseteq> {(q,i). q \<in> S \<and> i \<in> I}"
    using rule4 univI
    by blast
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

  have invar: "invar m (S',F',T')"
    using rule4 algo_step_keeps_invar algo_step.rule4
    by metis
  have "\<exists> x. out_star T' (s @ inp) = Some x"
    by (metis lenf lens not_Some_eq obs_tree.exhaust
    output_query_retains_some_output process_op_query_not_none_output rule4.hyps(11))
  then obtain new_outs where
    new_outs: "out_star T' (s @ inp) = Some new_outs"
    by fast
  have "\<exists> y. out_star T' (fs @ inp) = Some y"
    using process_op_query_not_none_output
    by (metis lenf not_Some_eq obs_tree.exhaust rule4.hyps(11))
  then obtain new_outf where
    new_outf: "out_star T' (fs @ inp) = Some new_outf"
    by fast
  have query_s: "new_outs = (output_query m (s @ inp))"
    using invar new_outs invars(6)
    by fastforce
  have query_fs: "new_outf = (output_query m (fs @ inp))"
    using invar new_outf invars
    by (metis not_None_eq option.inject)
  have "drop (length s) (output_query m (s @ inp)) \<noteq>
      drop (length fs) (output_query m (fs @ inp))"
    using rule4 difference_query_def
    by (metis output_query.elims output_query.simps)
  then have "drop (length s) new_outs \<noteq> drop (length fs) new_outf"
    using rule4 query_s query_fs
    by argo
  then have apart_s_fs: "apart T' s fs"
    using new_outs new_outf
    by auto
  have fincross: "finite (S' \<times> F')"
    using rule4 invars(3) invars(4)
    by blast
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p}"
    using fincross finite_subset
    by fast
  have one_elem: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart T' q p} = {(s,fs)}"
    using apart_s_fs rule4
    by fast
  have union: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (apart T' q p)} =
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} \<union>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart T' q p}"
    by fast
  then have finite_subs: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} \<and>
      finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart T' q p}"
    using fin3
    by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s) \<and> p = fs) \<and> apart T' q p} \<inter> {(s,fs)} = {}"
    by blast
  then have card_splitup: "card {(q,p). q \<in> S' \<and> p \<in> F' \<and> (apart T' q p)} =
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} +
      card {(s,fs)}"
    using fin3 union one_elem finite_subs card_Un_disjoint[of "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p}" "{(s,fs)}"]
    by argo
  have removed: "{(q,p). q \<in> S \<and> p \<in> F \<and> (apart T q p)} =
      {(q,p). q \<in> S \<and> p \<in> F \<and> \<not> (q = s \<and> p = fs) \<and> (apart T q p)}"
    using rule4
    by fast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> (q = s \<and> p = fs) \<and> (apart T q p)} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p}"
    using retain_specific rule4
    by (smt (verit,ccfv_SIG) Pair_inject apart.simps case_prodE case_prodI2 mem_Collect_eq subsetI)
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> (apart T q p)} \<le>
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p}"
    using fin3 card_mono removed finite_subs
    by force
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> (apart T q p)} <
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} + card {(s,fs)}"
    by simp
  then have trd: "norm_trd (S,F,T) < norm_trd (S',F',T')"
    using card_splitup
    by simp

  show ?case
    using fst snd trd
    by simp
qed


theorem norm_max_no_step:
  assumes "norm (S,F,T) \<ge> (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))" and
    "invar m (S,F,T)"
  shows "\<nexists> S' F' T'. algo_step m (S,F,T) (S',F',T')"
proof (rule ccontr)
  assume "\<not> (\<nexists> S' F' T'. algo_step m (S,F,T) (S',F',T'))"
  then obtain S' F' T' where
    S': "algo_step m (S,F,T) (S',F',T')"
    by fast
  have a: "norm (S',F',T') > (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))"
    using algo_step_increases_norm[OF S' assms(2)] assms(1) by linarith
  have inv: "invar m (S',F',T')" by(rule algo_step_keeps_invar[OF S' assms(2)])
  then have "norm (S',F',T') \<le> (card S' * (card S' + 1)) div 2 + (card S' * card I) + (card S' * (card S' * card I))"
    by(rule norm_max)
  then have "(card S' * (card S' + 1)) div 2 + (card S' * card I) + (card S' * (card S' * card I)) >
      (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))"
    using a
    by linarith
  then show False
    using a max_norm_total[OF inv] by linarith
qed


lemma no_step_rule1:
  assumes "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))"
  shows "\<not> (\<exists> f \<in> F. \<forall> s \<in> S. apart T s f)"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> f \<in> F. \<forall> s \<in> S. apart T s f)"
  then obtain f where
    "f \<in> F \<and> (\<forall> s \<in> S. apart T s f)"
    by blast
  then have "algo_step m (S,F,T) (S \<union> {f},{fnew. in_F (S \<union> {f},F,T) fnew},T)"
    using rule1 ass
    by blast
  then show False
    using assms
    by simp
qed


lemma no_step_rule2:
  assumes "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))"
  shows "\<not> (\<exists> s i. s \<in> S \<and> (out_star T (s @ [i]) = None))"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> s i. s \<in> S \<and> (out_star T (s @ [i]) = None))"
  then obtain s i where
    si: "s \<in> S \<and> (out_star T (s @ [i]) = None)"
    by blast
  then obtain out where
    out: "output_query m (s @ [i]) = out"
    by presburger
  then have "algo_step m (S,F,T) (S,F \<union> {s @ [i]},process_output_query T (s @ [i]) out)"
    using rule2 si out
    by blast
  then show False
    using assms
    by simp
qed


lemma no_step_rule3:
  assumes "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))" and
    "invar m (S,F,T)"
  shows "\<not> (\<exists> s1 s2 f. s1 \<in> S \<and> s2 \<in> S \<and> f \<in> F \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2)"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> s1 s2 f. s1 \<in> S \<and> s2 \<in> S \<and> f \<in> F \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2)"
  then obtain s1 s2 f where
    ss: "s1 \<in> S \<and> s2 \<in> S \<and> f \<in> F \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2"
    by blast
  have "sapart (S,F,T)"
    using assms invars
    by presburger
  then have "apart T s1 s2"
    using assms ss
    by (meson ass exsist_witness rule3 sapart.simps)
  then obtain w where
    w: "apart_witness T s1 s2 w"
    using assms exsist_witness
    by blast
  obtain out where
    out: "output_query m (f @ w) = out"
    by simp
  then have "algo_step m (S,F,T) (S,F,process_output_query T (f @ w) out)"
    using rule3 ss out w
    by blast
  then show False
    using assms
    by simp
qed


lemma no_step_rule4:
  assumes "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))" and
    "invar m (S,F,T)"
  shows "\<not> (\<exists> s fs inp. fs \<in> F \<and>
      s \<in> S \<and>
      \<not> apart T s fs \<and>
      difference_query m s fs = Some inp)"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> s fs inp. fs \<in> F \<and>
      s \<in> S \<and>
      \<not> apart T s fs \<and>
      difference_query m s fs = Some inp)"
  then obtain s fs inp where
    ss: "fs \<in> F \<and>
        s \<in> S \<and>
        \<not> apart T s fs \<and>
        difference_query m s fs = Some inp"
    by blast
  have si_not_none: "\<forall> s1 \<in> S. \<forall> i. out_star T (s1 @ [i]) \<noteq> None"
    using no_step_rule2 assms
    by metis
  have "~ (\<exists> f \<in> F. isolated T S f)"
    apply (simp only: isolated.simps)
    using no_step_rule1 assms
    by blast
  then have notiso: "\<forall> f \<in> F. \<not> isolated T S f"
    by blast
  obtain outf where
    outf: "outf = output_query m (fs @ inp)"
    by simp
  obtain outs where
    outs: "outs = output_query m (s @ inp)"
    by simp
  then have "algo_step m (S,F,T) (S,F,process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)"
    using rule4[of S T F fs s inp outs outf] ss outs outf notiso si_not_none
    by blast
  then show False
    using assms
    by simp
qed


theorem no_step_exists_hypothesis:
  assumes "invar m (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))"
  shows "\<exists> t. hypothesis (S,F,T) t"
    using assms no_step_rule1 no_step_rule2 exists_hypothesis
    by auto


lemma not_apart_machines_snd_f:
  assumes "\<not> (apart_machines f notapartq f q)"
  shows "snd (f (notapartq,i)) = snd (f (q,i))"
proof (rule ccontr)
  assume ass: "\<not> snd (f (notapartq,i)) = snd (f (q,i))"
  have "trans_star_output f notapartq [i] \<noteq> trans_star_output f q [i]"
    using ass
    by (metis eq_snd_iff split_trans_star_output split_trans_star_output_rev)
  then have "apart_machines f notapartq f q"
    by (meson apart_machines.elims(3))
  then show False
    using assms
    by blast
qed


lemma apart_machines_propagates_function:
  assumes "\<not> (apart_machines f notapartq t q)"
  shows "\<not> apart_machines f (fst (f (notapartq,i))) t (fst (t (q,i)))"
proof (rule ccontr)
  assume ass: "\<not> \<not> apart_machines f (fst (f (notapartq,i))) t (fst (t (q,i)))"
  then have "\<exists> j. trans_star_output f (fst (f (notapartq,i))) j \<noteq> trans_star_output t (fst (t (q,i))) j"
    by simp
  then obtain j where
    "trans_star_output f (fst (f (notapartq,i))) j \<noteq> trans_star_output t (fst (t (q,i))) j"
    by blast
  then have "(let (st,op) = f (notapartq,i) in (let x = trans_star_output f st j in (op # x))) \<noteq> (let (st,op) = t (q,i) in (let x = trans_star_output t st j in (op # x)))"
    by (simp add: split_beta)
  then have "trans_star_output f notapartq (i # j) \<noteq> trans_star_output t q (i # j)"
    by simp
  then show False
    using assms
    by (metis apart_machines.elims(1))
qed


lemma hypothesis_no_step_output_same:
  assumes "invar m (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))" and
    "hypothesis (S,F,T) t" and
    "m = (q_0,f)" and
    "\<not> (apart_machines f (trans_star_state f q_0 p) f q)" and
    "p \<in> S"
  shows "trans_star_output f q inp = trans_star_output t p inp"
using assms proof (induction inp arbitrary: q p)
  case Nil
  show ?case
    by simp
next
  case (Cons a inp)
  have not_rule2: "\<not> (\<exists> s i. s \<in> S \<and> (out_star T (s @ [i]) = None))"
    using no_step_rule2 assms
    by blast
  then have not_rule4: "\<not> (\<exists> s fs inp. fs \<in> F \<and>
      s \<in> S \<and>
      \<not> apart T s fs \<and>
      drop (length s) (trans_star_output f (q_0) (s @ inp)) \<noteq>
      drop (length fs) (trans_star_output f q_0 (fs @ inp)))"
    using no_step_rule4 assms difference_query_def difference_query_def_none
    by fast
  have "otree_star T p \<noteq> None"
    using assms
    by (smt (verit) Cons.prems(6) case_optionE invars option.discI otree_eq_out otree_star.elims)
  then obtain tran op where
    tran: "otree_star T p = Some (Node tran,op)"
    by (metis obs_tree.exhaust option.exhaust surj_pair)
  have pa_not_none: "otree_star T (p @ [a]) \<noteq> None"
    using assms
    by (smt (verit) Cons.prems(6) case_optionE not_rule2 option.discI otree_eq_out otree_star.elims)
  then have "tran a \<noteq> None"
    using tran
    by (metis obs_tree.exhaust otree_star_split_none)
  then obtain n out where
    nout: "tran a = Some (n,out)"
    by fast
  obtain tree where
    tree: "T = Node tree"
    using obs_tree.exhaust
    by auto
  obtain ots ptrans where
    ots: "trans_star f q_0 p = (ptrans,ots)"
    by fastforce
  obtain q' out2 where
    out2: "f (q,a) = (q',out2)"
    by fastforce
  have output_same: "Some (trans_star_output f q_0 (p @ [a])) = out_star T (p @ [a])"
    using pa_not_none Cons(2,5)
    by (metis Cons.prems(6) invars(6) not_rule2 output_query.simps)
  have "otree_star T (p @ [a]) = Some (n,op @ [out])"
    using tran nout
    by (metis obs_tree.exhaust otree_star_split)
  then have out_star_out: "out_star T (p @ [a]) = Some (op @ [out])"
    using otree_eq_out[of tree "p @ [a]"] tree
    by simp
  obtain notapartq outq where
    trans_starp: "trans_star f q_0 p = (notapartq,outq)"
    by fastforce
  then have "\<not> (apart_machines f notapartq f q)"
    using Cons
    by (metis Pair_inject trans_star_output_state)
  then have "snd (f (notapartq,a)) = snd (f (q,a))"
    using not_apart_machines_snd_f
    by fast
  then have "snd (f (notapartq,a)) = out2"
    using out2
    by auto
  then obtain notapartq' where
    notapartq': "f (notapartq,a) = (notapartq',out2)"
    by (metis prod.collapse)
  then have trans_star_pa: "(trans_star f q_0 (p @ [a])) = (notapartq',outq @ [out2])"
    using trans_star_split_end[of f notapartq a notapartq' out2 q_0 p outq] trans_starp
    by linarith
  then have "trans_star_output f q_0 (p @ [a]) = outq @ [out2]"
    by (simp add: trans_star_output_state)
  then have out2_eq: "out2 = out"
    using out_star_out output_same ots trans_starp
    by auto
  have notapartq'_alt: "trans_star_state f q_0 (p @ [a]) = notapartq'"
    using trans_star_output_state trans_star_pa
    by (metis Pair_inject)
  have "\<not> apart_machines f (fst (f (trans_star_state f q_0 p,a))) f q'"
    using apart_machines_propagates_function Cons
    by (metis fstI out2)
  then have "\<not> apart_machines f notapartq' f q'"
    using notapartq'
    by (metis split_pairs trans_star_output_state trans_starp)
  then have ih_prem: "\<not> apart_machines f (trans_star_state f q_0 (p @ [a])) f q'"
    using notapartq'_alt
    by simp
  show ?case proof (cases "p @ [a] \<in> S")
    case True
    have "t (p,a) = (p @ [a],out)"
      using Cons(4) nout tran Cons(7) True
      by (simp add: hypothesis_split_in_S)
    then have aux: "trans_star_output t p (a # inp) = (out # trans_star_output t (p @ [a]) inp)"
      by simp
    then have "trans_star_output f q' inp = trans_star_output t (p @ [a]) inp"
      using Cons.IH ih_prem True assms(1) assms(2) assms(3) assms(4)
      by blast
    then have "out2 # trans_star_output f q' inp = out # trans_star_output t (p @ [a]) inp"
      using out2_eq
      by blast
    then have "trans_star_output f q (a # inp) = trans_star_output t p (a # inp)"
      using aux out2
      by auto
    then show ?thesis
      by blast
  next
    case False
    have pa_in_F: "p @ [a] \<in> F"
      using Cons False in_F.simps invars(8) not_rule2
      by auto
    obtain p' where
      p': "t (p,a) = (p',out)"
      using False
      by (meson Cons.prems(3) Cons.prems(6) nout tran hypothesis_split_notin_S)
    then have notapart_p'pa: "\<not> apart T p' (p @ [a]) \<and> p' \<in> S"
      using hypothesis_split_notin_S[of S F T t p tran op a n out] assms(3,6)
      by (simp add: Cons.prems(6) False nout tran)
    have "\<not> apart_machines f (trans_star_state f q_0 (p')) f q'" proof (rule ccontr)
      assume assapart: "\<not> \<not> apart_machines f (trans_star_state f q_0 (p')) f q'"
      have "\<exists> inp. drop (length p') (trans_star_output f (q_0) (p' @ inp)) \<noteq>
          drop (length (p @ [a])) (trans_star_output f q_0 (p @ [a] @ inp))" proof (rule ccontr)
        assume "\<not> (\<exists> inp. drop (length p') (trans_star_output f (q_0) (p' @ inp)) \<noteq>
            drop (length (p @ [a])) (trans_star_output f q_0 (p @ [a] @ inp)))"
        then have same_output_pa_p': "\<forall> inp. drop (length p') (trans_star_output f (q_0) (p' @ inp)) =
            drop (length (p @ [a])) (trans_star_output f q_0 (p @ [a] @ inp))"
          by blast
        have pa_inp_trans_star_without_drop: "\<forall> inp. drop (length (p @ [a])) (trans_star_output f (q_0) (p @ [a] @ inp)) =
            trans_star_output f (trans_star_state f q_0 (p @ [a])) inp"
          by (metis append_assoc fst_eqD notapartq'_alt snd_conv trans_star_output_state trans_star_two_nested)
        have "\<forall> inp. drop (length p') (trans_star_output f (q_0) (p' @ inp)) = trans_star_output f (trans_star_state f q_0 (p')) inp"
          by (metis fst_eqD snd_conv trans_star_output_state trans_star_two_nested)
        then have trans_output_pa_p'_eq: "\<forall> inp. trans_star_output f (trans_star_state f q_0 (p')) inp = trans_star_output f (trans_star_state f q_0 (p @ [a])) inp"
          using pa_inp_trans_star_without_drop same_output_pa_p'
          by presburger
        have "\<forall> i. trans_star_output f (trans_star_state f q_0 (p @ [a])) i = trans_star_output f q' i"
          using ih_prem
          by force
        then have "\<forall> i. trans_star_output f (trans_star_state f q_0 (p')) i = trans_star_output f q' i"
          using trans_output_pa_p'_eq
          by simp
        then have "\<not> apart_machines f (trans_star_state f q_0 p') f q'"
          by simp
        then show False
          using assapart
          by blast
      qed
      then show False
        using not_rule4 notapart_p'pa pa_in_F
        by fastforce
    qed
    then have "trans_star_output f q' inp = trans_star_output t (p') inp"
      using Cons.IH p' False assms(1) assms(2) assms(3) assms(4) notapart_p'pa
      by blast
    then have "out2 # trans_star_output f q' inp = out # trans_star_output t (p') inp"
      using out2_eq
      by blast
    then have "trans_star_output f q (a # inp) = trans_star_output t p (a # inp)"
      by (simp add: out2 p')
    then show ?thesis
      by blast
  qed
qed


theorem no_step_mealy_equal:
  assumes "invar m (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step m (S,F,T) (S',F',T'))" and
    "hypothesis (S,F,T) t"
  shows "m \<approx> ([],t)"
proof (rule ccontr)
  assume ass: "~ (m \<approx> ([],t))"
  obtain q_0 f where
    two: "m = (q_0,f)"
    by fastforce
  then have "\<exists> inp. trans_star_output f q_0 inp \<noteq> trans_star_output t [] inp"
    using ass
    unfolding mealy_eq_def
    by blast
  then obtain inp where
    neq: "trans_star_output f q_0 inp \<noteq> trans_star_output t [] inp"
    by blast
  have one: "[] \<in> S"
    using assms
    by (simp add: invars(9))
  have three: "\<not> (apart_machines f (trans_star_state f q_0 []) f q_0)"
    by force
  have "trans_star_output f q_0 inp = trans_star_output t [] inp"
    using hypothesis_no_step_output_same[of S F T t q_0 f "[]" q_0 inp] one two three assms
    by blast
  then show False
    using neq
    by blast
qed


section \<open>function\<close>


lemma find1_step:
  assumes "find1 T S F = Some f"
  shows "algo_step m (set S,set F,T) (set (f # S),set (updateF T (f # S) F),T)"
    using assms updateF_def find1_def rule1
    by (smt (verit) inf_sup_aci(5) insert_def list.simps(15) singleton_conv)


lemma find2_step:
  assumes "find2 T S F = Some x"
  shows "algo_step m (set S,set F,T) (set S,set (x # F),process_output_query T x (output_query m x))"
    using assms find2_def rule2
    by (metis Un_commute insert_is_Un list.simps(15))


lemma find3_step:
  assumes "find3 T S F = Some x"
  shows "algo_step m (set S,set F,T) (set S,set F,process_output_query T x (output_query m x))"
    using find3_def rule3 assms
    by blast


lemma find4_step:
  assumes "find1 T S F = None" and
    "find2 T S F = None" and
    "find4 T S F = Some (x,y)"
  shows "algo_step m (set S,set F,T) (set S,set F,process_output_query (process_output_query T x (output_query m x)) y (output_query m y))"
proof -
  have "\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)"
    using assms find1_def_none
    by blast
  then have a: "\<forall> f1 \<in> set F. \<not> (isolated T (set S) f1)"
    by simp
  have "\<nexists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> out_star T x = None"
    using assms find2_def_none
    by blast
  then have b: "\<forall> s1 \<in> set S. \<forall> i. out_star T (s1 @ [i]) \<noteq> None"
    by auto
  have "\<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
      \<not> apart T s fs \<and>
      difference_query m s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp"
    using find4_def assms
    by blast
  then show ?thesis
    using a b rule4
    by blast
qed


lemma norm_ge_invar_fin1:
  assumes "find1 T S F = Some f" and
    "invar m (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set (f # S),set (updateF T (f # S) F),T)" and
    "invar m (set (f # S),set (updateF T (f # S) F),T)"
      using assms find1_step algo_step_increases_norm algo_step_keeps_invar
      by blast +


lemma norm_ge_invar_fin2:
  assumes "find2 T S F = Some x" and
    "invar m (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set S,set (x # F),process_output_query T x (output_query m x))" and
    "invar m (set S,set (x # F),process_output_query T x (output_query m x))"
      using assms find2_step algo_step_increases_norm algo_step_keeps_invar
      by blast +


lemma norm_ge_invar_fin3:
  assumes "find3 T S F = Some x" and
    "invar m (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set S,set F,process_output_query T x (output_query m x))" and
    "invar m (set S,set F,process_output_query T x (output_query m x))"
      using assms find3_step algo_step_increases_norm algo_step_keeps_invar
      by blast +


lemma norm_ge_invar_fin4:
  assumes "find1 T S F = None" and
    "find2 T S F = None" and
    "find4 T S F = Some (x,y)" and
    "invar m (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set S,set F,process_output_query (process_output_query T x (output_query m x)) y (output_query m y))" and
    "invar m (set S,set F,process_output_query (process_output_query T x (output_query m x)) y (output_query m y))"
      using assms find4_step algo_step_increases_norm algo_step_keeps_invar
      by blast +


lemma not_algostep_find_none:
  assumes "\<nexists> S' F' T'. algo_step m (set S,set F,T) (S',F',T')" and
    "invar m (set S,set F,T)"
  shows "find1 T S F = None" and
    "find2 T S F = None" and
    "find3 T S F = None" and
    "find4 T S F = None"
      using assms no_step_rule1 find1_def_none
      apply meson
      using assms no_step_rule2 find2_def_none
      apply fast
      using assms no_step_rule3 find3_def_none
      apply fast
      using assms no_step_rule4 find4_def_none
      by fast


lemma norm_max_find_none:
  assumes "norm (set S,set F,T) \<ge> (card Q * (card Q + 1)) div 2 + (card Q * card I) + (card Q * (card Q * card I))" and
    "invar m (set S,set F,T)"
  shows "find1 T S F = None" and
    "find2 T S F = None" and
    "find3 T S F = None" and
    "find4 T S F = None"
      using not_algostep_find_none norm_max_no_step assms
      by auto


lemma any_precon_algo_step:
  assumes "algo_step m (set S,set F,T) (S',F',T')"
  shows "(\<exists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)) \<or>
      (\<exists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> out_star T x = None) \<or>
      (\<exists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2 \<and>
        apart_witness T s1 s2 w) \<or>
      (\<exists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        difference_query m s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
    using assms
    apply (cases rule: algo_step.cases)
    by metis +


lemma nex_precondition_nex_algostep:
  assumes "\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)" and
    "\<nexists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> out_star T x = None" and
    "\<nexists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2 \<and>
        apart_witness T s1 s2 w" and
    "\<nexists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        difference_query m s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp"
  shows "\<nexists> S' F' T'. algo_step m (set S,set F,T) (S',F',T')"
proof
  assume "\<exists> S' F' T'. algo_step m (set S,set F,T) (S',F',T')"
  then have "(\<exists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)) \<or>
      (\<exists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> out_star T x = None) \<or>
      (\<exists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2 \<and>
        apart_witness T s1 s2 w) \<or>
      (\<exists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        difference_query m s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
    using any_precon_algo_step
    by presburger
  then show False
    using assms
    by fast
qed


lemma find_none_no_step:
  assumes "find1 T S F = None" and
    "find2 T S F = None" and
    "find3 T S F = None" and
    "find4 T S F = None" and
    "invar m (set S,set F,T)"
  shows "\<nexists> S' F' T'. algo_step m (set S,set F,T) (S',F',T')"
    using nex_precondition_nex_algostep assms find1_def_none find2_def_none find3_def_none find4_def_none
    by simp


function lsharp :: "('state,'input,'output) mealy \<Rightarrow> ('input,'output) state_list \<Rightarrow> ('input,'output) state_list" where
"lsharp m (S,F,T) = (if invar m (set S,set F,T)
    then (case find1 T S F of
      Some f \<Rightarrow> lsharp m (f # S,updateF T (f # S) F,T) |
      None \<Rightarrow> (case find2 T S F of
        Some x \<Rightarrow> lsharp m (S,x # F,process_output_query T x (output_query m x)) |
        None \<Rightarrow> (case find3 T S F of
          Some x \<Rightarrow> lsharp m (S,F,process_output_query T x (output_query m x)) |
          None \<Rightarrow> (case find4 T S F of
            Some (x,y) \<Rightarrow> (S,F,process_output_query (process_output_query T x (output_query m x)) y (output_query m y)) |
            None \<Rightarrow> (S,F,T)))))
    else ([], [],(Node Map.empty)))"
  using norm_ge_invar_fin1 norm_ge_invar_fin2 norm_ge_invar_fin3 norm_ge_invar_fin4 max_norm_total
  sorry


end
end