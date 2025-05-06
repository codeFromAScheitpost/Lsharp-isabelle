theory observation_tree
  imports "./mealie" Complex_Main
begin
sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

datatype ('input,'output) obs_tree = Node "'input list \<times>('input \<Rightarrow> ( ('input,'output) obs_tree \<times> 'output) option)"

type_synonym ('state,'input,'output) obs= "'state set\<times> 'state set \<times> ('state,'input,'output) mealie"

definition otree ::"('state,'input,'output) obs \<Rightarrow>bool" where
"otree ot \<equiv> (case ot of (S,F,(q_0,Q,t)) \<Rightarrow>mealie_invar (q_0,Q,t)\<and>mealie_tree (q_0,Q,t) \<and> S\<subseteq>Q\<and>F\<subseteq>Q )"

definition isolated :: " ('state,'input,'output) obs \<Rightarrow>'state \<Rightarrow>bool" where 
"isolated ot f \<equiv> (case ot of (S,F,m) \<Rightarrow> f\<in>F\<and>(\<forall> s. s\<in>S \<longrightarrow>apart m f s))"

definition identified :: " ('state,'input,'output) obs \<Rightarrow>'state \<Rightarrow>bool" where 
"identified ot f \<equiv> (case ot of (S,F,m) \<Rightarrow> f\<in>F\<and>(\<exists> s. \<forall>s2. s\<in>S\<and>s2\<in>S \<and> s\<noteq>s2 \<and>\<not>apart m f s \<and> apart m f s2))"

definition hypothesis ::"('state,'input,'output) obs \<Rightarrow> ('state\<Rightarrow>'state) \<Rightarrow>bool" where 
"hypothesis ot h \<equiv> (case ot of (S,F,m) \<Rightarrow> \<forall> f\<in>F. h f \<in>S \<and> ~ apart m (h f) f   )"

lemma "otree (S,F,m) \<Longrightarrow>\<forall> f\<in>F. \<not> isolated (S,F,m) f \<Longrightarrow> \<exists> h. hypothesis (S,F,m) h"
  unfolding otree_def mealie_invar_def mealie_tree_def isolated_def hypothesis_def apart_def   apply (auto split:prod.splits option.splits) 
  by metis
fun otree_star :: "'input list \<Rightarrow> ('input,'output) obs_tree \<Rightarrow> ( ('input,'output) obs_tree\<times> 'output list ) option" where 
"otree_star [] ot = Some (ot, [])"|
"otree_star (i#is) (Node (acc,t)) = (case t i of Some (n,op) \<Rightarrow> (case (otree_star is n) of Some (ot,ops) \<Rightarrow> Some (ot,op#ops)| None \<Rightarrow> None ) | None \<Rightarrow> None)"


fun apart ::"('input,'output) obs_tree \<Rightarrow> ('input,'output) obs_tree \<Rightarrow>bool" where 
"apart  (Node t1) (Node t2) = (\<exists> i x y. otree_star i (Node t1)  =Some x \<and> otree_star i  (Node t2)= Some y \<and> x\<noteq>y)"

fun apart_witness ::"'input list \<Rightarrow>('input,'output) obs_tree \<Rightarrow> ('input,'output) obs_tree \<Rightarrow>bool" where 
"apart_witness  is (Node t1) (Node t2) = (\<exists>  x y. otree_star is (Node t1)  =Some x \<and> otree_star is  (Node t2)= Some y \<and> x\<noteq>y)"



fun apart_ilist ::"'input list \<Rightarrow> 'input list \<Rightarrow> ('input,'output) obs_tree \<Rightarrow>bool" where
"apart_ilist  q p q_0 = (case (otree_star p q_0 ,otree_star q q_0) of (Some (t1,op1),Some (t2,op2)) \<Rightarrow>    (\<exists> i xn yn x y. otree_star i  t1  =Some (xn,x) \<and> otree_star i   t2= Some (yn,y) \<and> x\<noteq>y) | (_,_) \<Rightarrow> undefined)"



fun not_apart_s ::" ('input,'output) obs_tree \<Rightarrow> 'input list list  \<Rightarrow>     ('input,'output) obs_tree \<Rightarrow>  'input list list " where 
"not_apart_s q_0 [] f = []"|
"not_apart_s q_0  (s#ss) f = (case otree_star s q_0 of Some (snode,op) \<Rightarrow> (if (apart (snode) f) then not_apart_s q_0 ss f else s#(not_apart_s q_0 ss f)))"



fun output_query ::"('state,'input,'output) mealie \<Rightarrow> 'input list \<Rightarrow> 'output list " where 
"output_query (q_0,Q,t) is=  trans_star_output  is q_0 t"



definition eq_query :: " (('state,'input,'output) mealie \<Rightarrow> ('state2,'input,'output) mealie \<Rightarrow>(bool\<times>'input list)) \<Rightarrow>bool " where 
"eq_query f \<equiv> \<forall> m h x.(case (m,h) of ((q_0,Q,t),(p_0,P,g)) \<Rightarrow>  (if h\<approx>m then f h m = (True, []) else f h m= (False,x)\<and> trans_star_output x q_0 t \<noteq> trans_star_output x p_0 g ))   "








fun rule_one_set :: " ('state,'input,'output) mealie \<Rightarrow> ('input,'output) obs_tree set  \<Rightarrow>  ('input,'output) obs_tree set\<Rightarrow> ('input,'output) obs_tree \<Rightarrow>
(('input,'output) obs_tree set \<times> ('input,'output) obs_tree set \<times>  ('input,'output) obs_tree)" where
"rule_one_set m S F (Node t)  = ( let not_apart={f. f\<in> F\<and>(\<forall> s\<in> S. apart f s)} in (S\<union>not_apart,F-not_apart,(Node t))) " 



fun rule_one :: " ('state,'input,'output) mealie \<Rightarrow> 'input list  list  \<Rightarrow>  'input list  list\<Rightarrow> ('input,'output) obs_tree \<Rightarrow>
('input list list \<times> 'input list list \<times>  ('input,'output) obs_tree)" where
"rule_one m S [] q_0  = (S,[],q_0) " |
"rule_one m S (f#fs) q_0  = (let (S_2,F_2,q_0_2)=rule_one m S fs q_0  in (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2)))) " 


fun process_output_query :: "'input list\<Rightarrow> 'output list \<Rightarrow>('input,'output) obs_tree \<Rightarrow> ('input,'output) obs_tree" where 
"process_output_query [] [] q = q  "|
"process_output_query i [] q =  undefined"|
"process_output_query  [] _ q =  undefined"|
"process_output_query (i#is) (op#ops) (Node (acc,t)) =  (case t i of None\<Rightarrow> (Node (acc, (\<lambda> j. if j=i then Some ( process_output_query is ops (Node (acc@[i],(\<lambda> k. None))),op)  else  t j))) 
| Some (tree,out) \<Rightarrow>  (Node (acc, (\<lambda>j. if j=i then Some ((process_output_query is ops tree),out) else t j)) )) "





fun rule_two_aux :: " ('state,'input,'output) mealie \<Rightarrow> ('input,'output) obs_tree   \<Rightarrow>  ('input,'output) obs_tree \<Rightarrow> 'input list \<Rightarrow>  
( ('input,'output) obs_tree)" where
"rule_two_aux m (Node (acc,t))  q_0  [] = q_0 "|
"rule_two_aux m (Node (acc,t))  q_0  (i#is) =   (if t i=None then( let (output) = output_query m (acc@[i]) in process_output_query (acc@[i]) (output)  (rule_two_aux m (Node (acc,t))  (  q_0 ) is))   
else   rule_two_aux m  (Node (acc,t))  q_0 is)    "



fun find_f_aux :: "('input,'output) obs_tree  \<Rightarrow>('input list list) \<Rightarrow> 'input list \<Rightarrow>'input list list " where
"find_f_aux _ _  [] = []"|
"find_f_aux (Node (acc,t)) S  (i#is) = (case t i of Some ((Node (acc_follow,t_follow)),a) \<Rightarrow>(   if acc@[i] \<in> set S then [] else [acc@[i]])| None \<Rightarrow> []) @ find_f_aux (Node (acc,t)) S  (is)  "


fun find_f :: "'input list list \<Rightarrow> 'input list list\<Rightarrow> 'input list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow>'input list list " where
"find_f [] _ _  _= []"|
"find_f (n#ns) S i  q_0 = (case otree_star n q_0 of Some (node,op) \<Rightarrow> (find_f_aux node S i) @ (find_f ns S i q_0 )| None \<Rightarrow> undefined) "







fun rule_two :: " ('state,'input,'output) mealie \<Rightarrow> 'input list list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow> 'input list\<Rightarrow>   
 ('input,'output) obs_tree" where
"rule_two m [] q_0 is  = q_0 "|
"rule_two m (sn#sns) q_0 is  = (let node = (rule_two m sns q_0 is) in  (case   otree_star sn node  of Some (tree,op) \<Rightarrow>   rule_two_aux m tree node is|None \<Rightarrow> undefined))  "




fun rule_two_three_op :: " ('state,'input,'output) mealie \<Rightarrow> 'input list list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow> 'input list\<Rightarrow>   
('input list list \<times> 'input list list \<times> ('input,'output) obs_tree)" where
"rule_two_three_op  m S q_0 is  =  (let q_0_new= rule_two m S q_0 is in ( S,find_f S S is q_0_new, q_0_new )) "


definition norm ::"'input list list \<Rightarrow> 'input list list \<Rightarrow>'input list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow> real" where
"norm S F I q_0 =  ((real (length S *(length S +1)))/2) + card {(q,i). q\<in>set S \<and>   i\<in> set I \<and>  otree_star (q@[i]) q_0 \<noteq>None} +card {(q,p). q\<in> set S\<and> p\<in>set F \<and>apart_ilist q p q_0 } "



definition otree_rec_1 :: " 'input list list \<Rightarrow> 'input list list \<Rightarrow>  bool" where 
"otree_rec_1  S F \<equiv>(\<forall> acc.  \<not>(acc\<in>set S\<and>acc\<in> set F))"


definition otree_rec_3 :: " ('input,'output) obs_tree\<Rightarrow> 'input list \<Rightarrow>  bool" where 
"otree_rec_3 ot I \<equiv>(\<forall> is i. i\<in> set is\<and> i\<notin>set I  \<longrightarrow>  otree_star is ot=None )"

definition otree_rec_4 :: " ('input,'output) obs_tree\<Rightarrow>  bool" where 
"otree_rec_4 ot  \<equiv>(\<forall>  t2 pos is os.   otree_star is ot = Some ((Node (pos,t2)),os) \<longrightarrow> pos=is)"


definition otree_rec_5 :: " ('input,'output) obs_tree \<Rightarrow> 'input list list  \<Rightarrow>  bool" where 
"otree_rec_5 ot S   \<equiv> (\<forall> i. i\<in>set S \<longrightarrow> otree_star i ot \<noteq> None)"

definition otree_rec::"('input,'output) obs_tree \<Rightarrow> 'input list list \<Rightarrow> 'input list list \<Rightarrow> 'input list \<Rightarrow> bool" where 
"otree_rec ot S F I \<equiv>  otree_rec_1 S F\<and>  otree_rec_3 ot I\<and> otree_rec_4 ot \<and> otree_rec_5 ot S \<and>  otree_rec_5 ot F \<and> distinct (S@F)
   "

definition norm_fst ::"'input list list \<Rightarrow> 'input list list \<Rightarrow>'input list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow> real" where
"norm_fst S F I q_0 =  ((real (length S *(length S +1)))/2) "

definition norm_scd ::"'input list list \<Rightarrow> 'input list list \<Rightarrow>'input list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow> real" where
"norm_scd S F I q_0 =   card {(q,i). q\<in>set S \<and>   i\<in> set I \<and>  otree_star (q@[i]) q_0 \<noteq>None}  "

definition norm_trd ::"'input list list \<Rightarrow> 'input list list \<Rightarrow>'input list \<Rightarrow> ('input,'output) obs_tree  \<Rightarrow> real" where
"norm_trd S F I q_0 =  card {(q,p). q\<in> set S\<and> p\<in>set F \<and>apart_ilist q p q_0 } "


lemma rec_4:" otree_rec_4  ot \<Longrightarrow>  otree_star is ot = Some ((Node (pos,t2)),os) \<Longrightarrow> pos=is"
  unfolding otree_rec_4_def by auto  



lemma  otree_induct_helper:"t i = (Some (tree,out)) \<Longrightarrow> length op= length acc \<Longrightarrow>otree_star acc (process_output_query (acc) op (tree)) = Some (lt,lout) \<Longrightarrow>
 otree_star (i#acc) (process_output_query (i#acc ) (out#op) (Node (acc_n, t))) = Some (lt,out#lout)"
by (induction acc) auto
 

lemma  otree_induct_helper_none:"t i = None \<Longrightarrow> length op= length acc \<Longrightarrow>otree_star acc (process_output_query (acc) op (Node (acc_n@[i],Map.empty))) = Some (lt,lout) \<Longrightarrow>
 otree_star (i#acc) (process_output_query (i#acc ) (out#op) (Node (acc_n, t))) = Some (lt,out#lout)"
  by (induction acc) auto

lemma nq_stays: "otree_rec q_0 S F I\<Longrightarrow>(n_S,n_F,n_q_0) =rule_one m S F q_0 \<Longrightarrow> n_q_0=q_0"
proof (induction  m S F q_0 arbitrary:n_S n_F n_q_0 rule:rule_one.induct)
  case (1 m S q_0)
  then show ?case 
    by fastforce
next
  case (2 m S f fs q_0)
  have a:" otree_star f q_0\<noteq> None"  using 2 unfolding otree_rec_def otree_rec_5_def 
    by force
  have rec:"otree_rec  q_0 S fs I " using 2 unfolding otree_rec_def otree_rec_1_def otree_rec_5_def 
    by auto
  then obtain nS nF nq where nq: "(nS, nF, nq) = rule_one m S fs q_0  " using 2 
    by (metis prod_cases3)
  then have  nqeq:"nq=q_0" using 2 rec 
    by fast
 have same:"\<exists> SS FF. (SS,FF,nq) =  (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#nS,nF,nq) else (nS,f#nF,nq)))" using a by auto
  have "rule_one m S (f # fs) q_0 =(let (S_2,F_2,q_0_2)=rule_one m S fs q_0  in (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))))" 
    by simp
  also have "\<dots>= (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#nS,nF,nq) else (nS,f#nF,nq)))"
    using nq 
    by (metis (no_types, lifting) case_prod_conv)
 
  finally show ?case  using 2 nqeq nq same 
    by (metis Pair_inject)   
qed 


lemma rone_length_s:"otree_rec q_0 S F I\<Longrightarrow>(n_S,n_F,n_q_0) =rule_one m S F q_0\<Longrightarrow>length n_S \<ge> length S"
proof (induction m S F q_0 arbitrary:n_S n_F n_q_0 rule:rule_one.induct)
  case (1 m S q_0)
  then show ?case 
    by fastforce
next
  case (2 m S f fs q_0)
  obtain S_2 F_2 q_0_2 where s:"(S_2,F_2,q_0_2)=rule_one m S fs q_0" 
    by (metis prod_cases3)
  have orec:"otree_rec q_0 S fs I" using 2 unfolding otree_rec_def otree_rec_1_def otree_rec_5_def 
    by simp
  have lens:"length S_2\<ge>length S" using orec s 2 
    by blast
  have "otree_star f q_0 \<noteq>None" using 2 unfolding otree_rec_def otree_rec_5_def  
    by auto
  then obtain fnode out where fnode:"otree_star f q_0= Some (fnode,out)" 
    by fast
    have "rule_one m S (f#fs) q_0 =(let (S_2,F_2,q_0_2)=rule_one m S fs q_0  in (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))))" 

      by simp
    also have "\<dots>=(case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2)))" using s 
      by (metis (no_types, lifting) case_prod_conv)
    also have 2:"\<dots>=(if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))" using fnode 
      by auto 
  then show ?case proof(cases "not_apart_s q_0 S fnode =[]")
    case True
    then have "rule_one m S (f#fs) q_0 = (f#S_2,F_2,q_0_2) " using calculation 2 
      by auto
    then show ?thesis using lens 
      using "2.prems"(2) by auto
  next
    case False
 then have "rule_one m S (f#fs) q_0 = (S_2,f#F_2,q_0_2) " using calculation 2 
      by auto
    then show ?thesis using lens 
      using "2.prems"(2) by auto
  qed
qed

lemma rone_subs_s:"otree_rec q_0 S F I\<Longrightarrow>(n_S,n_F,n_q_0) =rule_one m S F q_0\<Longrightarrow>set n_S \<supseteq> set S"
proof (induction m S F q_0 arbitrary:n_S n_F n_q_0 rule:rule_one.induct)
  case (1 m S q_0)
  then show ?case 
    by fastforce
next
  case (2 m S f fs q_0)
  obtain S_2 F_2 q_0_2 where s:"(S_2,F_2,q_0_2)=rule_one m S fs q_0" 
    by (metis prod_cases3)
  have orec:"otree_rec q_0 S fs I" using 2 unfolding otree_rec_def otree_rec_1_def otree_rec_5_def 
    by simp
  have lens:"set S_2\<supseteq>set S" using orec s 2 
    by blast
  have "otree_star f q_0 \<noteq>None" using 2 unfolding otree_rec_def otree_rec_5_def  
    by auto
  then obtain fnode out where fnode:"otree_star f q_0= Some (fnode,out)" 
    by fast
    have "rule_one m S (f#fs) q_0 =(let (S_2,F_2,q_0_2)=rule_one m S fs q_0  in (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))))" 

      by simp
    also have "\<dots>=(case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2)))" using s 
      by (metis (no_types, lifting) case_prod_conv)
    also have 2:"\<dots>=(if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))" using fnode 
      by auto 
  then show ?case proof(cases "not_apart_s q_0 S fnode =[]")
    case True
    then have "rule_one m S (f#fs) q_0 = (f#S_2,F_2,q_0_2) " using calculation 2 
      by auto
    then show ?thesis using lens 
      using "2.prems"(2) 
      by auto
  next
    case False
 then have "rule_one m S (f#fs) q_0 = (S_2,f#F_2,q_0_2) " using calculation 2 
      by auto
    then show ?thesis using lens 
      using "2.prems"(2) by auto
  qed
qed


  

theorem  assumes   "otree_rec q_0 S F I" "(n_S,n_F,n_q_0) =rule_one m S F q_0"
  shows    "norm S F I q_0 \<le> norm n_S n_F I n_q_0 "
using assms proof (induction m S F q_0  arbitrary: n_S n_F n_q_0  rule:rule_one.induct )
  case (1 m S q_0)
  then show ?case  
    by auto 
next
  case (2 m S f fs q_0)
  have "rule_one m S (f#fs) q_0 =(let (S_2,F_2,q_0_2)=rule_one m S fs q_0  in (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2)))) " 
    by simp
  obtain S_2 F_2 q_0_2 where  r:" (S_2,F_2,q_0_2)=rule_one m S fs q_0" 
    by (metis prod_cases3)
  have otree_rec: "otree_rec q_0 S ( fs) I" using 2 unfolding otree_rec_def otree_rec_1_def otree_rec_5_def 
    by simp
  then have induct:"observation_tree.norm S fs I q_0 \<le> observation_tree.norm S_2 F_2 I q_0_2" using 2 r  
    by fast

   have subs:"{(q, p). q \<in> set S_2 \<and> p \<in> set (f # F_2) \<and> apart_ilist q p q_0_2}\<subseteq>{(q, p). q \<in> set S_2 \<and> p \<in> set (f # F_2)} " 
     by auto
 have  f1:"finite (set F_2)" 
     by simp 
 have f2: "finite (set S_2)" 
   by simp 
 have f3: "finite (set I)" 
   by simp 



 
  have subs:"{(q, i). q \<in> set S_2 \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0_2 \<noteq> None}\<subseteq> {(q, i). q \<in> set (f # S_2) \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0_2 \<noteq> None}" 
    by auto 
  have finite_bigger:"finite {(q, i). q \<in> set (f # S_2) \<and> i \<in> set I }" using f1 f3 
    by simp

   have "otree_star f q_0\<noteq> None" using 2 unfolding otree_rec_def otree_rec_5_def 
     by force
   then obtain fnode out where fnode:"otree_star f q_0 = Some (fnode,out)" 
     by force
   then have "rule_one m S (f#fs) q_0= (let (S_2,F_2,q_0_2)=rule_one m S fs q_0  in (case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))))"
     by simp
   also have "\<dots>=(case otree_star f q_0 of Some (fnode,out) \<Rightarrow>  (if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2)))" using r 
     by (metis (no_types, lifting) case_prod_conv)
   also have "\<dots>=(if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))" using fnode 
     by simp
   finally have comp: "rule_one m S (f#fs) q_0=(if not_apart_s q_0 S fnode =[] then  (f#S_2,F_2,q_0_2) else (S_2,f#F_2,q_0_2))" 
     by linarith
    have q_0:"q_0_2=q_0" using nq_stays r otree_rec 
      by blast

 have fst_diff_old:"norm_fst S (f # fs) I q_0 -norm_fst S (fs) I q_0 =0 " unfolding norm_fst_def  
   by auto  
  have scd_diff_old:"norm_scd S (f # fs) I q_0 -norm_scd S (fs) I q_0 =0 " unfolding norm_scd_def 
    by argo 
   have fin_trd:"finite  {(q, p). q \<in> set S \<and> p \<in> set (f # fs)} " using f1 f2 f3  
     by simp
   have " {(q, p). q \<in> set S \<and> p \<in> set (f # fs) \<and> apart_ilist q p q_0}\<subseteq>{(q, p). q \<in> set S \<and> p \<in> set (f # fs)}" 
     by blast
   then have finite_trd_new:"finite  {(q, p). q \<in> set S \<and> p \<in> set (f # fs) \<and> apart_ilist q p q_0}" using fin_trd finite_subset 
     by blast
    have trd_union:" {(q, p). q \<in> set S \<and> p \<in> set (f # fs) \<and> apart_ilist q p q_0} =  {(q, p). q \<in> set S \<and> p \<in> set fs \<and> apart_ilist q p q_0} \<union>  {(q, p). q \<in> set S \<and> p \<in> {f} \<and> apart_ilist q p q_0}"
      by auto
  then have card_mix:"card {(q, p). q \<in> set S \<and> p \<in> set (f # fs) \<and> apart_ilist q p q_0} \<le> card  {(q, p). q \<in> set S \<and> p \<in> set fs \<and> apart_ilist q p q_0} + card {(q, p). q \<in> set S \<and> p \<in> {f} \<and> apart_ilist q p q_0}"
    using finite_trd_new 
    by (simp add: card_Un_le)
  have subs_temp:" {(q, p). q \<in> set S \<and> p \<in> {f} \<and> apart_ilist q p q_0} \<subseteq>  {(q, p). q \<in> set S \<and> p \<in>  {f}}"  
    by auto 
  have "finite {(q, p). q \<in> set S \<and> p \<in> {f} }" using trd_union finite_trd_new 
    by auto

  then have card_max_trd:" card  {(q, p). q \<in> set S \<and> p \<in> {f} \<and> apart_ilist q p q_0} \<le> card  {(q, p). q \<in> set S \<and> p \<in>  {f}}" 
    using subs_temp   card_mono[of " {(q, p). q \<in> set S \<and> p \<in> {f} }" " {(q, p). q \<in> set S \<and> p \<in> {f} \<and> apart_ilist q p q_0}"] 
    by blast   
  also have  "\<dots>\<le> length S" apply auto 
    by (simp add: card_length)
  finally have trd_diff_old:"norm_trd S (f # fs) I q_0 -norm_trd S (fs) I q_0 \<le> length S " unfolding norm_trd_def using card_mix  by auto
   
  then show ?case proof (cases " not_apart_s q_0 S fnode=[]" )
    case True

    have lens:"length S \<le> length S_2" using rone_length_s r 
      using otree_rec by blast

  have "{(q, i). q \<in> set (f # S_2) \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0_2 \<noteq> None}\<subseteq>{(q, i). q \<in> set (f # S_2) \<and> i \<in> set I } " 
    by fast
  then have "finite {(q, i). q \<in> set (f # S_2) \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0_2 \<noteq> None}" using finite_bigger finite_subset 
    by fast 
  then have c_scd:"(card {(q, i). q \<in> set S_2 \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0_2 \<noteq> None}) \<le>  (card {(q, i). q \<in> set (f # S_2) \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0_2 \<noteq> None})" using subs 
    by (simp add: card_mono)
   then have scd: "norm_scd S_2 F_2 I q_0_2 \<le>norm_scd (f#S_2) (F_2) I q_0_2" unfolding norm_scd_def 
     by linarith  
   have tmp:"finite {(q, p). q \<in> set (f#S_2) \<and> p \<in> set F_2}" using f1 f2 
     by simp
   have "{(q, p). q \<in> set (f#S_2) \<and> p \<in> set F_2 \<and> apart_ilist q p q_0_2}\<subseteq>{(q, p). q \<in> set (f#S_2) \<and> p \<in> set F_2} " 
     by fast
   then have fin_trd:"finite ({(q, p). q \<in> set (f#S_2) \<and> p \<in> set F_2 \<and> apart_ilist q p q_0_2})" using tmp finite_subset 
     by blast
   have " {(q, p). q \<in> set S_2 \<and> p \<in> set F_2 \<and> apart_ilist q p q_0_2}\<subseteq>  {(q, p). q \<in> set (f#S_2) \<and> p \<in> set F_2 \<and> apart_ilist q p q_0_2}" 
     by auto
   then have "card {(q, p). q \<in> set S_2 \<and> p \<in> set F_2 \<and> apart_ilist q p q_0_2}\<le>  card {(q, p). q \<in> set (f#S_2) \<and> p \<in> set F_2 \<and> apart_ilist q p q_0_2}" using fin_trd 
     using card_mono by auto
   then have trd:"norm_trd  S_2 F_2 I q_0_2 \<le>norm_trd (f#S_2) (F_2) I q_0_2" unfolding norm_trd_def 
     by simp
  then have r1:"rule_one m S (f#fs) q_0 = (f#S_2,F_2,q_0) " using  comp  q_0 True
    by auto
  have "norm_fst (S_2) n_F I n_q_0+(length S_2 +1)=norm_fst (f#S_2) n_F I n_q_0" unfolding norm_fst_def 
    by simp
  then have fst_diff_new:" norm_fst (f#S_2) F_2 I q_0_2 = norm_fst (S_2) F_2 I q_0_2  +(length S_2 +1)"  unfolding norm_fst_def 
    by argo
 
   have scd_diff_new:" norm_scd (f#S_2)F_2 I q_0_2 \<ge> norm_scd (S_2) F_2 I q_0_2  "  using scd q_0 
     using 2 r1 by auto

   have trd_diff_new:" norm_trd (f#S_2) n_F I n_q_0 - norm_trd (S_2) n_F I n_q_0  \<ge>0"  unfolding norm_trd_def using trd q_0
     using 2 r1 
     by (smt (verit, best) Collect_cong Pair_inject case_prodI2 case_prod_conv norm_trd_def)

  have "norm_fst S (f#fs) I q_0+norm_scd S (f#fs) I q_0+norm_trd S (f#fs) I q_0\<le>norm_fst S (fs) I q_0+norm_scd S (fs) I q_0+norm_trd S (fs) I q_0 +length S" using fst_diff_old scd_diff_old trd_diff_old
    by simp
  then have n1:"norm  S (f#fs) I q_0 \<le>norm  S (fs) I q_0 +length S" unfolding norm_def norm_fst_def norm_scd_def norm_trd_def 
    by blast 
  have "norm_fst (f# S_2) F_2 I q_0_2 + norm_scd (f# S_2) F_2 I q_0_2 + norm_trd (f# S_2) F_2 I q_0_2 \<ge> norm_fst ( S_2) F_2 I q_0_2 + norm_scd ( S_2) F_2 I q_0_2 + norm_trd ( S_2) F_2 I q_0_2+(length S_2 +1) " 
    using fst_diff_new scd_diff_new trd 
    by argo    
  then have "norm (f# S_2) F_2 I q_0_2 \<ge> norm S_2  F_2 I q_0_2 +(length S_2 +1)"  unfolding norm_def norm_fst_def norm_scd_def norm_trd_def 
    by blast 
 
   then show ?thesis using  n1 lens 
     using "2.prems"(2) induct q_0 r1 by auto  
  next
    case False
  have "finite {(q, p). q \<in> set S_2 \<and> p \<in> set (f # F_2)}" using f1 f2 
    by simp
  then  have fin: "finite {(q, p). q \<in> set S_2 \<and> p \<in> set (f# F_2) \<and> apart_ilist q p q_0_2}" using  subs finite_subset[of "{(q, p). q \<in> set S_2 \<and> p \<in> set (f # F_2) \<and> apart_ilist q p q_0_2}"  
"{(q, p). q \<in> set S_2 \<and> p \<in> set (f # F_2)}"] 
    by blast 


then have fst_new:"norm_fst S_2 F_2 I q_0_2 =norm_fst S_2 (f#F_2) I q_0_2" unfolding norm_fst_def 
     by blast 
   have scd_new:"norm_scd S_2 F_2 I q_0_2 =norm_scd S_2 (f#F_2) I q_0_2" unfolding norm_scd_def 
     by blast
   have change: "{(q, p). q \<in> set S_2 \<and> p \<in> set (f # F_2) \<and> apart_ilist q p q_0_2} = {(q, p). q \<in> set S_2 \<and> p \<in> set ( F_2) \<and> apart_ilist q p q_0_2}\<union> {(q, p). q \<in> set S_2 \<and> p \<in> {f} \<and> apart_ilist q p q_0_2} "
     by auto


   
 
   then have ja:"card {(q, p). q \<in> set S_2 \<and> p \<in> set ( F_2) \<and> apart_ilist q p q_0_2} \<le> card ({(q, p). q \<in> set S_2 \<and> p \<in> set ( F_2) \<and> apart_ilist q p q_0_2}\<union> {(q, p). q \<in> set S_2 \<and> p \<in> {f} \<and> apart_ilist q p q_0_2}) "
     by (metis (no_types, lifting) Un_upper1 card_mono fin)
   then have "  card ({(q, p). q \<in> set S_2 \<and> p \<in> set ( F_2) \<and> apart_ilist q p q_0_2}) \<le> card ({(q, p). q \<in> set S_2 \<and> p \<in> set ( F_2) \<and> apart_ilist q p q_0_2}\<union> {(q, p). q \<in> set S_2 \<and> p \<in> {f} \<and> apart_ilist q p q_0_2}) "
     using fin 
     by linarith
     then have "norm_trd S_2 F_2 I q_0_2 \<le>norm_trd S_2 (f#F_2) I q_0_2" unfolding norm_trd_def ja change 
       by simp

    

     then show ?thesis  sorry
  qed

qed




lemma process_op_quer_not_none: "length (ip) = length op \<Longrightarrow>  otree_star (ip)   (process_output_query (ip) (op) (Node (acc,t)))\<noteq>None"
 proof (induction ip  arbitrary:op t acc )
   case Nil
   then show ?case  by auto 
 next
   case (Cons a ip)
   obtain ofs os where ofs: " op = os#ofs" using Cons apply auto 
     by (meson Suc_length_conv)

 
   then show ?case  proof (cases "t a")
     case None
 
       have " otree_star (ip) (process_output_query (ip) ofs (Node (acc@[a],(\<lambda> is. None)))) \<noteq> None" using Cons ofs   by auto 
       then obtain  lt lout where "otree_star (ip) (process_output_query (ip) ofs (Node (acc@[a],(\<lambda> is. None)))) = Some (lt,lout)" 
         by fast
       then have " otree_star (a # ip) (process_output_query (a # ip) op (Node (acc, t))) = Some (lt,os#lout)" using Cons ofs None   otree_induct_helper_none  by auto
     then show ?thesis by auto 
   next
     case (Some b)
    
     then show ?thesis  proof (cases b)
       case (Pair tree c )
       
       have " otree_star (ip) (process_output_query (ip) ofs tree) \<noteq> None" using Cons ofs   apply auto 
         by (metis obs_tree.exhaust surj_pair) 
       then obtain lt lout where "otree_star (ip) (process_output_query (ip) ofs tree) = Some (lt,lout)" 
         by fast
       then have " otree_star (a # ip) (process_output_query (a # ip) op (Node (acc, t))) = Some (lt,c#lout)" using Cons ofs Some Pair otree_induct_helper by auto
       then show ?thesis  by auto
     qed 
   qed
 qed 

lemma output_query_different:"length op=length (ip) \<Longrightarrow> i\<noteq>ac \<Longrightarrow>(case process_output_query (i#ip) (os#op) (Node (acc,t)) of (Node (accs,ts)) \<Rightarrow> ts ac=t ac)"
  by  (auto split:prod.splits option.splits)  


lemma otree_star_output_query_different:
  assumes"ac\<noteq>i " "length (ip) = length op " " t ac= Some (tree,outies)"
  shows " otree_star (ac#list) (process_output_query (i#ip) (os#op) (Node (acc,t)))  =(case otree_star list tree of Some (n,opl) \<Rightarrow> Some (n,outies#opl) | None \<Rightarrow> None) "
proof -
  
  have "(case process_output_query (i#ip) (os#op) (Node (acc,t)) of (Node (accs,ts)) \<Rightarrow> ts ac=t ac) "   using assms output_query_different[of op ip i ac] by auto
 
  then show ?thesis using assms(3) by (auto split:prod.splits option.splits) 
qed


lemma output_query_retains_some: assumes "length (ip) = length op" " otree_star (acc) q_0 \<noteq> None "
  shows" otree_star (acc) (process_output_query (ip) (op) (q_0)) \<noteq> None"
using assms proof (induction ip arbitrary:op acc q_0 )
  case Nil
  then show ?case 
    by simp
next
  case a:(Cons a ip)
obtain os ops where os: "op=os#ops" using a apply auto 
              by (meson Suc_length_conv) 
  then show ?case proof (cases acc)
    case Nil
    then show ?thesis by auto
  next
    case (Cons ac list)
    then show ?thesis   proof (cases q_0)
      case (Node x)
      then show ?thesis proof (cases x)
        case (Pair l r)
        then show ?thesis using a proof (cases "a=ac")
          case True 
          then show ?thesis proof (cases "r ac")
            case None
            then have "otree_star (ac#list) (q_0) =None" using Pair Node by auto
            then show ?thesis using a Cons
              by (simp)  
          next
            case (Some c)
              then  obtain tree outies where outies:"r ac = Some (tree,outies) " using Pair Node Cons a Some  
              by fastforce 
            then have h2: " otree_star (ac#list) (process_output_query (a # ip) (os#ops) q_0) =(case otree_star list (process_output_query ip ops tree) of Some (n,opl) \<Rightarrow> Some (n,outies#opl) | None \<Rightarrow> None)  "
              using Some True Pair Node Cons a
              using otree_star_output_query_different[of ac  a ip ops r tree outies list os ]  by auto 
            have h1:"otree_star (ac#list) q_0=(case otree_star  list tree of Some (n,opl) \<Rightarrow> Some (n,outies#opl) | None \<Rightarrow> None)"  using outies Pair Node by auto
            have "otree_star (ac#list) q_0 \<noteq> None" using a Cons 
              by blast
            then have "otree_star list tree\<noteq> None " using a h1 
              by (metis option.simps(4))
            then have "otree_star list (process_output_query ip ops tree)\<noteq> None " using a os 
              by force 
            then show ?thesis using h2 os Cons 
              by force
             
          qed
        next
          case False
         
          then show ?thesis proof (cases "r ac")
            case None
            then have "otree_star (ac#list) (q_0) =None" using Pair Node by auto
            then show ?thesis using a Cons
              by (simp)  
          next
            case (Some c)
            
            then  obtain tree outies where outies:"r ac = Some (tree,outies) " using Pair Node Cons a Some  
              by fastforce 
            then have h2: "otree_star (ac#list) (process_output_query (a#ip) (os#ops) q_0)  =(case otree_star list tree of Some (n,opl) \<Rightarrow> Some (n,outies#opl) | None \<Rightarrow> None) " using Some False Pair Node Cons a
              using otree_star_output_query_different[of ac  a ip ops r tree outies list os ] 
              apply auto by  (auto split:prod.splits option.splits)
            have h1:"otree_star (ac#list) q_0=(case otree_star  list tree of Some (n,opl) \<Rightarrow> Some (n,outies#opl) | None \<Rightarrow> None)"  using outies Pair Node by auto
            have "otree_star (ac#list) q_0 \<noteq> None" using a Cons 
              by blast
            then have "otree_star list tree \<noteq> None" using h1 
              by (metis option.simps(4))
            then show ?thesis using h2 Cons a 
              by (simp add: h1 os)
          qed
        qed
      qed
    qed
  qed
qed 

lemma trans_star_length:"trans_star  iss q_0 t=(q,os) \<Longrightarrow> length iss=length os"
proof (induction iss arbitrary:os q q_0)
  case Nil
  then show ?case by auto
next
  case (Cons a iss)
  then show ?case by (auto split:prod.splits option.splits)  
qed



lemma output_query_length:assumes "output_query m iss =os "shows" length iss=length os"
proof-
  obtain  q_0 Q t where m: "m=(q_0,Q,t)" 
    using prod_cases3 by blast
  then have "output_query  (q_0,Q,t) iss =os \<Longrightarrow> length iss=length os"using trans_star_length apply  (auto split:prod.splits option.splits)   
  by fastforce 
  then show ?thesis   using m  assms 
    by blast
qed



  
lemma rule_two_aux_retain_some: "otree_star is q_0 \<noteq> None \<Longrightarrow> otree_star (is) (rule_two_aux m  (Node (acc,t)) q_0 (iss)) \<noteq> None"
proof(induction iss)
  case Nil
  then show ?case by auto
next
  case (Cons a iss)
  have " rule_two_aux m  (Node (acc,t)) q_0 (a#iss) =  (if t a=None then( let (output) = output_query m (acc@[a]) in process_output_query (acc@[a]) (output)  (rule_two_aux m (Node (acc,t))  (  q_0 ) iss))   
else   rule_two_aux m  (Node (acc,t))  q_0 iss) " by auto 
  then show ?case proof(cases "t a")
    case None
    have decomp:" rule_two_aux m  (Node (acc,t)) q_0 (a#iss) = ( let (output) = output_query m (acc@[a]) in process_output_query (acc@[a]) (output)  (rule_two_aux m (Node (acc,t))  (  q_0 ) iss)) " 
      using None by auto 
    obtain out where out: "(out) = output_query m (acc@[a])" 
      by simp
    then have "length out=length (acc@[a])" using output_query_length 
      by metis
    
    then show ?thesis using Cons output_query_retains_some using decomp 
      by (metis out)
  next
    case (Some b)
    then have "rule_two_aux m  (Node (acc,t)) q_0 (a#iss) =   rule_two_aux m  (Node (acc,t))  q_0 iss" by auto 
    
    then show ?thesis using Cons Some 
      by argo
  qed
qed



lemma otree_star_split_none: assumes "t i = None"   "otree_star acc (Node (accq,tq)) = Some (Node (ac,t),ops)" 
  shows"otree_star (acc@[i]) (Node (accq,tq)) = None"
using assms proof(induction acc arbitrary:  ops accq  tq ac)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a acc)
  then show ?case  proof(cases "tq a")
    case None
    then show ?thesis using Cons 
      by auto
  next
    case (Some b)
    obtain tr on where b: "b=(tr,on)" 
      by fastforce
   then have apart_i:" otree_star ((a # acc@[i]) ) (Node (accq, tq)) = (case otree_star (acc@[i]) tr of Some (n,opl) \<Rightarrow> Some (n,on#opl) | None \<Rightarrow> None)" using Some 
      by auto
    then have apart:" otree_star ((a # acc) ) (Node (accq, tq)) = (case otree_star (acc) tr of Some (n,opl) \<Rightarrow> Some (n,on#opl) | None \<Rightarrow> None)" using Some b
      by auto

    then have " otree_star (acc) tr \<noteq>None" using Some Cons b 
      by (metis option.distinct(1) option.simps(4))
   
    then obtain opl where opl:" otree_star (acc) tr = Some (Node (ac,t),opl) " using Some Cons b apart 
      by fastforce
 obtain ntq nac where ntq: "tr=Node (nac,ntq)" 
   using b Some Cons 
   by (metis obs_tree.exhaust surj_pair)
    then have " otree_star (acc @ [i]) (Node (nac,ntq)) = None" using Cons opl 
      by blast 
    then show ?thesis using Cons b Some apart opl ntq apart_i 
      by auto 
  qed
qed


lemma otree_star_split: assumes "t i = Some (tree,op)"   "otree_star acc (Node (accq,tq)) = Some (Node (ac,t),ops)" 
  shows"otree_star (acc@[i]) (Node (accq,tq)) = Some (tree,ops@[op])"
using assms proof(induction acc arbitrary:  ops accq  tq ac)
  case Nil
  then show ?case 
    by fastforce
    
next
  case (Cons a acc)
  then show ?case  proof(cases "tq a")
    case None
    then show ?thesis using Cons 
      by auto
  next
    case (Some b)
    obtain tr on where b: "b=(tr,on)" 
      by fastforce
   then have apart_i:" otree_star ((a # acc@[i]) ) (Node (accq, tq)) = (case otree_star (acc@[i]) tr of Some (n,opl) \<Rightarrow> Some (n,on#opl) | None \<Rightarrow> None)" using Some 
      by auto
    then have apart:" otree_star ((a # acc) ) (Node (accq, tq)) = (case otree_star (acc) tr of Some (n,opl) \<Rightarrow> Some (n,on#opl) | None \<Rightarrow> None)" using Some b
      by auto

    then have " otree_star (acc) tr \<noteq>None" using Some Cons b 
      by (metis option.distinct(1) option.simps(4))
   
    then obtain opl where opl:" otree_star (acc) tr = Some (Node (ac,t),opl) " using Some Cons b apart 
      by fastforce
 obtain ntq nac where ntq: "tr=Node (nac,ntq)" 
   using b Some Cons 
   by (metis obs_tree.exhaust surj_pair)
    then have " otree_star (acc @ [i]) (Node (nac,ntq)) = Some (tree, opl @ [op])" using Cons opl 
      by blast 
    then show ?thesis using Cons b Some apart opl ntq apart_i 
      by auto 
  qed
qed


lemma rule_two_aux_split:"rule_two_aux  m (Node (acc,t))  q_0  (ifront@iback) = rule_two_aux m (Node (acc,t))  (rule_two_aux  m (Node (acc,t))  q_0  (iback)) ifront"
  by (induction ifront) fastforce+









lemma rule_two_aux_single_elim:
  assumes "otree_star acc q_0 =Some ((Node (accs,t)),ops)"
  shows  "otree_star (acc@[i])   (rule_two_aux  m (Node (acc,t))  q_0  ([i]))\<noteq>None"
proof-
  show ?thesis proof (cases "t i")
    case None
    obtain outp where op:"outp=output_query m (acc@[i])" 
      by blast
    then have a: "rule_two_aux  m (Node (acc,t))  q_0  ([i]) =    process_output_query (acc@[i]) (outp)  q_0" using None 
      by simp
    have "length outp=length (acc@[i])" using op output_query_length 
      by metis
    then have b:" otree_star (acc@[i]) (process_output_query (acc@[i]) (outp)  q_0)\<noteq> None" using  process_op_quer_not_none 
      by (metis obs_tree.exhaust surj_pair)
    have "otree_star (acc@[i])   (rule_two_aux  m (Node (acc,t))  q_0  ([i])) = otree_star (acc@[i]) (process_output_query (acc@[i]) (outp)  q_0)" using a 
      by auto

    then show ?thesis using b op 
      by argo
  next
    case (Some a)
    obtain out t2 where a:"a=(t2,out)" using Some  
      using prod.exhaust by blast
    have b:"otree_star (acc@[i])   (rule_two_aux  m (Node (acc,t))  q_0  ([i])) = otree_star (acc@[i]) q_0" 
      using Some by auto
     have " otree_star (acc@[i]) q_0 = Some (t2,ops@[out])  " using Some assms  otree_star_split a 
       by (smt (verit) otree_star.elims snoc_eq_iff_butlast)
    then show ?thesis using b 
      by simp
  qed 
qed


lemma rule_two_aux_single_elim_tail:
  assumes "otree_star acc q_0 =Some ((Node (accs,t)),ops)"
  shows  "otree_star (acc@[i])   (rule_two_aux  m (Node (acc,t))  q_0  ([i]@is))\<noteq>None"
proof -
  have "(rule_two_aux  m (Node (acc,t))  q_0  ([i]@is)) = 
(if t i=None then( let (output) = output_query m (acc@[i]) in process_output_query (acc@[i]) (output)  (rule_two_aux m (Node (acc,t))  (  q_0 ) is))   
else   rule_two_aux m  (Node (acc,t))  q_0 is) " 
    by simp
  show ?thesis proof(cases "t i=None")
    case True
    have "(rule_two_aux  m (Node (acc,t))  q_0  ([i]@is)) =( let (output) = output_query m (acc@[i]) in process_output_query (acc@[i]) (output)  (rule_two_aux m (Node (acc,t))  (  q_0 ) is))"
      using True 
      by simp
    
    then show ?thesis using process_op_quer_not_none 
      by (metis obs_tree.exhaust old.prod.exhaust output_query_length) 
  next
    case False
    have "otree_star (acc@[i]) q_0\<noteq> None " using False assms otree_star_split 
      by (metis rule_two_aux.simps(1) rule_two_aux.simps(2) rule_two_aux_single_elim)
    then show ?thesis using rule_two_aux_retain_some  
      by blast
  qed
qed

lemma rule_two_aux_works:
  assumes   "i\<in>set iss" "otree_star acc q_0 =Some ((Node (acc,t)),ops)" "otree_rec_4 q_0"
  shows "otree_star (acc@[i])   (rule_two_aux  m (Node (acc,t))  q_0  (iss))\<noteq>None"
using assms proof (induction iss )
  case Nil
  then show ?case   by auto
next
  case (Cons a ifollows)
  obtain pi ai where pi:"(a#ifollows)= pi@(i#ai)" using Cons 
    by (metis Cons_eq_appendI eq_Nil_appendI in_set_conv_decomp_first)
  have a:"rule_two_aux m (Node (acc,t)) (rule_two_aux m (Node (acc,t)) q_0 (i#ai)) pi = (rule_two_aux  m (Node (acc,t))  q_0  (a#ifollows)) " using rule_two_aux_split  pi 
    by metis
 
 
  have "otree_star acc ( rule_two_aux m (Node (acc,t)) q_0 (ai)) \<noteq> None" using rule_two_aux_retain_some assms 
    by fast 
  then have "otree_star (acc@[i])  (rule_two_aux m (Node (acc,t)) q_0 ([i]@ai)) \<noteq> None "  using  rule_two_aux_single_elim_tail   using assms 
    by fast
  then have "otree_star (acc@[i]) (rule_two_aux m (Node (acc,t)) (rule_two_aux m (Node (acc,t)) q_0 (i#ai)) pi) \<noteq> None " using rule_two_aux_retain_some 
    by (metis append_Cons self_append_conv2)

  then show ?case using a 
    by argo
qed


lemma  rule_two_retains_some:
"otree_rec q_0 S F I \<Longrightarrow>otree_star acc q_0\<noteq> None \<Longrightarrow> otree_star acc (rule_two m S q_0 I) \<noteq> None"
proof (induction S arbitrary: acc)
  case Nil
  then show ?case 
    by fastforce
next
  case (Cons a S)
  have orec:"otree_rec q_0 ( S) F I " using Cons unfolding  otree_rec_def otree_rec_1_def otree_rec_3_def otree_rec_5_def 
    by auto
  have "otree_star a q_0 \<noteq> None" using Cons unfolding otree_rec_def otree_rec_5_def 
    by force 
  then have "otree_star a (rule_two m S q_0 I) \<noteq> None" using Cons(1) orec 
    by blast
  then obtain tree op where "otree_star a (rule_two m S q_0 I) = Some (tree,op)" using Cons orec 
    by fast 
  then have a:"rule_two m (a#S) q_0 I=   rule_two_aux m tree (rule_two m S q_0 I) I" 
    by fastforce
   have "otree_rec q_0 S F I" using Cons(2) unfolding otree_rec_def otree_rec_1_def  otree_rec_3_def  otree_rec_4_def  otree_rec_5_def 
     by auto
   then have "otree_star acc (rule_two m S q_0 I) \<noteq> None" using Cons 
     by blast
   then have "otree_star acc ( rule_two_aux m tree (rule_two m S q_0 I) I)\<noteq> None" using rule_two_aux_retain_some 
     by (metis obs_tree.exhaust surj_pair) 
  then show ?case using a 
    by argo
qed


lemma process_op_q_invar:
  assumes "length inp = length otp " "q_0=(Node (acc,Map.empty))" " otree_star  iss (process_output_query inp otp q_0) = Some (Node (acc2,t),os ) "
  shows"acc2=acc@iss"
  using assms proof (induction iss arbitrary:inp otp acc acc2 os q_0 t)
  case Nil
  have "\<exists> t out. otree_star  [] (process_output_query inp otp q_0) = Some (Node (acc,t),out) " using  Nil by (induction inp otp q_0 rule: process_output_query.induct )  auto
  then obtain t2 out where some:" otree_star  [] (process_output_query inp otp q_0) = Some (Node (acc,t2),out) " 
    by presburger
  then have "acc2=acc" using some Nil 
    by force
  then show ?case using Nil  
    by fast
next
  case cons1:(Cons i1 iss)
  then show ?case proof (induction inp otp q_0 rule:process_output_query.induct)
    case (4 i2 ips op ops acc t)

    have "i1\<noteq>i2 \<Longrightarrow>  otree_star  (i1#iss) (process_output_query (i2#ips) (op#ops) (Node (acc,t))) = None  " using  Cons  4 
      by auto  
    then have i_eq:  "i1=i2" using 4 Cons 
      by fastforce  
    have "t=Map.empty" using 4 
      by fastforce
    then have two:" otree_star  (i1#iss) (process_output_query (i2#ips) (op#ops) (Node (acc,t))) =(case  otree_star iss (process_output_query ips ops (Node (acc@[i1],Map.empty))) of
None \<Rightarrow> None | Some (node,opi) \<Rightarrow> Some (node,op#opi))  " using i_eq  
      by auto
     then have "otree_star iss (process_output_query ips ops (Node (acc@[i1],Map.empty)))\<noteq> None  " using cons1  4 
       by (metis option.distinct(1) option.simps(4))
     then have "\<exists> acc3 t3 outs. otree_star iss (process_output_query ips ops (Node (acc@[i1],Map.empty))) = Some (Node (acc3,t3),outs)" 
       by (metis obs_tree.exhaust old.prod.exhaust option.exhaust)
     then obtain acc3 t3 outs where b: " otree_star iss (process_output_query ips ops (Node (acc@[i1],Map.empty))) = Some (Node (acc3,t3),outs)" 
       by blast
     have a:"length ips=length ops" using 4 
       by simp
     then have "acc3=acc@[i1]@iss" using   b cons1.IH[of ips ops _ "acc@[i1]" acc3 t3 outs] 
       by auto
    
    then show ?case using i_eq two  4 b 
      by force
  qed auto
 
qed

 
lemma process_op_q_otree_4: "length inp=length otp\<Longrightarrow>   otree_star is (Node (acc,t)) = Some ((Node (pos,t2)),os) \<longrightarrow> pos=acc@is \<Longrightarrow> 
   otree_star is (process_output_query (inp) (otp) (Node (acc,t))) = Some ((Node (pos,t2)),os) \<longrightarrow> pos=acc@is"
proof (induction inp arbitrary:otp acc t)
  case Nil
  then show ?case 
    by simp
next
  case c:(Cons i ips)
  then obtain op ops where os: "otp=op#ops" 
    by (metis length_Suc_conv)
   have one: " (process_output_query (i#ips) (op#ops) (Node (acc,t))) =(case t i of None\<Rightarrow> (Node (acc, (\<lambda> j. if j=i then Some ( process_output_query ips ops (Node (acc@[i],(\<lambda> k. None))),op)  else  t j))) 
| Some (tree,out) \<Rightarrow>  (Node (acc, (\<lambda>j. if j=i then Some ((process_output_query ips ops tree),out) else t j)) ))" 
     by auto 
  then show ?case proof (cases "t i")
    case None
    then have " (process_output_query (i#ips) (op#ops) (Node (acc,t))) = (Node (acc, (\<lambda> j. if j=i then Some ( process_output_query ips ops (Node (acc@[i],(\<lambda> k. None))),op)  else  t j))) " 
      by simp
    then have simpies:"otree_star is (process_output_query (i#ips) (op#ops) (Node (acc,t))) =otree_star is (Node (acc, (\<lambda> j. if j=i then Some ( process_output_query ips ops (Node (acc@[i],(\<lambda> k. None))),op)  else  t j))) "
      by argo
      then show ?thesis using c proof(induction "is" )
        case Nil
        then show ?case using Cons os 
          by force
      next
        case (Cons a "is")
          
        then show ?case proof (cases "a=i")
          case True
          have "length ips=length ops" using c os 
            by auto
          then have now:"\<forall> os4. otree_star is ( process_output_query ips ops (Node (acc@[i],(\<lambda> k. None)))) = Some ((Node (pos,t2)),os4) \<longrightarrow> pos=acc@[a]@is "  using process_op_q_invar  True
            by fastforce
          have "otree_star (a#is) (process_output_query (i#ips) (op#ops) (Node (acc,t))) =otree_star (a#is) (Node (acc, (\<lambda> j. if j=i then Some ( process_output_query ips ops (Node (acc@[i],(\<lambda> k. None))),op)  else  t j))) "
            using simpies Cons 
            by blast
          also have "\<dots>= (case (\<lambda> j. if j=i then Some ( process_output_query ips ops (Node (acc@[i],(\<lambda> k. None))),op)  else  t j) i of Some (n,op) \<Rightarrow> (case (otree_star is n) of Some (ot,ops) \<Rightarrow> Some (ot,op#ops)| None \<Rightarrow> None ) | None \<Rightarrow> None) " using True 
            by auto
          also have "\<dots>=(case otree_star is ( process_output_query ips ops (Node (acc@[a],(\<lambda> k. None)))) of Some (ot,ops) \<Rightarrow> Some (ot,op#ops)| None \<Rightarrow> None )" using True 
            by simp
       
          finally show ?thesis using now True  apply  (auto split:prod.splits option.splits) 
            using os by auto            
        next
          case False
          then show ?thesis using Cons c os
 
            by simp
        qed
      qed
  next
    case s: (Some a)
    then obtain tree out where tree:"a=(tree,out)" 
      by fastforce
    then have " (process_output_query (i#ips) (op#ops) (Node (acc,t))) = 
 (Node (acc, (\<lambda>j. if j=i then Some ((process_output_query ips ops tree),out) else t j)) )" using s using c
      by auto
    then show ?thesis using c  proof (induction "is")
      case Nil
      then show ?case using os 
        by auto
    next
      case (Cons a "is")
      then show ?case proof (cases "a=i")
        case True
        have "length ips=length ops " using c os 
          by fastforce
        have c_1: "otree_star (a#is) (Node (acc,t)) = (case t i of Some (n,op) \<Rightarrow> (case (otree_star is n) of Some (ot,ops) \<Rightarrow> Some (ot,op#ops)| None \<Rightarrow> None ) | None \<Rightarrow> None)  "
          using True 
          by simp
        also have c_2: "\<dots>= (case (otree_star is tree) of Some (ot,ops) \<Rightarrow> Some (ot,out#ops)| None \<Rightarrow> None )" using tree s 
          by simp
        finally  have fin: "\<forall> pos3 t3 os3. otree_star is  tree = Some ((Node (pos3,t3)),os3)\<and> otree_star (a#is) (Node (acc,t)) =Some (Node (pos,t2),os) \<longrightarrow> pos=pos3  " using c  
          by force  
      

        have "otree_star (a#is) (Node (acc,t)) =Some (Node (pos,t2),os) \<longrightarrow> pos=acc@(a#is)" using Cons(5) 
          by blast
       
          
        have "otree_star (a#is) (process_output_query (i#ips) (op#ops) (Node (acc,t))) =otree_star (a#is) (Node (acc, (\<lambda>j. if j=i then Some ((process_output_query ips ops tree),out) else t j)) ) "
            using  Cons tree os  s c tree 
            by argo
          
          also have "\<dots>= (case (\<lambda>j. if j=i then Some ((process_output_query ips ops tree),out) else t j) i of Some (n,op) \<Rightarrow> (case (otree_star is n) of Some (ot,ops) \<Rightarrow> Some (ot,op#ops)| None \<Rightarrow> None ) | None \<Rightarrow> None)"            
            using True by auto
           also have "\<dots>=(case otree_star is (process_output_query ips ops tree) of Some (ot,ops) \<Rightarrow> Some (ot,out#ops)| None \<Rightarrow> None )" using True 
             by auto 
           
           finally show ?thesis using os Cons True c s   proof (cases "otree_star (a # is)  (process_output_query (i#ips) (op#ops) (Node (acc,t)))")
             case None
             then show ?thesis 
               by (simp add: os)
               
           next
             case (Some b)
             have c1: "otree_star (a#is) (Node (acc,t)) = (case t i of Some (n,op) \<Rightarrow> (case (otree_star is n) of Some (ot,ops) \<Rightarrow> Some (ot,op#ops)| None \<Rightarrow> None ) | None \<Rightarrow> None)  "
          using True 
          by simp 
          also have  "\<dots>= (case (otree_star is tree) of Some (ot,ops) \<Rightarrow> Some (ot,out#ops)| None \<Rightarrow> None )" using tree s 
            by simp
          then have "otree_star (a#is) (Node (acc,t)) =(case (otree_star is tree) of Some (ot,ops) \<Rightarrow> Some (ot,out#ops)| None \<Rightarrow> None )" using c1 
            by argo
          
          
             then have "otree_star is tree\<noteq>None"  using Some sorry
             then have "os\<noteq>[]" using Cons c_1 c_2  sorry
             then obtain os3  where "os=out#os3" using Cons  Some os tree     sorry
             then have sr:" otree_star is tree = Some (Node (pos, t2),os3) \<longrightarrow> otree_star (a # is) (Node (acc, t)) = Some (Node (pos, t2), os)" using Some tree c_1 c_2 
               by simp    
             then show ?thesis sorry
           qed
            
            
      next
        case False
        then show ?thesis using Cons os 
          by fastforce
      qed
    qed
  qed
qed


lemma rec_4_poq: assumes "length inp=length otp"" otree_rec_4 q_0 "
  shows"otree_rec_4 (process_output_query (inp) (otp) q_0)"
proof -
   show ?thesis using assms process_op_q_otree_4 unfolding  otree_rec_4_def 
    by (smt (verit, ccfv_threshold) eq_Nil_appendI length_0_conv otree_star.simps(1) process_output_query.elims process_output_query.simps(1))
qed 

lemma rec_4_two_aux: "otree_rec_4 q_0 \<Longrightarrow> otree_rec_4  (rule_two_aux  m (Node (acc,t))  q_0  (iss))"
proof(induction iss)
  case Nil
  then show ?case unfolding otree_rec_def 
    by simp
next
  case (Cons i I)
  have a:"(rule_two_aux  m (Node (acc,t))  q_0  (i#I)) =(if t i=None then( let (output) = output_query m (acc@[i]) in process_output_query (acc@[i]) (output)  (rule_two_aux m (Node (acc,t))  (  q_0 ) I))   
else   rule_two_aux m  (Node (acc,t))  q_0 I)  " 
    by simp
  then show ?case proof (cases "t i")
    case None
    then show ?thesis using rec_4_poq Cons a 
      by (metis output_query_length) 
  next
    case (Some a)
    then have "(rule_two_aux  m (Node (acc,t))  q_0  (i#I)) = rule_two_aux m  (Node (acc,t))  q_0 I" 
      by simp
    then show ?thesis using Cons 
      by presburger
  qed
qed


lemma  rec_4_rule2:"otree_rec q_0 S F I \<Longrightarrow> otree_rec_4 (rule_two m S q_0 I)"
proof(induction S arbitrary: q_0)
  case Nil
  then show ?case unfolding otree_rec_def 
    by simp
next
  case (Cons a S)
  have a:"rule_two m (a # S) q_0 I = (let node = (rule_two m S q_0 I) in  (case   otree_star a node  of Some (tree,op) \<Rightarrow>   rule_two_aux m tree node I|None \<Rightarrow> undefined))" 
    by simp
    have b:" otree_star a q_0 \<noteq> None" using Cons unfolding  otree_rec_def otree_rec_1_def otree_rec_3_def otree_rec_5_def 
      by simp
    then obtain tree op where tree:"otree_star a q_0 = Some (tree,op)" 
      by fast
    have c: "otree_rec q_0 ( S) F I" using Cons unfolding   otree_rec_def otree_rec_1_def otree_rec_3_def otree_rec_5_def   
      by auto
    then  have "  otree_rec_4 (rule_two m S q_0 I) " using Cons  tree 
      by blast
  then show ?case    using rec_4_two_aux  a tree 
    by (metis (no_types, lifting) c case_prod_conv not_None_eq obs_tree.exhaust option.simps(5) rule_two_retains_some surj_pair)
qed

lemma rule_two_no_nones:
  assumes "otree_rec q_0 S F I" "i\<in> set I" "acc\<in> set S"
  shows "otree_star (acc@[i]) (rule_two m S q_0 I)\<noteq> None"
using assms proof (induction S)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a S)
  have "otree_star acc q_0\<noteq>None" using assms unfolding otree_rec_def otree_rec_5_def 
    by fast
  then obtain t out accies where star: "otree_star acc q_0=Some (Node (accies,t),out)" 
    by (metis obs_tree.exhaust option.exhaust surj_pair)
  then have accies:"accies=acc" using assms(1) unfolding otree_rec_def otree_rec_4_def 
    by fast
  have a:"otree_rec q_0 S F I" using Cons(2) unfolding otree_rec_def otree_rec_1_def  otree_rec_3_def  otree_rec_4_def  otree_rec_5_def 
    by auto
  have "otree_star a q_0 \<noteq> None" using Cons unfolding otree_rec_def otree_rec_5_def 
    by force 
  then have "   otree_star a (rule_two m S q_0 I) \<noteq> None"  using rule_two_retains_some  Cons 
      using a by blast
  then obtain tree op where op:"otree_star a (rule_two m S q_0 I) = Some (tree,op)" 
    by fast 
  then obtain accn tn where tn: "tree=Node (accn,tn)" 
    using obs_tree.exhaust by auto
have r:"otree_rec_4 (rule_two m S q_0 I) " using  Cons(2) unfolding otree_rec_def 
      using a rec_4_rule2 by blast
  have acca:"accn=a" using r unfolding otree_rec_4_def using op tn 
    by blast
  then have b:"rule_two m (a#S) q_0 I=   rule_two_aux m tree (rule_two m S q_0 I) I" using op
    by simp
  then show ?case proof (cases "acc\<in>set S")
    case True
    then have "otree_star (acc@[i]) (rule_two m S q_0 I) \<noteq> None" using Cons a  
      by fastforce
    
    then show ?thesis using   b rule_two_aux_retain_some[of "acc@[i]" "(rule_two m S q_0 I)" m accn tn I] tn 
      by argo

  next
    case False

    then have aeqacc:"a=acc" using Cons  False
      by force
 
    
    
    have  simp:" (rule_two m (a # S) q_0 I) =  (let node = (rule_two m S q_0 I) in  (case   otree_star a node  of Some (tree,op) \<Rightarrow>   rule_two_aux m tree node I|None \<Rightarrow> undefined))" 
      by simp
    
   
  
    
    then have "otree_star (acc@[i]) ( rule_two_aux m (Node (acc, tn)) (rule_two m S q_0 I) I) \<noteq> None " using rule_two_aux_works[of i I acc "(rule_two m S q_0 I)" tn op m]  Cons(3) r  
      using acca aeqacc op tn by auto 

    then show ?thesis using simp 
      using acca aeqacc b tn by fastforce     
  qed
qed

lemma norm_split:"norm S F I q_0 = norm_fst S F I q_0+ norm_scd S F I q_0+ norm_trd S F I q_0" unfolding norm_def norm_fst_def norm_scd_def norm_trd_def 
  by fast


lemma card_diff:" finite A \<Longrightarrow>card ((A)-B) \<le> card A"unfolding card_def  
  by (metis Diff_subset card_def card_mono)    


theorem  assumes   "otree_rec q_0 S F I" "(n_S,n_F,n_q_0) =rule_two_three_op m S q_0 I"
  shows    "norm S F I q_0 \<le> norm n_S n_F I n_q_0 "
proof -
  have "length S = length n_S" using assms apply auto 
    by (metis prod.inject)
  have  nS:"S=n_S" using assms(2)     by (metis prod.inject rule_two_three_op.simps)
  then have fst:"norm_fst S F I q_0 = norm_fst n_S n_F I n_q_0 " unfolding norm_fst_def by auto
  have "rule_two_three_op m S q_0 I =(let q_0_new= rule_two m S q_0 I in ( S,find_f S S I q_0_new, q_0_new ))" 
    by simp
  have nq0:"n_q_0=( rule_two m S q_0 I)" using assms 
    by (metis prod.inject rule_two_three_op.simps)
  have "{(q, i). q \<in> set n_S \<and> i \<in> set I \<and> otree_star (q @ [i]) n_q_0 \<noteq> None}= {(q, i). q \<in> set n_S \<and> i \<in> set I}-{(q,i). q \<in> set n_S \<and> i \<in> set I \<and> otree_star (q @ [i]) ( rule_two m S q_0 I) = None }" 
    using assms(1) nq0 by fastforce
 then have card:"card {(q, i). q \<in> set n_S \<and> i \<in> set I \<and> otree_star (q @ [i]) n_q_0 \<noteq> None}= card ({(q, i). q \<in> set n_S \<and> i \<in> set I}-  {(q,i). q \<in> set n_S \<and> i \<in> set I \<and> otree_star (q @ [i]) ( rule_two m S q_0 I) = None })" 
    using assms(1) nq0  
    by argo

  have "\<forall> q i. q \<in> set n_S \<and> i \<in> set I \<longrightarrow> otree_star (q @ [i]) ( rule_two m S q_0 I) \<noteq> None " using assms(1)   rule_two_no_nones[of q_0 S F I _ _ m]  using nS by auto   
  then have "{(q,i). q \<in> set n_S \<and> i \<in> set I \<and> otree_star (q @ [i]) ( rule_two m S q_0 I) = None } ={} " by auto 
  then have max:"(card {(q, i). q \<in> set n_S \<and> i \<in> set I \<and> otree_star (q @ [i]) n_q_0 \<noteq> None}) = card  {(q, i). q \<in> set n_S \<and> i \<in> set I} "using card nq0  Diff_empty 
    by (smt (verit))
  have second: " {(q, i). q \<in> set S \<and> i \<in> set I \<and> otree_star (q @ [i]) q_0 \<noteq> None} ={(q, i). q \<in> set S \<and> i \<in> set I}-{(q,i). q \<in> set S \<and> i \<in> set I \<and> otree_star (q @ [i]) ( q_0) = None } "
    by auto
  have "{(q, i). q \<in> set S \<and> i \<in> set I} = {(q, i). q \<in> set n_S \<and> i \<in> set I} " using nS 
    by simp
  have finite:"finite {(q, i). q \<in> set S \<and> i \<in> set I}" 
    by auto
  have "card ({(q, i). q \<in> set S \<and> i \<in> set I}-{(q,i). q \<in> set S \<and> i \<in> set I \<and> otree_star (q @ [i]) ( q_0) = None } ) \<le>  card  {(q, i). q \<in> set S \<and> i \<in> set I} "using  card_diff  finite
    by blast  
  then have scd: "norm_scd S F I q_0 \<le> norm_scd n_S n_F I n_q_0 " unfolding norm_scd_def using max card second nS 
    by fastforce   
  have trd:"norm_trd S F I q_0 =norm_trd  n_S n_F I n_q_0 " unfolding norm_trd_def  sorry
  have n1:"norm S F I q_0 =  norm_fst S F I q_0+ norm_scd S F I q_0+ norm_trd S F I q_0 " using norm_split 
    by auto
have n2:"norm n_S n_F I n_q_0 =  norm_fst n_S n_F I n_q_0+ norm_scd n_S n_F I n_q_0+ norm_trd n_S n_F I n_q_0 " using norm_split 
    by auto

   show ?thesis apply (simp add:n1 n2)  using fst scd trd  
     by simp
 qed

lemma otrree_1_find_f_aux: " e\<in>set (find_f_aux node S I) \<Longrightarrow> e\<notin>set S "
proof (induction node S I rule:find_f_aux.induct)
  case (1 uu uv)
  then show ?case 
    by simp
next
  case (2 acc t S i "is")
  then show ?case proof(cases " t i ")
    case None
    have "(find_f_aux (Node (acc, t)) S (i # is)) = (find_f_aux (Node (acc, t)) S ( is))" using None 
      by simp
    then show ?thesis  using 2 
      by argo
  next
    case (Some a)
    then obtain some thing b where "a=(Node (some,thing),b)" 
      by (metis obs_tree.exhaust old.prod.exhaust) 
    then have "(find_f_aux (Node (acc, t)) S (i # is)) =(   if acc@[i] \<in> set S then [] else [acc@[i]])@(find_f_aux (Node (acc, t)) S ( is))" using Some by auto 
    
    then show ?thesis using 2 
      by (smt (verit, ccfv_threshold) append_Cons append_self_conv2 set_ConsD)
  qed
qed


lemma rec1_aux: "otree_rec_5 q_0  ns \<Longrightarrow> e\<in>set (find_f (ns) S i  q_0) \<Longrightarrow> e\<notin>set S "
proof(induction ns S i q_0 rule:find_f.induct)
  case (1 uu uv uw)
  then show ?case 
    by simp
next
  case (2 n ns S i q_0)
 have "otree_star n q_0 \<noteq>None" using 2 unfolding otree_rec_5_def 
   by auto
  then obtain node op where op: "otree_star n q_0 = Some (node,op)" 
    by fast
 
  then have a:"find_f (n#ns) S i q_0 =  (find_f_aux node S i) @ (find_f ns S i q_0 )" 
    by auto
  have r5:"otree_rec_5 q_0  ns" using 2 unfolding otree_rec_5_def 
    by force
  then show ?case   proof(cases "e\<in>set (find_f ns S i q_0 )" )
    case True
    then show ?thesis using 2 op r5 
      by blast
  next
    case False
    have "e\<in>set (find_f_aux node S i)" using a False 2 
      by fastforce
    then show ?thesis using otrree_1_find_f_aux 
      by auto
  qed   
qed

lemma "otree_rec_5 q_0  ns \<Longrightarrow> otree_rec_1 S (find_f (ns) S i  q_0)"
  unfolding otree_rec_1_def using rec1_aux 
  by blast


theorem assumes  "otree_rec q_0 S F I" "(n_S,n_F,n_q_0) =rule_two_three_op m S q_0 I"
  shows "otree_rec n_q_0 n_S n_f I"
proof-
  have  nS:"S=n_S" using assms(2)     by (metis prod.inject rule_two_three_op.simps)
  have "n_F = find_f S S I n_q_0 " using assms(2)     by (metis prod.inject rule_two_three_op.simps)
  have "otree_rec_4 n_q_0 " using assms(2) rec_4_rule2 
    by (metis Pair_inject assms(1) rule_two_three_op.elims)
  have "otree_rec_1  n_S n_F" unfolding otree_rec_1_def  
