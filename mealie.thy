theory mealie
  imports Main
begin

sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

type_synonym ('state,'input,'output) transition ="(('state \<times>'input) \<Rightarrow> ('state \<times> 'output) )"

type_synonym ('state,'input,'output) mealie = "'state \<times> 'state set \<times> ('state,'input,'output) transition"




fun trans_star ::"'input list \<Rightarrow>'state \<Rightarrow> ('state,'input,'output) transition \<Rightarrow> ('state\<times>'output list)  " where
"trans_star [] q f =  (q,[])"|
"trans_star (w#ws) q f = (let  (st,op) =f (q,w)  in (let (q',x) = trans_star ws st f in  (q',op#x))) "



fun trans_star_output ::"'input list \<Rightarrow>'state \<Rightarrow> ('state,'input,'output) transition \<Rightarrow> ('output list)  " where
"trans_star_output (is) q f =  (let (q',op) = trans_star is q f in  op) "


fun trans_star_state ::"'input list \<Rightarrow>'state \<Rightarrow> ('state,'input,'output) transition \<Rightarrow> ('state)  " where
"trans_star_state (is) q f =  (case trans_star is q f of   (q',op) \<Rightarrow>  q') "


definition mealie_eq ::"('state, 'input, 'output) mealie \<Rightarrow>'state \<Rightarrow> ('state2, 'input, 'output) mealie \<Rightarrow> 'state2 \<Rightarrow> bool" where
"mealie_eq a q b  p \<equiv> (case (a,b) of ((q_0,S,f),(p_0,S_2,g)) \<Rightarrow> (\<forall> is. trans_star_output is q f = trans_star_output is p g))"

abbreviation equal :: "('state, 'input, 'output) mealie \<Rightarrow> ('state2, 'input, 'output) mealie \<Rightarrow> bool" (infixr "\<approx>" 80)
  where "a \<approx> b \<equiv>(case (a,b) of ((q_0,S,f),(p_0,S_2,g)) \<Rightarrow> mealie_eq a q_0 b p_0) "

definition mealie_invar ::"('state,'input,'output) mealie \<Rightarrow> bool" where 
"mealie_invar m = (case m of (q_0,S,t) \<Rightarrow>q_0\<in>S\<and>  (\<forall> q q' i out. q\<in>S \<and>(t (q,i) =  (q',out)) \<longrightarrow> q'\<in>S))"

definition func_sim ::"('state\<Rightarrow>'state2) \<Rightarrow>  ('state, 'input, 'output) mealie \<Rightarrow> ('state2, 'input, 'output) mealie \<Rightarrow> bool" where 
"func_sim f a b \<equiv> (case (a,b) of ((q_0,S,t),(p_0,S_2,g)) \<Rightarrow>   ( f q_0 = p_0)\<and>(\<forall> q q' i op. q\<in>S \<and> q'\<in>S \<and> t (q,i) =  (q',op) \<longrightarrow> g (f q,i) =  (f q',op))) "



lemma trans_star_output_t :"(trans_star_output (a#b) q t=  x) \<Longrightarrow>\<exists> op. (t (q,a) =  op)"
  by(auto) 


lemma split_trans_star_output:"t (q,i) =  (q',ot) \<Longrightarrow> trans_star_output is q' t = op \<Longrightarrow> trans_star_output (i#is) q t =  (ot#op)"
  by(auto split:prod.splits option.splits) 

lemma sim_subset :
  assumes "mealie_invar (q_0,S,t) " "mealie_invar (p_0,S_2,g)"  " func_sim f  (q_0,S,t) (p_0,S_2,g)" "q\<in>S" "trans_star_output i q t =  ot"
  shows"trans_star_output i (f q) g =  ot"
  using assms proof (induction i arbitrary: q ot )
  case Nil
  then show ?case 
    by fastforce
next
  case (Cons a i)
  have a: "\<forall> q' ot. t (q,a) =  (q',ot) \<longrightarrow> g (f q,a) =  (f q',ot) " using  assms(3) Cons(5) assms(1)  assms(2) unfolding mealie_invar_def func_sim_def
    apply auto  by metis
     

  have "\<exists> q' out.  t (q,a) =  (q',out)" using Cons trans_star_output_t try0
    by auto 
   
  then obtain  q' out where q: " t (q,a) =  (q',out)" using Cons trans_star_output_t 
    by fastforce
  then have "\<exists> os .ot= out#os" using Cons by (auto split:prod.splits option.splits) 
 
  then obtain os where ot: "ot= out#os" by auto
   then have " trans_star_output i q' t =  os \<Longrightarrow> trans_star_output i (f q') g =  os" using Cons.IH 
     Cons.prems(4) q assms(1) assms(2)  assms(3) unfolding mealie_invar_def by blast 

   then have "trans_star_output i q' t =  os \<Longrightarrow> trans_star_output i (f q') g =  os" by auto
   then have "trans_star_output (a#i) q t = (out#os) \<Longrightarrow> trans_star_output (a#i) (f q) g = (out#os)" using  a  q split_trans_star_output[of t q a q' out i os ] 
     by (auto split:prod.splits option.splits) 
 


  then show ?case using Cons q a  ot 
    by argo
qed

definition mealie_tree ::" ('state,'input,'output) mealie \<Rightarrow>bool" where 
"mealie_tree m = (case m of (q_0, Q,t) \<Rightarrow>\<forall> q. \<exists> \<sigma>. \<forall>  is. q\<in>Q\<and> (trans_star_state \<sigma> q_0 t = q) \<longrightarrow>  (trans_star_state is q_0 t \<noteq> q)) "


definition observation_tree :: "('state,'input,'output) mealie \<Rightarrow>('state2,'input,'output) mealie \<Rightarrow>  bool" where
"observation_tree t m \<equiv> \<exists> f. func_sim f t m \<and> mealie_tree t"


definition apart ::"('state,'input,'output) mealie \<Rightarrow> 'state \<Rightarrow>'state \<Rightarrow>bool" where 
"apart m q p \<equiv> (case m of(q_0, Q,t) \<Rightarrow> \<exists> i x y. trans_star_output i p t = x \<and> trans_star_output i q t=  y \<and> x\<noteq>y)"


definition apart_with_witness ::"('state,'input,'output) mealie \<Rightarrow> 'state \<Rightarrow>'state \<Rightarrow>'input list \<Rightarrow>bool" where 
"apart_with_witness m q p is \<equiv> (case m of(q_0, Q,t) \<Rightarrow> \<exists> x y. trans_star_output is p t = x \<and> trans_star_output is q t=  y \<and> x\<noteq>y)"

lemma simulation_apart:
  assumes  "func_sim f (q_0,Q,t)  (p_0,P,g)" "apart (q_0,Q,t) q q'"  "q\<in>Q" "q'\<in>Q" "mealie_invar (p_0,P,g)" "mealie_invar (q_0,Q,t) "
  shows "\<not>mealie_eq (p_0,P,g) (f q) (p_0,P,g) (f q')"
proof 
  assume"mealie_eq (p_0,P,g) (f q) (p_0,P,g) (f q')"
  then have c:"(\<forall> is. trans_star_output is (f q) g = trans_star_output is (f  q') g )" unfolding mealie_eq_def 
    by fastforce

   have "\<exists> w x y. trans_star_output w q t =  x \<and> trans_star_output w q' t=  y \<and> x\<noteq>y " using assms (2) unfolding apart_def 
     apply auto 
     by metis
   then obtain w x y where w: " trans_star_output w q t =  x \<and> trans_star_output w q' t=  y \<and> x\<noteq>y " 
     by blast
   then have a: " trans_star_output w (f q) g =  x"  using  assms sim_subset 
     by fast
   have b:" trans_star_output w (f q') g =  y"  using  w assms sim_subset 
     by meson
   have d:"x\<noteq>y" using w 
     by simp
   then show False using a b c d   
     by force
 qed


lemma weak_co_transitivity: 
  assumes "apart_with_witness (q_0,Q,t) r r' \<sigma>" "mealie_invar (q_0,Q,t)" "trans_star_output \<sigma> q t = x "
  shows "apart (q_0,Q,t) r q \<or> apart (q_0,Q,t) r' q "
proof (auto)
   show "\<not> apart (q_0, Q, t) r' q \<Longrightarrow> apart (q_0, Q, t) r q" using assms unfolding apart_def apart_with_witness_def  
    by blast 
qed


end
