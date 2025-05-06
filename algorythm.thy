theory algorythm
  imports "./mealie"
begin

fun output_query ::"('state,'input,'output) mealie \<Rightarrow> 'input list \<Rightarrow> 'output list " where 
"output_query (q_0,Q,t) is= (case trans_star_output  is q_0 t of Some os \<Rightarrow> os | None \<Rightarrow> undefined)"



definition eq_query :: " (('state,'input,'output) mealie \<Rightarrow> ('state2,'input,'output) mealie \<Rightarrow>(bool\<times>'input list)) \<Rightarrow>bool " where 
"eq_query f \<equiv> \<forall> m h x.(case (m,h) of ((q_0,Q,t),(p_0,P,g)) \<Rightarrow>  (if h\<approx>m then f h m = (True, []) else f h m= (False,x)\<and> trans_star_output x q_0 t \<noteq> trans_star_output x p_0 g ))   "





text "gibt es eine sinvolle methode die existierenden states in die drei Teile S F und sonstige zu teilen?"


text"wie definieren wir hypothesen? F->S mit wir kennen keine eingabe \<sigma> mit \<sigma> \<stileturn> f#s" 

