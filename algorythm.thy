theory algorythm
  imports "./mealy"
begin

fun output_query ::"('state,'input,'output) mealy \<Rightarrow> 'input list \<Rightarrow> 'output list " where 
"output_query (q_0,Q,t) is= trans_star_output  t q_0 is"



definition eq_query :: " (('state,'input,'output) mealy \<Rightarrow> ('state2,'input,'output) mealy \<Rightarrow>(bool\<times>'input list)) \<Rightarrow>bool " where 
"eq_query f \<equiv> \<forall> m h x.(case (m,h) of ((q_0,Q,t),(p_0,P,g)) \<Rightarrow>  (if h\<approx>m then f h m = (True, []) else f h m= (False,x)\<and> trans_star_output t q_0 x \<noteq> trans_star_output g p_0 x ))   "
text "wieviel sinn macht die unterscheidung von state und state2"
text "wollen wir eine konkrete definition für Equiv query oder eine aussage über equiv query?"

text "gibt es eine sinvolle methode die existierenden states in die drei Teile S F und sonstige zu teilen?"


text"wie definieren wir hypothesen? F->S mit wir kennen keine eingabe \<sigma> mit \<sigma> \<stileturn> f#s" 

