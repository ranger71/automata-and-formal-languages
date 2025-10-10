include "../simulators/PDA_Simulator.dfy"

/* Chapter 12: Pushdown Automata */
module Assignment2_Chapter12 {
	import opened FormalLanguages
	import opened PDA_Simulation

	// Exercise 1: pushdown automata
	const alphabet1a := ['{', '[', '(', ')', ']', '}']
	predicate BalancedPrentheses(w: String)
		decreases |w|
	{
		|w| == 0 ||
		(var first, last := w[0], w[|w|-1];
		 ((first == '{' && last == '}') || (first == '[' && last == ']') || (first == '(' && last == ')')) &&
		 BalancedPrentheses(w[1..|w|-1]))
	}
	ghost const L1a := iset w,q | (forall w' :: w' in q ==> |w'| > 0 && ValidString(w', set c | c in alphabet1a) && BalancedPrentheses(w')) && w == SeqConcat(q) :: w

	// Goal: show a context-free grammar for the language L1a
	method {:verify false} Exercise1a() {
		var w1a1 := "({[{}]})(){{}}[[]]";
		assert w1a1 in L1a by {
			var q := ["({[{}]})", "()", "{{}}", "[[]]"];
			assert w1a1 == SeqConcat(q);
			assert forall w' :: w' in q ==> |w'| > 0 && ValidString(w', set c | c in alphabet1a) && BalancedPrentheses(w') by {
				var w0 := q[0];
				assert w0 == "({[{}]})";
				assert |w0| == 8;
				assert |w0| > 0 && |w0| % 2 == 0 && ValidString(w0, set c | c in alphabet1a) && BalancedPrentheses(w0) by {
					assert w0[0] == '(' && w0[7] == ')';
					var w0b := w0[1..7];
					assert w0b == "{[{}]}";
					assert |w0b| == 6;
					assert BalancedPrentheses(w0b) by {
						assert w0b[0] == '{' && w0b[5] == '}';
						var w0c := w0b[1..5];
						assert w0c == "[{}]";
						assert |w0c| == 4;
						assert BalancedPrentheses(w0c) by {
							assert w0c[0] == '[' && w0c[3] == ']';
							var w0d := w0c[1..3];
							assert w0d == "{}";
							assert |w0d| == 2;
							assert BalancedPrentheses(w0d[1..1]) by {
								assert w0d[0] == '{' && w0d[1] == '}';
							}
						}
					}
				}
				assert |q[1]| > 0 && ValidString(q[1], set c | c in alphabet1a) && BalancedPrentheses(q[1]);
				assert |q[2]| > 0 && ValidString(q[2], set c | c in alphabet1a) && BalancedPrentheses(q[2]);
				assert |q[3]| > 0 && ValidString(q[3], set c | c in alphabet1a) && BalancedPrentheses(q[3]);
			}
		}
	}

	// Goal: complete this initial solution by adding further rules to the grammar
	function Exercise1a_solution(): PDA {
		var K1a := [1];
		var Sigma1a := ['{', '[', '(', ')', ']', '}'];
		var Gamma1a := ['{', '[', '('];
		var DELTA1a: PDA_TransitionRelation := 
			[((1, sym('{'), EPSILON), (1, "{")),
			 ((1, sym('['), EPSILON), (1, "[")),
			 ((1, sym('('), EPSILON), (1, "(")),
			 ((1, sym('}'), "{"), (1, EPSILON)),
			 ((1, sym(']'), "["), (1, EPSILON)),
			 ((1, sym(')'), "("), (1, EPSILON))];
		var s1a: State := 1;
		var A1a: seq<State> := [1, 2];
		(K1a, Sigma1a, Gamma1a, DELTA1a, s1a, A1a)
	}

	method {:verify false} Main()
		decreases *
	{
		var M1a := Exercise1a_solution();
		assert ValidPDA(M1a) && ValidString("", set c | c in PDA_Sigma(M1a));
		var accepted := pdasimulate(M1a, "");
		assert accepted;
		var q := ["({[{}]})", "()", "{{}}", "[[]]"];
		var w := SeqConcat(q);
		assert ValidPDA(M1a) && ValidString(q[1], set c | c in PDA_Sigma(M1a));
		accepted := pdasimulate(M1a, q[1]);
		assert accepted;
		var w1a2 := "{[}]";
		assert ValidPDA(M1a) && ValidString(w1a2, set c | c in PDA_Sigma(M1a));
		accepted := pdasimulate(M1a, w1a2);
		assert !accepted;
	}
}
