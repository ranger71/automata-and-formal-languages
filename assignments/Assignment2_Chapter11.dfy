include "../lectures/AFL-week02.dfy"
include "../lectures/AFL-week08.dfy"

/* Chapter 11: Context-Free Grammars */
module Assignment2_Chapter11 {
	import opened Week01
	import opened Lecture02
	import opened Lecture08

	const EPSILON := Week01.EPSILON

	// Exercise 6(a):
	const alphabet6a := ['{', '[', '(', ')', ']', '}']
	predicate BalancedPrentheses(w: String)
		decreases |w|
	{
		|w| == 0 ||
		(var first, last := w[0], w[|w|-1];
		 ((first == '{' && last == '}') || (first == '[' && last == ']') || (first == '(' && last == ')')) &&
		 BalancedPrentheses(w[1..|w|-1]))
	}
	ghost const L6a := iset w,q | (forall w' :: w' in q ==> |w'| > 0 && ValidString(w', set c | c in alphabet6a) && BalancedPrentheses(w')) && w == SeqConcat(q) :: w

	// Goal: show a context-free grammar for the language L6a
	method {:verify false} Exercise6a() {
		var w6a1 := "({[{}]})(){{}}[[]]";
		assert w6a1 in L6a by {
			var q := ["({[{}]})", "()", "{{}}", "[[]]"];
			assert w6a1 == SeqConcat(q);
			assert forall w' :: w' in q ==> |w'| > 0 && ValidString(w', set c | c in alphabet6a) && BalancedPrentheses(w') by {
				var w0 := q[0];
				assert w0 == "({[{}]})";
				assert |w0| == 8;
				assert |w0| > 0 && |w0| % 2 == 0 && ValidString(w0, set c | c in alphabet6a) && BalancedPrentheses(w0) by {
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
				assert |q[1]| > 0 && ValidString(q[1], set c | c in alphabet6a) && BalancedPrentheses(q[1]);
				assert |q[2]| > 0 && ValidString(q[2], set c | c in alphabet6a) && BalancedPrentheses(q[2]);
				assert |q[3]| > 0 && ValidString(q[3], set c | c in alphabet6a) && BalancedPrentheses(q[3]);
			}
		}
	}

	function Exercise6a_solution(): CFG {
		var NT6a := [NT("S")];
		var T6a := [T('{'), T('['), T('('), T(')'), T(']'), T('}')];
		var V6a := NT6a + T6a;
		var rule1 := ("S", [NT("S"), NT("S")]);
		var rule2 := ("S", []);
		var rule3 := ("S", [T('{'), NT("S"), T('}')]);
		var rule4 := ("S", [T('['), NT("S"), T(']')]);
		var rule5 := ("S", [T('('), NT("S"), T(')')]);
		var R6a := [rule1, rule2, rule3, rule4, rule5];
		(V6a, alphabet6a, R6a, "S")
	}

	method {:verify false} Main() {
		var G6a := Exercise6a_solution();
		assert ValidCFG(G6a);
		SimulateCFG(G6a, 3);
	}
}
