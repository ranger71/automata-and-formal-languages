include "AFL-week02.dfy"

module Tutorial03 {
	import opened Week01
	import opened Lecture02

	// exercise: draw a FSM that accepts the language over the alphabet {'a','b'} such that immediately after each occurrence of 'a', there is a 'b'
	ghost const L1 := iset w: String | ValidString(w, Alphabet_a_b) &&
		forall i :: 0 <= i < |w| && w[i] == 'a' ==> i+1 < |w| && w[i+1] == 'b'

	method M1() {
		assert EPSILON in L1;
		assert "bbbbb" in L1;
		assert "abbbbabbb" in L1;
		assert "a" !in L1 by { var i, w := 0, "a"; assert i < |w| && w[i] == 'a' && !(i+1 < |w| && w[i+1] == 'b'); }
		assert "aa" !in L1 by { var i, w := 0, "aa"; assert i < |w| && w[i] == 'a' && !(i+1 < |w| && w[i+1] == 'b'); }
		assert "aabbab" !in L1 by { var i, w := 0, "aabbab"; assert i < |w| && w[i] == 'a' && !(i+1 < |w| && w[i+1] == 'b'); }
	}
}

module Lecture03 {
	import opened Week01
	import opened Lecture02

	// DFSM definitions
	type State = nat

	type TransitionFunction = (State, Symbol) --> State
	type DFSM = (set<State>, set<Symbol>, TransitionFunction, State, set<State>)

	function K(M: DFSM): set<State> { M.0 }
	function Sigma(M: DFSM): set<Symbol> { M.1 }
	function Delta(M: DFSM): TransitionFunction { M.2 }
	function s(M: DFSM): State { M.3 }
	function A(M: DFSM): set<State> { M.4 }

	// DFSM properties:
	ghost predicate ValidDFSM(M: DFSM) {
		s(M) in K(M) && A(M) <= K(M) && forall k, c :: k in K(M) && c in Sigma(M) ==> Delta(M).requires(k, c) && Delta(M)(k, c) in K(M)
	}

	ghost function L(M: DFSM): Language // iset<String>
	{
		iset w: String | ValidString(w, Sigma(M)) && AcceptedByDFSM(w, M)
	}

	ghost predicate AcceptedByDFSM(w: String, M: DFSM)
	{
		ValidDFSM(M) && ValidString(w, Sigma(M)) && Yield_Full(w, M) in A(M)
	}

	ghost function Yield_Full(w: String, M: DFSM): (res: State)
		requires ValidDFSM(M) && ValidString(w, Sigma(M))
		ensures res in K(M)
	{
		Yield_Full_From(w, s(M), M)
	}

	ghost function Yield_Full_From(w: String, state: State, M: DFSM): (res: State)
		requires ValidDFSM(M) && state in K(M) && ValidString(w, Sigma(M))
		ensures res in K(M)
	{
		if |w| == 0 then state
		else
			var c := w[0];
			var next_w := w[1..];
			assert Delta(M).requires(state, c);
			var next_state := Delta(M)(state, c);
			Yield_Full_From(next_w, next_state, M)
	}

	// Slide 11
	/*
		(q0, "235") |- (q0, "35")
		            |- (q1, "5")
						|- (q1, "")

		and since q1 is an accepting state, the string "235" is accepted by the FSM, it is "in the language" of that machine
	*/

	// Slide 12: regular language definition
	type RegularLanguage = lang: Language | exists M: DFSM :: L(M) == lang witness *

	// Example 5.4 in the textbook - a finite state machine that accepts all binary numbers having "odd parity": with an odd number of occurrences of the digit '1'
	ghost const L_5_4 := iset w | ValidString(w, Alphabet_0_1) && Count('1', w) % 2 == 1
	const q0: State := 0 // the actual number for each state does not really matter, it's just an identifier
	const q1: State := 1
	const K_5_4 := {0,1}
	const Sigma_5_4 := {'0', '1'}
	function delta_5_4(k: State, c: Symbol): State
		requires k in K_5_4 && c in Sigma_5_4
	{
		if k == q0 && c == '0' then q0
		else if k == q0 && c == '1' then q1
		else if k == q1 && c == '0' then q1
		else assert k == q1 && c == '1'; q0
	}
	const s_5_4 := q0
	const A_5_4 := {q1}
	const M_5_4 := (K_5_4, Sigma_5_4, delta_5_4, s_5_4, A_5_4)
	
	lemma Lemma_5_4()
		ensures L(M_5_4) == L_5_4
	{
		forall w | ValidString(w, Alphabet_0_1) ensures w in L_5_4 <==> w in L(M_5_4) {
			if |w| == 0 {
				assert w !in L_5_4 by { assert Count('1', w) == 0; }
				assert w !in L(M_5_4) by { assert Yield_Full_From(w, q0, M_5_4) == q0 && q0 !in A(M_5_4);}
			}
			else {
				assert |w| > 0;
				var c := w[0];
				var next_w := w[1..];
				assert ValidString(next_w, Sigma(M_5_4));
				var next_state := Delta(M_5_4)(q0, c);
				calc {
					w in L(M_5_4);
				==
					ValidString(w, Sigma(M_5_4)) && AcceptedByDFSM(w, M_5_4);
				==
					Yield_Full(w, M_5_4) in A(M_5_4);
				==
					Yield_Full_From(w, s(M_5_4), M_5_4) in A(M_5_4);
				==
					Yield_Full_From(w, q0, M_5_4) in A(M_5_4);
				== { Lemma_5_4_q0(w); }
					Count('1', w) % 2 == 1;
				==
					w in L_5_4;
				}
			}
		}
	}

	lemma Lemma_5_4_q0(w: String)
		requires ValidString(w, Alphabet_0_1)
		ensures Count('1', w) % 2 == 1 <==> Yield_Full_From(w, q0, M_5_4) in A(M_5_4)
		decreases |w|
	{
		if |w| == 0 {
			assert Count('1', w) % 2 == 0;
			assert Yield_Full_From(w, q0, M_5_4) == q0 && q0 !in A(M_5_4);
		}
		else {
			assert ValidString(w, Alphabet_0_1);
			assert |w| > 0;
			var c := w[0];
			var next_w := w[1..];
			assert ValidString(next_w, Alphabet_0_1);
			var next_state := Delta(M_5_4)(q0, c);
			if w[0] == '0' {
				calc {
					Yield_Full_From(w, q0, M_5_4) in A(M_5_4);
				==
					Yield_Full_From(next_w, next_state, M_5_4) in A(M_5_4);
				== { assert next_state == delta_5_4(q0, '0') == q0; Lemma_5_4_q0(next_w); }
					Count('1', next_w) % 2 == 1;
				== { assert w == ['0'] + next_w; }
					Count('1', w) % 2 == 1;
				}
			}
			else {
				calc {
					Yield_Full_From(w, q0, M_5_4) in A(M_5_4);
				==
					Yield_Full_From(next_w, next_state, M_5_4) in A(M_5_4);
				== { assert next_state == delta_5_4(q0, '1') == q1; Lemma_5_4_q1(next_w); }
					Count('1', next_w) % 2 == 0;
				== { assert w == ['1'] + next_w; }
					Count('1', w) % 2 == 1;
				}
			}
		}
	}

	lemma Lemma_5_4_q1(w: String)
		requires ValidString(w, Alphabet_0_1)
 		ensures Count('1', w) % 2 == 0 <==> Yield_Full_From(w, q1, M_5_4) in A(M_5_4)
		decreases |w|
	{
		if |w| == 0 {
			assert Count('1', w) % 2 == 0;
			assert Yield_Full_From(w, q1, M_5_4) == q1 && q1 in A(M_5_4);
		}
		else {
			assert ValidString(w, Alphabet_0_1);
			assert |w| > 0;
			var c := w[0];
			var next_w := w[1..];
			assert ValidString(next_w, Alphabet_0_1);
			var next_state := Delta(M_5_4)(q1, c);
			if w[0] == '0' {
				calc {
					Yield_Full_From(w, q1, M_5_4) in A(M_5_4);
				==
					Yield_Full_From(next_w, next_state, M_5_4) in A(M_5_4);
				== { assert next_state == delta_5_4(q1, '0') == q1; Lemma_5_4_q1(next_w); }
					Count('1', next_w) % 2 == 0;
				== { assert w == ['0'] + next_w; }
					Count('1', w) % 2 == 0;
				}
			}
			else {
				calc {
					Yield_Full_From(w, q1, M_5_4) in A(M_5_4);
				==
					Yield_Full_From(next_w, next_state, M_5_4) in A(M_5_4);
				== { assert next_state == delta_5_4(q1, '1') == q0; Lemma_5_4_q0(next_w); }
					Count('1', next_w) % 2 == 1;
				== { assert w == ['1'] + next_w; }
					Count('1', w) % 2 == 0;
				}
			}
		}
	}

	lemma Lemma_5_4_with_short_proof()
		ensures L(M_5_4) == L_5_4
	{
		forall w | ValidString(w, Alphabet_0_1) ensures w in L_5_4 <==> w in L(M_5_4) {
			Lemma_5_4_q0_with_short_proof(w);
		}
	}

	lemma Lemma_5_4_q0_with_short_proof(w: String)
		requires ValidString(w, Alphabet_0_1)
		ensures Count('1', w) % 2 == 1 <==> Yield_Full_From(w, q0, M_5_4) in A(M_5_4)
		decreases |w|
	{
		if |w| > 0 {
			assert ValidString(w, Alphabet_0_1);
			var c := w[0];
			var next_w := w[1..];
			Lemma_5_4_q0_with_short_proof(next_w);
			var next_state := Delta(M_5_4)(q0, c);
			if w[0] == '0' {
				Lemma_5_4_q0_with_short_proof(next_w);
				assert w == ['0'] + next_w;
			}
			else {
				Lemma_5_4_q1_with_short_proof(next_w);
				assert w == ['1'] + next_w;
			}
		}
	}

	lemma Lemma_5_4_q1_with_short_proof(w: String)
		requires ValidString(w, Alphabet_0_1)
 		ensures Count('1', w) % 2 == 0 <==> Yield_Full_From(w, q1, M_5_4) in A(M_5_4)
		decreases |w|
	{
		if |w| > 0 {
			var c := w[0];
			var next_w := w[1..];
			if w[0] == '0' {
				Lemma_5_4_q1_with_short_proof(next_w);
				assert w == ['0'] + next_w;
			}
			else {
				Lemma_5_4_q0_with_short_proof(next_w);
				assert w[0] == '1' by { assert w[0] in Sigma(M_5_4) && w[0] != '0'; }
				assert w == ['1'] + next_w;
			}
		}
	}

	// Slide 23: exercise

}