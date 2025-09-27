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

	// Slide 16 - a finite state machine that accepts all binary numbers having "odd parity": with an odd number of occurrences of the digit '1'
	ghost const L_16 := iset w | ValidString(w, Alphabet_0_1) && Count('1', w) % 2 == 1
	const q0: State := 5 // the actual number for each state does not really matter, it's just an identifier
	const q1: State := 8
	const K_16 := {5,8}
	const Sigma_16 := {'0', '1'}
	function delta_16(k: State, c: Symbol): State
		requires k in K_16 && c in Sigma_16
	{
		if k == q0 && c == '0' then q0
		else if k == q0 && c == '1' then q1
		else if k == q1 && c == '0' then q1
		else assert k == q1 && c == '1'; q0
	}
	const s_16 := q0
	const A_16 := {q1}
	const M_16 := (K_16, Sigma_16, delta_16, s_16, A_16)
	
	lemma Lemma_16()
		ensures L(M_16) == L_16
	{
		forall w | ValidString(w, Alphabet_0_1) ensures w in L_16 <==> w in L(M_16) {
			if |w| == 0 {
				assert w !in L_16 by { assert Count('1', w) == 0; }
				assert w !in L(M_16) by { assert Yield_Full_From(w, q0, M_16) == q0 && q0 !in A(M_16);}
			}
			else {
				assert |w| > 0;
				var c := w[0];
				var next_w := w[1..];
				assert ValidString(next_w, Sigma(M_16));
				var next_state := Delta(M_16)(q0, c);
				calc {
					w in L(M_16);
				==
					ValidString(w, Sigma(M_16)) && AcceptedByDFSM(w, M_16);
				==
					Yield_Full(w, M_16) in A(M_16);
				==
					Yield_Full_From(w, s(M_16), M_16) in A(M_16);
				==
					Yield_Full_From(w, q0, M_16) in A(M_16);
				== { Lemma_16_q0(w); }
					Count('1', w) % 2 == 1;
				==
					w in L_16;
				}
			}
		}
	}

	lemma Lemma_16_q0(w: String)
		requires ValidString(w, Alphabet_0_1)
		ensures Count('1', w) % 2 == 1 <==> Yield_Full_From(w, q0, M_16) in A(M_16)
		decreases |w|
	{
		if |w| == 0 {
			assert Count('1', w) % 2 == 0;
			assert Yield_Full_From(w, q0, M_16) == q0 && q0 !in A(M_16);
		}
		else {
			assert ValidString(w, Alphabet_0_1);
			assert |w| > 0;
			var c := w[0];
			var next_w := w[1..];
			assert ValidString(next_w, Alphabet_0_1);
			var next_state := Delta(M_16)(q0, c);
			if w[0] == '0' {
				calc {
					Yield_Full_From(w, q0, M_16) in A(M_16);
				==
					Yield_Full_From(next_w, next_state, M_16) in A(M_16);
				== { assert next_state == delta_16(q0, '0') == q0; Lemma_16_q0(next_w); }
					Count('1', next_w) % 2 == 1;
				== { assert w == ['0'] + next_w; }
					Count('1', w) % 2 == 1;
				}
			}
			else {
				calc {
					Yield_Full_From(w, q0, M_16) in A(M_16);
				==
					Yield_Full_From(next_w, next_state, M_16) in A(M_16);
				== { assert next_state == delta_16(q0, '1') == q1; Lemma_16_q1(next_w); }
					Count('1', next_w) % 2 == 0;
				== { assert w == ['1'] + next_w; }
					Count('1', w) % 2 == 1;
				}
			}
		}
	}

	lemma Lemma_16_q1(w: String)
		requires ValidString(w, Alphabet_0_1)
 		ensures Count('1', w) % 2 == 0 <==> Yield_Full_From(w, q1, M_16) in A(M_16)
		decreases |w|
	{
		if |w| == 0 {
			assert Count('1', w) % 2 == 0;
			assert Yield_Full_From(w, q1, M_16) == q1 && q1 in A(M_16);
		}
		else {
			assert ValidString(w, Alphabet_0_1);
			assert |w| > 0;
			var c := w[0];
			var next_w := w[1..];
			assert ValidString(next_w, Alphabet_0_1);
			var next_state := Delta(M_16)(q1, c);
			if w[0] == '0' {
				calc {
					Yield_Full_From(w, q1, M_16) in A(M_16);
				==
					Yield_Full_From(next_w, next_state, M_16) in A(M_16);
				== { assert next_state == delta_16(q1, '0') == q1; Lemma_16_q1(next_w); }
					Count('1', next_w) % 2 == 0;
				== { assert w == ['0'] + next_w; }
					Count('1', w) % 2 == 0;
				}
			}
			else {
				calc {
					Yield_Full_From(w, q1, M_16) in A(M_16);
				==
					Yield_Full_From(next_w, next_state, M_16) in A(M_16);
				== { assert next_state == delta_16(q1, '1') == q0; Lemma_16_q0(next_w); }
					Count('1', next_w) % 2 == 1;
				== { assert w == ['1'] + next_w; }
					Count('1', w) % 2 == 0;
				}
			}
		}
	}

	lemma Lemma_16_with_short_proof()
		ensures L(M_16) == L_16
	{
		forall w | ValidString(w, Alphabet_0_1) ensures w in L_16 <==> w in L(M_16) {
			Lemma_16_q0_with_short_proof(w);
		}
	}

	lemma Lemma_16_q0_with_short_proof(w: String)
		requires ValidString(w, Alphabet_0_1)
		ensures Count('1', w) % 2 == 1 <==> Yield_Full_From(w, q0, M_16) in A(M_16)
		decreases |w|
	{
		if |w| > 0 {
			assert ValidString(w, Alphabet_0_1);
			var c := w[0];
			var next_w := w[1..];
			Lemma_16_q0_with_short_proof(next_w);
			var next_state := Delta(M_16)(q0, c);
			if w[0] == '0' {
				Lemma_16_q0_with_short_proof(next_w);
				assert w == ['0'] + next_w;
			}
			else {
				Lemma_16_q1_with_short_proof(next_w);
				assert w == ['1'] + next_w;
			}
		}
	}

	lemma Lemma_16_q1_with_short_proof(w: String)
		requires ValidString(w, Alphabet_0_1)
 		ensures Count('1', w) % 2 == 0 <==> Yield_Full_From(w, q1, M_16) in A(M_16)
		decreases |w|
	{
		if |w| > 0 {
			var c := w[0];
			var next_w := w[1..];
			if w[0] == '0' {
				Lemma_16_q1_with_short_proof(next_w);
				assert w == ['0'] + next_w;
			}
			else {
				Lemma_16_q0_with_short_proof(next_w);
				assert w[0] == '1' by { assert w[0] in Sigma(M_16) && w[0] != '0'; }
				assert w == ['1'] + next_w;
			}
		}
	}

	// Slide 23: exercise

}