include "AFL-week03.dfy"
/*
	Non-Deterministic Finite State Machines (NDFSMs) - based on the second half of Chapter 5

	In the tutorial session we were informally drawing on the white board an NDFSM to accept the language of slide 58;
	see a formal version (along with other machines) in the examples module at the end of this file (below the lecture's module)
*/
module Lecture04 {
	import opened Week01
	import opened Lecture02
	import opened Lecture03

	// NDFSM definitions
	datatype MaybeSymbol = epsilon | sym(Symbol)
	type TransitionRelation = set<(State, MaybeSymbol, State)>
	type NDFSM = (set<State>, set<Symbol>, TransitionRelation, State, set<State>)

	function ND_K(M: NDFSM): set<State> { M.0 }
	function ND_Sigma(M: NDFSM): set<Symbol> { M.1 }
	function ND_Delta(M: NDFSM): TransitionRelation { M.2 }
	function ND_s(M: NDFSM): State { M.3 }
	function ND_A(M: NDFSM): set<State> { M.4 }

	// NDFSM properties:
	ghost predicate ValidNDFSM(M: NDFSM) {
		ND_s(M) in ND_K(M) && ND_A(M) <= ND_K(M) &&
		(forall p, r :: (p, epsilon, r) in ND_Delta(M) ==> {p, r} <= ND_K(M)) &&
		(forall p, c, r :: (p, sym(c), r) in ND_Delta(M) ==> {p, r} <= ND_K(M) && c in ND_Sigma(M))
	}

	ghost function L_NDFSM(M: NDFSM): Language {
		iset w: String | ValidString(w, ND_Sigma(M)) && AcceptedByNDFSM(w, M)
	}

	function eps(q: State, M: NDFSM): set<State>
		requires ValidNDFSM(M) && q in ND_K(M)
		ensures eps(q, M) <= ND_K(M)
	{
		eps_recursive({q}, M)
	}

	function eps_successors(states: set<State>, M: NDFSM): set<State>
		requires ValidNDFSM(M) && states <= ND_K(M)
	{
		set r | r in ND_K(M) && exists p :: p in states && (p, epsilon, r) in ND_Delta(M)
	}

	function eps_recursive(states: set<State>, M: NDFSM): set<State>
		requires ValidNDFSM(M) && states <= ND_K(M)
		ensures eps_recursive(states, M) <= ND_K(M)
		decreases ND_K(M)-states
	{
		var eps_successor_states := eps_successors(states, M);
		if eps_successor_states <= states then
			states
		else
			eps_recursive(states + eps_successor_states, M)
	}

	ghost predicate AcceptedByNDFSM(w: String, M: NDFSM) {
		ValidString(w, ND_Sigma(M)) && ValidNDFSM(M) && AcceptedSuffixByNDFSM(w, eps(ND_s(M), M), M)
	}

	ghost predicate AcceptedSuffixByNDFSM(w: String, states: set<State>, M: NDFSM)
		decreases |w|
	{
		ValidNDFSM(M) && states <= ND_K(M) && ValidString(w, ND_Sigma(M)) &&
		if |w| == 0 then
			states * ND_A(M) != {}
		else
			var c := w[0];
			var next_w := w[1..];
			var next_states := ND_Yield(states, c, M);
			AcceptedSuffixByNDFSM(next_w, next_states, M)
	}

	ghost function ND_Yield(states: set<State>, c: Symbol, M: NDFSM): set<State>
		requires ValidNDFSM(M) && states <= ND_K(M) && c in ND_Sigma(M)
	{
		var successors := set p,q | p in states && q in ND_K(M) && (p, sym(c), q) in ND_Delta(M) :: q;
		set q,r | q in successors && r in ND_K(M) && r in eps(q, M) :: r
	}

	lemma {:verify false} Lemma_EpsilonTransition(w: String, from_state: State, to_state: State, M: NDFSM)
		requires ValidString(w, ND_Sigma(M))
		requires {from_state, to_state} <= ND_K(M) && (from_state, epsilon, to_state) in ND_Delta(M)
		ensures AcceptedSuffixByNDFSM(w, {from_state}, M) <== AcceptedSuffixByNDFSM(w, {to_state}, M)
	{}

	lemma {:verify false} Lemma_OneStep(w: String, from_state: State, to_state: State, M: NDFSM)
		requires ValidString(w, ND_Sigma(M)) && |w| > 0
		requires {from_state, to_state} <= ND_K(M) && (from_state, sym(w[0]), to_state) in ND_Delta(M)
		ensures AcceptedSuffixByNDFSM(w, {from_state}, M) <== AcceptedSuffixByNDFSM(w[1..], {to_state}, M)
	{}

	lemma ND_DeadEnd(states: set<State>, c: Symbol, M: NDFSM)
		requires ValidNDFSM(M) && states <= ND_K(M) && c in ND_Sigma(M)
		requires !exists p,q :: p in states && q in ND_K(M) && (p, sym(c), q) in ND_Delta(M)
		ensures ND_Yield(states, c, M) == {}
	{}

	ghost function NewState(K: set<State>): State
	{
		if |K| == 0 then 0 else	MaxState(K)+1
	}

	ghost function MaxState(K: set<State>): State
		requires |K| > 0
		decreases K
	{
		var s :| s in K;
		if |K| == 1 then s else var m := MaxState(K-{s}); if m > s then m else s
	}

	// rename all states, adding "n" to their number, leaving states 0..n-1 unused
	ghost function RenameAllStates_ND(M: NDFSM, n: nat): NDFSM
		requires ValidNDFSM(M)
	{
		var K := ND_K(M);
		var sigma := ND_Sigma(M);
		var DELTA: TransitionRelation := ND_Delta(M);
		var s := ND_s(M);
		var A := ND_A(M);
		var K': set<State> := set x | x in K :: x+n;
		var sigma' := sigma;
		var DELTA' := (set p, c, q | p in K && c in sigma && q in K && (p, sym(c), q) in DELTA :: (p+n, sym(c), q+n)) +
			(set p, q | p in K && q in K && (p, epsilon, q) in DELTA :: (p+n, epsilon, q+n));
		var s' := s+n;
		var A': set<State> := set x | x in A :: x+n;
		(K', sigma', DELTA', s', A')
	}

	lemma {:verify false} ConsistentStateRenaming_ND(M: NDFSM, M': NDFSM, n: nat)
		requires ValidNDFSM(M) && M' == RenameAllStates_ND(M, n)
		ensures ValidNDFSM(M') && L_NDFSM(M) == L_NDFSM(M')
	{}
}

module Examples04 {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04

	// NDFSM to accept the language in slide 48
	ghost const K_48: set<State> := {0, 1, 2, 3}
	ghost const sigma_48: set<Symbol> := {'a', 'b'}
	ghost const DELTA_48: TransitionRelation := {(0, epsilon, 1), (0, sym('a'), 1), (1, sym('a'), 2), (2, sym('a'), 3), (3, sym('b'), 3)}
	ghost const s_48: State := 0
	ghost const A_48: set<State> := {3}
	ghost const M_48: NDFSM := (K_48, sigma_48, DELTA_48, s_48, A_48)
	ghost const L_M48 := L_NDFSM(M_48)

	method W4a() {
		assert "" !in L_M48;
		ghost var aa := "aa";
		assert aa in L_M48 by {
			calc {
				AcceptedSuffixByNDFSM(aa, {0}, M_48);
			<== { assert (0, epsilon, 1) in DELTA_48; Lemma_EpsilonTransition(aa, 0, 1, M_48); }
				AcceptedSuffixByNDFSM(aa, {1}, M_48);
			<== { assert (1, sym('a'), 2) in DELTA_48; Lemma_OneStep(aa, 1, 2, M_48); }
				AcceptedSuffixByNDFSM(aa[1..], {2}, M_48);
			<== { assert (2, sym('a'), 3) in DELTA_48; Lemma_OneStep(aa[1..], 2, 3, M_48); assert aa[1..] == [aa[1]]+aa[2..]; }
				AcceptedSuffixByNDFSM(aa[2..], {3}, M_48);
			<==
				|aa[2..]| == 0 && 3 in {3} * A_48;
			}
		}
	}

	// NDFSM to accept the language in slide 58
	ghost const K_58: set<State> := {0, 1, 2, 3, 4, 5, 6, 7}
	ghost const sigma_58: set<Symbol> := {'0', '1'}
	// 0: two epsilon transitions, to states 1 and 6 - the initial state of two machines, one accepting positive integers divisible by 16 and one accepting odd positive integers
	// 1: stay in 1 on '0' or '1', move to 2 on '0' (guessing there are three more '0's after that);
	// 2 -> 3 -> 4 ->5 on '0' only;
	// 6: stay in 6 on '0' or '1', move to 7 on '1' (guessing it is the last character in the string (representing the least significant bit)
	ghost const DELTA_58: TransitionRelation := 
		{(0, epsilon, 1), (0, epsilon, 6),
		 (1, sym('0'), 1), (1, sym('1'), 1), (1, sym('0'), 2),
		 (2, sym('0'), 3), 
		 (3, sym('0'), 4),
		 (4, sym('0'), 5), 
		 (6, sym('0'), 6), (6, sym('1'), 6), (6, sym('1'), 7)}
	ghost const s_58: State := 0
	ghost const A_58: set<State> := {5, 7}
	ghost const M_58: NDFSM := (K_58, sigma_58, DELTA_58, s_58, A_58)
	ghost const L_M58 := L_NDFSM(M_58)

	method {:vcs_split_on_every_assert} W4b() {
		assert "" !in L_M58;
		assert "0" !in L_M58;
		ghost var five := "101";
		assert five in L_M58 by {
			calc {
				five in L_M58;
			<==
				AcceptedByNDFSM(five, M_58);
			<==
				AcceptedSuffixByNDFSM(five, eps(0, M_58), M_58);
			<== { assert eps(0, M_58) == {0, 1, 6}; }
				AcceptedSuffixByNDFSM(five, {0, 1, 6}, M_58);
			<==
				AcceptedSuffixByNDFSM(five, {6}, M_58);
			<== { assert (6, sym('1'), 6) in DELTA_58; Lemma_OneStep(five, 6, 6, M_58); assert five == ['1']+five[1..]; }
				AcceptedSuffixByNDFSM(five[1..], {6}, M_58);
			<== { assert (6, sym('0'), 6) in DELTA_58; Lemma_OneStep(five[1..], 6, 6, M_58); assert five[1..] == ['0']+five[2..]; }
				AcceptedSuffixByNDFSM(five[2..], {6}, M_58);
			<== { assert (6, sym('1'), 7) in DELTA_58; Lemma_OneStep(five[2..], 6, 7, M_58); assert five[2..] == ['1']+five[3..]; }
				AcceptedSuffixByNDFSM(five[3..], {7}, M_58);
 			<==
				|five[3..]| == 0 && 7 in {7} * A_58;
			}
		}
	}

	// NDFSM to accept the language L3 in slide 59
	const K_59: set<State> := {0, 1, 2, 3, 4, 5, 6}
	const sigma_59: set<Symbol> := {'a', 'b'}
	// 0: two epsilon transitions, to states 1 and 4 - the initial state of two machines, one accepting strings containing "aa" the other for strings containing "bb" as a substring
	// 1: stay in 1 on 'a' or 'b', move to 2 on 'a' (guessing there is one more 'a' after that);
	// 2 -> 3 on 'a' only;
	// 4: stay in 4 on 'a' or 'b', move to 5 on 'b' (guessing there is one more 'b' after that);
	// 5 -> 6 on 'b' only
	const DELTA_59: TransitionRelation := 
		{(0, epsilon, 1), (0, epsilon, 4),
		 (1, sym('a'), 1), (1, sym('b'), 1), (1, sym('a'), 2), 
		 (2, sym('a'), 3),
		 (3, sym('a'), 3), (3, sym('b'), 3),
		 (4, sym('a'), 4), (4, sym('b'), 4), (4, sym('b'), 5),
		 (5, sym('b'), 6),
		 (6, sym('a'), 6), (6, sym('b'), 6)}
	const s_59: State := 0
	const A_59: set<State> := {3, 6}
	const M_59: NDFSM := (K_59, sigma_59, DELTA_59, s_59, A_59)
	ghost const L_M59 := L_NDFSM(M_59)

	// this one used to verify in an earlier version with the {:vcs_split_on_every_assert} attribute, but now times out
	method {:verify false} W4c() {
		assert "" !in L_M59;
		assert "aba" !in L_M59 by {
			var s_0_1_4 := {0, 1, 4};
			var s_1_2_4 := {1, 2, 4};
			calc {
				"aba" !in L_M59;
			<==
				!AcceptedByNDFSM("aba", M_59);
			<==
				!AcceptedSuffixByNDFSM("aba", eps(0, M_59), M_59);
			<== { assert eps(0, M_59) == s_0_1_4; }
				!AcceptedSuffixByNDFSM("aba", s_0_1_4, M_59);
			<== { assert ND_Yield(s_0_1_4, 'a', M_59) == {1, 2, 4} by {
				var states, c, M := s_0_1_4, 'a', M_59;
				var successors := set p,q | p in states && q in ND_K(M) && (p, sym(c), q) in ND_Delta(M) :: q;
				assert successors == s_1_2_4;
				var res := set q,r | q in successors && r in ND_K(M) && r in eps(q, M) :: r;
				assert res == s_1_2_4 == ND_Yield(states, c, M);
			} }//{(1, sym('a'), 1), (1, sym('a'), 2), (4, sym('a'), 4)} <= DELTA_59; }
				!AcceptedSuffixByNDFSM("ba", {1, 2, 4}, M_59);
			<==
				!AcceptedSuffixByNDFSM("a", {1, 4, 5}, M_59);
			<==
				!AcceptedSuffixByNDFSM("", {1, 2, 4}, M_59);
			<==
				A_59 * {1, 2, 4} == {};
			}
		}
	}

	method W4c'() {
		ghost var baa := "baa";
		assert baa in L_M59 by {
			calc {
				baa in L_M59;
			<==
				AcceptedByNDFSM(baa, M_59);
			<==
				AcceptedSuffixByNDFSM(baa, eps(0, M_59), M_59);
			<== { assert eps(0, M_59) == {0, 1, 4}; }
				AcceptedSuffixByNDFSM(baa, {0, 1, 4}, M_59);
			<==
				AcceptedSuffixByNDFSM(baa, {1}, M_59);
			<== { assert (1, sym('b'), 1) in DELTA_59; Lemma_OneStep(baa, 1, 1, M_59); assert baa == ['b']+baa[1..]; }
				AcceptedSuffixByNDFSM(baa[1..], {1}, M_59);
			<== { assert (1, sym('a'), 2) in DELTA_59; Lemma_OneStep(baa[1..], 1, 2, M_59); assert baa[1..] == ['a']+baa[2..]; }
				AcceptedSuffixByNDFSM(baa[2..], {2}, M_59);
			<== { assert (2, sym('a'), 3) in DELTA_59; Lemma_OneStep(baa[2..], 2, 3, M_59); assert baa[2..] == ['a']+baa[3..]; }
				AcceptedSuffixByNDFSM(baa[3..], {3}, M_59);
 			<==
				|baa[3..]| == 0 && 3 in {3} * A_59;
			}
		}
	}

	method {:isolate_assertions} W4d() {
		ghost var abba := "abba";
		assert abba in L_M59 by {
			calc {
				abba in L_M59;
			<==
				ValidString(abba, ND_Sigma(M_59)) && AcceptedByNDFSM(abba, M_59);
			<==
				AcceptedByNDFSM(abba, M_59);
			<==
				AcceptedSuffixByNDFSM(abba, eps(0, M_59), M_59);
			<== { assert eps(0, M_59) == {0, 1, 4}; }
				AcceptedSuffixByNDFSM(abba, {0, 1, 4}, M_59);
			<==
				AcceptedSuffixByNDFSM(abba, {4}, M_59);
			<== { assert (4, sym('a'), 4) in DELTA_59; Lemma_OneStep(abba, 4, 4, M_59); assert abba == ['a']+abba[1..]; }
				AcceptedSuffixByNDFSM(abba[1..], {4}, M_59);
			<== { assert (4, sym('b'), 5) in DELTA_59; Lemma_OneStep(abba[1..], 4, 5, M_59); assert abba[1..] == ['b']+abba[2..]; }
				AcceptedSuffixByNDFSM(abba[2..], {5}, M_59);
			<== { assert (5, sym('b'), 6) in DELTA_59; Lemma_OneStep(abba[2..], 5, 6, M_59); assert abba[2..] == ['b']+abba[3..]; }
				AcceptedSuffixByNDFSM(abba[3..], {6}, M_59);
			<== { assert (6, sym('a'), 6) in DELTA_59; Lemma_OneStep(abba[3..], 6, 6, M_59); assert abba[3..] == ['a']+abba[4..]; }
				AcceptedSuffixByNDFSM(abba[4..], {6}, M_59);
 			<==
				|abba[4..]| == 0 && 6 in {6} * A_59;
			}
		}
	}
}

module FSM_SIMULATION {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04
	import opened Examples04

	// Slide 81: A Deterministic FSM Interpreter
	method dfsmsimulate(M: DFSM, w: String) returns (accepted: bool)
		requires ValidDFSM(M) && ValidString(w, Sigma(M))
		ensures accepted <==> w in L(M)
	{
		print "Run a DFSM on input string ", w;
		var st := s(M);
		var i := 0;
		var blanks := ""; // just for pretty printing: such that the remaining string's suffix will be displayed clearly
		while i < |w|
			invariant 0 <= i <= |w| && st in K(M)
			invariant ValidDFSM(M) && ValidString(w, Sigma(M))
			invariant Yield_Full_From(w[i..], st, M) in A(M) <==> w in L(M)
			decreases |w|-i
		{
			print "\nConfiguration #", i, ": <", blanks, w[i..], ", ", st, ">";
			var c := w[i];
			assert st in K(M) && c in Sigma(M);
			st := Delta(M)(st, c);
			blanks := blanks + " ";
			i := i+1;
		}
			print "\nConfiguration #", i, ": <", blanks, w[i..], ", ", st, ">";
		accepted := st in A(M);
		print "\nResult: ", if accepted then "Accepted" else "Rejected", "\n";
	}

	// Slide 68: A Non-Deterministic FSM Interpreter
	method ndfsmsimulate(M: NDFSM, w: String) returns (accepted: bool)
		requires ValidNDFSM(M) && ValidString(w, ND_Sigma(M))
		ensures accepted <==> w in L_NDFSM(M)
	{
		print "Run an NDFSM on input string ", w;
		var current_state := eps(ND_s(M), M);
		var i := 0;
		var blanks := ""; // just for pretty printing: such that the remaining string's suffix will be displayed clearly
		while i < |w| && current_state != {} 
			invariant 0 <= i <= |w| && current_state <= ND_K(M)
			invariant ValidNDFSM(M) && ValidString(w, ND_Sigma(M)) && ValidString(w[i..], ND_Sigma(M))
			invariant AcceptedSuffixByNDFSM(w[i..], current_state, M) <==> AcceptedByNDFSM(w, M)
			decreases |w|-i
		{
			print "\n<", blanks, w[i..], ", ", current_state, ">";
			var c := w[i];
			var next_state := set q, r, r' | r in ND_K(M) && q in current_state && (q, sym(c), r) in ND_Delta(M) && r' in eps(r, M) :: r';
			assert next_state == ND_Yield(current_state, c, M);
			assert next_state <= ND_K(M);
			current_state := next_state;
			blanks := blanks + " ";
			i := i+1;
		}
		print "\n<", blanks, w[i..], ", ", current_state, ">";
		if current_state == {} {
			assert !AcceptedByNDFSM(w, M) by { Lemma_Stuck_NDFSM(w[i..], M); }
		} else {
			calc {
				(current_state * ND_A(M) != {});
			==
				AcceptedSuffixByNDFSM(w[i..], current_state, M);
			== { assert i == |w| && w[i..] == []; }
				AcceptedSuffixByNDFSM([], current_state, M);
			==
				AcceptedByNDFSM(w, M);
			==
				w in L_NDFSM(M);
			}
		}
		accepted := current_state * ND_A(M) != {};
		print "\nResult: ", if accepted then "Accepted" else "Rejected", "\n";
	}

	lemma Lemma_Stuck_NDFSM(w: String, M: NDFSM)
		requires ValidNDFSM(M) && ValidString(w, ND_Sigma(M))
		ensures !AcceptedSuffixByNDFSM(w, {}, M)
	{
		if |w| == 0 {
			assert {} * ND_A(M) == {};
		} else {
			assert ND_Yield({}, w[0], M) == {};
		}
	}

	method Main() {
		var accepted := dfsmsimulate(M_16, "1001");
		accepted := dfsmsimulate(M_16, "10011");
		accepted := ndfsmsimulate(M_59, "");
		accepted := ndfsmsimulate(M_59, "aba");
		accepted := ndfsmsimulate(M_59, "baa");
		accepted := ndfsmsimulate(M_59, "abba");
	}
}