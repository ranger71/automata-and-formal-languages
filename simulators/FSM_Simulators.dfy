include "Basic_Definitions.dfy"

module FSM_SIMULATION {
	import opened FormalLanguages
	import opened DFSM
	import opened NDFSM

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

	const q0: State := 0
	const q1: State := 1
	const K_5_4 := {q0, q1}
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

	const K_59: set<State> := {0, 1, 2, 3, 4, 5, 6}
	const sigma_59: set<Symbol> := {'a', 'b'}
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

	method Main() {
		// "running" a DFSM:
		var accepted := dfsmsimulate(M_5_4, "1001");
		accepted := dfsmsimulate(M_5_4, "10011");
		// "running" an NDFSM:
		accepted := ndfsmsimulate(M_59, "") by {
			assume {:axiom} ValidNDFSM(M_59);
			assert ValidString("", ND_Sigma(M_59));
		}
		accepted := ndfsmsimulate(M_59, "aba");
		accepted := ndfsmsimulate(M_59, "baa");
		accepted := ndfsmsimulate(M_59, "abba");
	}
}