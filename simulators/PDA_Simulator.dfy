include "Basic_Definitions.dfy"

module PDA_Simulation {
	import opened FormalLanguages

	type State = nat
	datatype MaybeSymbol = epsilon | sym(Symbol)
	// ((from state, current input string symbol or epsilon, top of the stack string to pop), (to state, string to push onto the stack))
	type PDA_Transition = ((State, MaybeSymbol, String), (State, String))
	type PDA_TransitionRelation = seq<PDA_Transition>
	type PDA = (seq<State>, seq<Symbol>, seq<Symbol>, PDA_TransitionRelation, State, seq<State>)
	type PDA_Configuration = (State, String, String) // state, remaining suffix of input string, contents of the stack

	function PDA_K(M: PDA): seq<State> { M.0 }
	function PDA_Sigma(M: PDA): seq<Symbol> { M.1 }
	function PDA_Gamma(M: PDA): seq<Symbol> { M.2 }
	function PDA_Delta(M: PDA): PDA_TransitionRelation { M.3 }
	function PDA_s(M: PDA): State { M.4 }
	function PDA_A(M: PDA): seq<State> { M.5 }

	// PDA properties:
	ghost predicate ValidPDA(M: PDA) {
		PDA_s(M) in PDA_K(M) && PDA_A(M) <= PDA_K(M) &&
		(forall from_state, pop_str, to_state, push_str :: ((from_state, epsilon, pop_str), (to_state, push_str)) in PDA_Delta(M) ==> 
			from_state in PDA_K(M) && to_state in PDA_K(M) && ValidString(pop_str, set c | c in PDA_Gamma(M)) && ValidString(push_str, set c | c in PDA_Gamma(M))) &&
		(forall from_state, c, pop_str, to_state, push_str :: ((from_state, sym(c), pop_str), (to_state, push_str)) in PDA_Delta(M) ==> 
			from_state in PDA_K(M) && to_state in PDA_K(M) && c in PDA_Sigma(M) && ValidString(pop_str, set c | c in PDA_Gamma(M)) && ValidString(push_str, set c | c in PDA_Gamma(M)))
	}

	ghost predicate Valid_PDA_Configuration(C: PDA_Configuration, M: PDA) {
		ValidPDA(M) && C.0 in PDA_K(M) && ValidString(C.1, set c | c in PDA_Sigma(M)) && ValidString(C.2, set c | c in PDA_Gamma(M))
	}

	predicate Accepting_PDA_Configuration(C: PDA_Configuration, M: PDA)
		requires Valid_PDA_Configuration(C, M)
	{
		C.0 in PDA_A(M) && C.1 == EPSILON && C.2 == EPSILON
	}
  
	// example PDA to accept the (A^n)(B^n) language
	const K_AnBn := [1, 2]
	const Sigma_AnBn := ['a', 'b']
	const Gamma_AnBn := ['a']
	const DELTA_AnBn: PDA_TransitionRelation := 
		[((1, sym('a'), EPSILON), (1, "a")),
		 ((1, sym('b'), "a"), (2, EPSILON)),
		 ((2, sym('b'), "a"), (2, EPSILON))]
	const s_AnBn: State := 1
	const A_AnBn: seq<State> := [1, 2]
	const M_AnBn := (K_AnBn, Sigma_AnBn, Gamma_AnBn, DELTA_AnBn, s_AnBn, A_AnBn)
	const DELTA_AnBn': PDA_TransitionRelation := 
		[((1, sym('a'), EPSILON), (1, "a")),
		 ((1, epsilon, EPSILON), (2, EPSILON)),
		 ((2, sym('b'), "a"), (2, EPSILON))]
	const A_AnBn': seq<State> := [2]
	const M_AnBn' := (K_AnBn, Sigma_AnBn, Gamma_AnBn, DELTA_AnBn', s_AnBn, A_AnBn')

	ghost function L_PDA(M: PDA): Language {
		iset w: String | ValidString(w, set c | c in PDA_Sigma(M)) && AcceptedByPDA(w, M)
	}

	ghost predicate AcceptedByPDA(w: String, M: PDA) {
		ValidString(w,set c | c in  PDA_Sigma(M)) && ValidPDA(M) && AcceptedSuffixByPDA(w, [PDA_s(M)], M)
	}

	ghost predicate AcceptedSuffixByPDA(w: String, states: seq<State>, M: PDA)
		decreases |w|
	{
		true // TODO: define...
	}

	method PrintPDA(M: PDA) {
		print "\n(K = ", PDA_K(M), ", Sigma = ", PDA_Sigma(M), ", Gamma = ", PDA_Gamma(M), ", DELTA = ", PDA_Delta(M), ", s = ", PDA_s(M), ", A = ", PDA_A(M), ")";
	}

	method {:verify false} pdasimulate(M: PDA, w: String) returns (accepted: bool)
		requires ValidPDA(M) && ValidString(w, set c | c in PDA_Sigma(M))
		ensures accepted <==> w in L_PDA(M)
		decreases * // could be non-terminating?
	{
		print "\nRun the PDA ";
		PrintPDA(M);
		print "\non input string \"", w, "\"";
		var initial_configuration := (PDA_s(M), w, EPSILON);
		var previous_configurations := [];
		accepted := pdasimulate_recursive(M, initial_configuration, previous_configurations, 0);
		print "\nThe input string \"", w, "\" is ";
		if !accepted {
			print "NOT ";
		}
		print "in the language accepted by this PDA.\n";
	}

	method Print_PDA_Configuration(C: PDA_Configuration, steps: nat) {
		print "\nConfiguration #", steps, ": <(state=", C.0, ", suffix=\"", C.1, "\", stack=\"", C.2, "\")>"; 
	}

	method {:verify false} pdasimulate_recursive(M: PDA, C: PDA_Configuration, previous_configurations: seq<PDA_Configuration>, steps: nat) returns (accepted: bool)
		requires ValidPDA(M) && Valid_PDA_Configuration(C, M) && forall C' :: C' in previous_configurations ==> Valid_PDA_Configuration(C', M)
		//ensures accepted <==> w in L_PDA(M) TODO: formulate
		decreases * // could be non-terminating?
	{
		Print_PDA_Configuration(C, steps);
		if Accepting_PDA_Configuration(C, M) {
			print "\nThis configuration is accepting!";
			accepted := true;
		}
		else if C in previous_configurations {
			print " This configuration is not new. Backtracking.";
			accepted := false;
		}
		else {
			//print " This is a newly reached configuration. Try to advance.";
			var next_configurations := pdasimulate_one_step(M, C);
			if |next_configurations| == 0 {
				print "\n",
					(if |C.1| == 0 then 
						if C.0 !in PDA_A(M) then "At the end of the input string reached a non-accepting state."
						else "At the end of the input string the stack is not empty."
					else "Stuck with no potential transitions."),
					" Backtracking.";
				accepted := false;
			}
			else if |next_configurations| == 1 {
				accepted := pdasimulate_recursive(M, next_configurations[0], previous_configurations + [C], steps + 1);
			}
			else {
				print "\nFound ", |next_configurations|, " next configurations. Trying each of them in order.";
				var i := 0;
				accepted := false;
				while i != |next_configurations| && !accepted
					invariant 0 <= i <= |next_configurations|
					decreases |next_configurations|-i
				{
					accepted := pdasimulate_recursive(M, next_configurations[i], previous_configurations + [C], steps + 1);
					i := i + 1;
				}
			}
		}
	}

	method {:verify false} pdasimulate_one_step(M: PDA, C: PDA_Configuration) returns (next_configurations: seq<PDA_Configuration>)
		requires ValidPDA(M) && Valid_PDA_Configuration(C, M)
		//ensures accepted <==> w in L_PDA(M) TODO: formulate
		decreases * // could be non-terminating?
	{
		var current_state, suffix, current_stack := C.0, C.1, C.2;
		var all_transitions := PDA_Delta(M);
		next_configurations := [];
		var i := 0;
		while i != |all_transitions|
			invariant 0 <= i <= |all_transitions|
			decreases |all_transitions|-i
		{
			var T := all_transitions[i];
			var from_state, with, pop_str, to_state, push_str := T.0.0, T.0.1, T.0.2, T.1.0, T.1.1;
			if from_state == current_state && (with == epsilon || (suffix != [] && with == sym(suffix[0]))) && pop_str <= current_stack {
				if with == epsilon {
					next_configurations := next_configurations + [(to_state, suffix, push_str + current_stack[|pop_str|..])];
				}
				if suffix != [] && with == sym(suffix[0]) {
					next_configurations := next_configurations + [(to_state, suffix[1..], push_str + current_stack[|pop_str|..])];
				}
			}
			i := i + 1;
		}
	}

	method {:verify false} Main()
		decreases *
	{
		assert ValidPDA(M_AnBn) && ValidString("", set c | c in PDA_Sigma(M_AnBn));
		var accepted := pdasimulate(M_AnBn, "");
		assert accepted;
		assert ValidPDA(M_AnBn) && ValidString("aaab", set c | c in PDA_Sigma(M_AnBn));
		accepted := pdasimulate(M_AnBn, "aaab");
		assert !accepted;
		assert ValidPDA(M_AnBn) && ValidString("aaabbb", set c | c in PDA_Sigma(M_AnBn));
		accepted := pdasimulate(M_AnBn, "aaabbb");
		assert accepted;
		// do the same on a nondeterministic version of a PDA accepting the same language
		assert ValidPDA(M_AnBn') && ValidString("", set c | c in PDA_Sigma(M_AnBn));
		accepted := pdasimulate(M_AnBn', "");
		assert accepted;
		assert ValidPDA(M_AnBn') && ValidString("aaab", set c | c in PDA_Sigma(M_AnBn'));
		accepted := pdasimulate(M_AnBn', "aaab");
		assert !accepted;
		assert ValidPDA(M_AnBn') && ValidString("aaabbb", set c | c in PDA_Sigma(M_AnBn'));
		accepted := pdasimulate(M_AnBn', "aaabbb");
		assert accepted;
	}
}