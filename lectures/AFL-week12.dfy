include "../simulators/FSM_Simulators.dfy"

module Tutorial12 {
	/*

	Exam A 2022

	3) some potential solutions:

	b* union b*(ab+)*(a union epsilon)
	(b*ab)*b*(a union epsilon)
	(b*(ab)*)*(a union epsilon)
	b*(abb*)*(a union epsilon)

	*/
}

module Lecture12 {
	/*

	12:27 slide 21

	111
	#11 
	#11#
	#11##
	#11##
	##1##
	##1###
	##1####
	#######
	########
	#########
	########1
	#######11
	######111
	#####1111
	####11111
	###111111
	##1111111
	#11111111
	111111111

	final state: h


	12:53 Slide 22

	ba abba
	ba  bba  // x is 'a'
	baa bba
	baa  ba // x is 'b'
	baab ba
	baab  a // x is 'b'
	baabb a
	baabb   // x is 'a'
	baabba _
	baabba_


	baabba

	Slide 28:

	- a TM to semidecide b*a(a union b)*

	{((0, _) -> (1, _, ->)),
	((1, b) -> (1, b, ->)),
	((1, a) -> (y, a, ->))}

	- a TM to decide b*a(a union b)*

	{((0, _) -> (1, _, ->)),
	((1, b) -> (1, b, ->)),
	((1, a) -> (y, a, ->)),
	((1, _) -> (n, _, ->))}


	13:45 Q4 in the 2022 Moed A exam:

	(1^n 0^m 1 0^m 1^n for any m, n >= 0)

	1
	010   [S => T => X => 0 X 0 => 0 1 0]
	111
	00100 [S => T => X => 0 X 0 => 0 0 X 0 0 => 0 0 1 0 0]

	00000 [the middle symbol must be 1]
	00110 [the second 0 is not matched with the second from last symbol, 1: this is a language of palindromes]
	111111 [the length of any string in this language is odd]

	S => 1 S 1 => 1 T 1 => 1 X 1 => 1 1 1
	S => T => 1 X 1 => 1 1 1

	*/
}

module Turing_Machine_Simulation {
	import opened FormalLanguages

	type State = nat
	datatype Direction = Left | Right
	type TM_TransitionFunction = (State, Symbol) --> (State, Symbol, Direction)
	type TuringMachine = (set<State>, set<Symbol>, set<Symbol>, TM_TransitionFunction, State, set<State>)
	type TM_Configuration = (State, seq<Symbol>, Symbol, seq<Symbol>)

	const BLANK_SQUARE: Symbol := ' '

	function TM_K(M: TuringMachine): set<State> { M.0 }
	function TM_Sigma(M: TuringMachine): set<Symbol> { M.1 }
	function TM_Gamma(M: TuringMachine): set<Symbol> { M.2 }
	function TM_Delta(M: TuringMachine): TM_TransitionFunction { M.3 }
	function TM_s(M: TuringMachine): State { M.4 }
	function TM_H(M: TuringMachine): set<State> { M.5 }

	// TM properties:
	ghost predicate ValidTM(M: TuringMachine) {
	TM_s(M) in TM_K(M) && TM_H(M) <= TM_K(M) &&
	TM_Sigma(M) <= TM_Gamma(M) && BLANK_SQUARE in TM_Gamma(M)-TM_Sigma(M) && 
	forall k, c :: k in TM_K(M)-TM_H(M) && c in TM_Gamma(M) ==>
		TM_Delta(M).requires(k, c) &&
		TM_Delta(M)(k, c).0 in TM_K(M) &&
		TM_Delta(M)(k, c).1 in TM_Gamma(M)
	}

	predicate NoLeadingBlanks(str: String) {
		|str| == 0 || str[0] != BLANK_SQUARE
	}

	predicate NoTrailingBlanks(str: String) {
		|str| == 0 || str[|str|-1] != BLANK_SQUARE
	}

	ghost predicate Valid_TM_Configuration(C: TM_Configuration, M: TuringMachine) {
		ValidTM(M) &&
		C.0 in TM_K(M) &&
		(forall c :: c in C.1 + [C.2] + C.3 ==> c in TM_Gamma(M)) &&
		NoLeadingBlanks(C.1) &&
		NoTrailingBlanks(C.3)
	}

	predicate Halting_TM_Configuration(C: TM_Configuration, M: TuringMachine)
		requires Valid_TM_Configuration(C, M)
	{
		C.0 in TM_H(M)
	}
  
	// example TM from slide 9:
	const K_9 := {1, 2, 3, 4, 5, 6, 7} // adding 7 as a dummy halting state: it should never be reached when running on valid input
	const Sigma_9 := {'a', 'b'}
	const Gamma_9 := Sigma_9 + {BLANK_SQUARE, '$', '#'}
	function delta_9(k: State, c: Symbol): (State, Symbol, Direction)
	requires k in K_9-H_9 && c in Gamma_9
	{
	if k == 1 then
		if c == BLANK_SQUARE then (2, c, Right) else (7, c, Right)
	else if k == 2 then
		if c == 'a' then (3, '$', Right) else if c == BLANK_SQUARE then (6, c, Left) else (7, c, Right)
	else if k == 3 then
		if c == 'a' || c == '$' || c == '#' then (3, c, Right) else if c == 'b' || c == BLANK_SQUARE then (4, '#', Left) else (7, c, Right)
	else if k == 4 then
		if c == 'a' then (3, '$', Right) else if c == '$' || c == '#' then (4, c, Left) else if c == BLANK_SQUARE then (5, c, Right) else (7, c, Right)
	else
		assert k == 5;
		if c == '$' then (5, 'a', Right) else if c == '#' then (5, 'b', Right) else if c == BLANK_SQUARE then (6, c, Left) else (7, c, Right)
	}
	const s_9 := 1
	const H_9 := {6, 7}
	const M_9 := (K_9, Sigma_9, Gamma_9, delta_9, s_9, H_9)

	method {:verify false} tmsimulate(M: TuringMachine, w: String) returns (output: TM_Configuration, steps: nat)
		requires ValidTM(M) && ValidString(w, TM_Sigma(M))
		ensures Halting_TM_Configuration(output, M)
		decreases * // could be non-terminating
	{
		print "Run a TM on input string ", w;
		steps := 0;
		var st := TM_s(M);
		var tape_left, c, tape_right := "", BLANK_SQUARE, w;
		var blanks := "";
		while !Halting_TM_Configuration((st, tape_left, c, tape_right), M)
			invariant Valid_TM_Configuration((st, tape_left, c, tape_right), M)
			decreases *
		{
			print "\n ", tape_left + [c] + tape_right, "\t\tConfiguration #", steps, ": <", (st, tape_left, c, tape_right), ">";
			assert st in TM_K(M) && c in TM_Gamma(M);
			var action := TM_Delta(M)(st, c);
			st := action.0;
			var tape := tape_left + [action.1] + tape_right;
			var c_index := if action.2 == Left then |tape_left| - 1 else |tape_left| + 1;
			if c_index < 0 {
				tape_left, c, tape_right := "", BLANK_SQUARE, tape;
			}
			else if c_index >= |tape| {
				tape_left, c, tape_right := tape, BLANK_SQUARE, "";
			}
			else {
				tape_left, c, tape_right := tape[..c_index], tape[c_index], tape[c_index+1..];
			}
			if |tape_left| == 1 && tape_left  == [BLANK_SQUARE] {
				tape_left := [];
			}
			if |tape_right| == 1 && tape_right  == [BLANK_SQUARE] {
				tape_right := [];
			}
			steps := steps + 1;
		}
		output := (st, tape_left, c, tape_right);
		print "\n ", output.1 + [output.2] + output.3, "\t\tConfiguration #", steps, ": <", output, ">";
		print "\nTM halts after ", steps, " steps.";
		assert Valid_TM_Configuration(output, M);
		assert Halting_TM_Configuration(output, M);
	}

	method Main()
		decreases *
	{
		assert ValidTM(M_9) && ValidString("aaab", TM_Sigma(M_9));
		var output, steps := tmsimulate(M_9, "aaab");
		assert output.0 in TM_H(M_9); //Valid_TM_Configuration(output, M_9);
	}
}