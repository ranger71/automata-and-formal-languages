include "../lectures/AFL-week04.dfy"

/* Chapter 5: Finite State Machines */
module Assignment1_Chapter5 {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04

	/* Exercise 2a. Build a deterministic FSM for the language L2a:
	
	 {w in {a, b}* : every 'a' in w is immediately preceded and followed by 'b'}

	 */
	ghost const L2a := iset w | ValidString(w, Alphabet_a_b) &&
		forall i :: 0 <= i < |w| && w[i] == 'a' ==> 0 <= i-1 && i+1 < |w| && w[i-1] == 'b' && w[i+1] == 'b'

	// write your solution here or in an attached pdf file (and state here clearly the page number of your answer)
	function f2a(): DFSM

	// a proof is optional [may be awarded by some bonus points]
	lemma {:verify false} LemmaL2a()
		ensures ValidDFSM(f2a()) && L(f2a()) == L2a
	{}

	/* Exercise 2a. Build a deterministic FSM for the language L2i:
	
	 {w in {a, b}* : w has neither "ab" nor "bb" as a substring}

	 */
	ghost const L2i := iset w | ValidString(w, Alphabet_a_b) && !Substring("ab", w) && !Substring("bb", w)

	// write your solution here or in an attached pdf file (and state here clearly the page number of your answer)
	function f2i(): DFSM

	// a proof is optional [may be awarded by some bonus points]
	lemma {:verify false} LemmaL2i()
		ensures ValidDFSM(f2i()) && L(f2i()) == L2i

	// Exercise 5: Consider the following NDFSM M_5 and the language it accepts, L_M5:
	ghost const K_5: set<State> := {0, 1, 2, 3}
	ghost const sigma_5: set<Symbol> := {'a', 'b'}
	ghost const DELTA_5: TransitionRelation :=
		{(0, sym('a'), 0), (0, sym('b'), 1), (0, sym('b'), 2), 
		 (1, sym('a'), 1), (1, sym('b'), 2), (1, sym('a'), 3),
		 (2, sym('b'), 1), (2, sym('a'), 2),
		 (3, sym('b'), 2)}
	ghost const s_5: State := 0
	ghost const A_5: set<State> := {0, 3}
	ghost const M_5: NDFSM := (K_5, sigma_5, DELTA_5, s_5, A_5)
	ghost const L_M5 := L_NDFSM(M_5)

	/* Exercise 5: For each of the following strings determine whether they are in L_M5:

		a) "aabbba"
		b) "bab"
		c) "baba"

		Based on your answer, keep the correct lemma, delete the incorrect one.
		Explain your choice.
		A verified proof may be awarded by some bonus points.
	*/
	lemma {:verify false} Lemma_3a_aabbba_in_L_M5()
		ensures "aabbba" in L_M5

	lemma {:verify false} Lemma_3a_aabbba_NOT_in_L_M5()
		ensures "aabbba" !in L_M5

	lemma {:verify false} Lemma_3b_bab_in_L_M5()
		ensures "bab" in L_M5

	lemma {:verify false} Lemma_3b_bab_NOT_in_L_M5()
		ensures "bab" !in L_M5

	lemma {:verify false} Lemma_3c_baba_in_L_M5()
		ensures "baba" in L_M5

	lemma {:verify false} Lemma_3c_baba_NOT_in_L_M5()
		ensures "baba" !in L_M5

	/* Exercise 9c.
	
		For the following NDFSM, M9c, use ndfsmtodfsm to construct an equivalent DFSM.
		Begin by showing the value of eps(q) for each state q.
		Show in detail the intermediate results of each step of the construction.
	*/
	ghost const q0 := 0
	ghost const q1 := 1
	ghost const q2 := 2
	ghost const q3 := 3
	ghost const q4 := 4
	ghost const q5 := 5
	ghost const K_9c: set<State> := {q0, q1, q2, q3, q4, q5}
	ghost const sigma_9c: set<Symbol> := {'0', '1'}
	ghost const DELTA_9c: TransitionRelation :=
		{(q0, epsilon, q1), (q0, sym('a'), q2), (q0, sym('b'), q3), 
		 (q1, sym('a'), q2), (q1, sym('b'), q3), (q1, sym('a'), q4), 
		 (q2, sym('a'), q2), (q2, sym('b'), q3), (q2, sym('b'), q5), 
		 (q0, epsilon, q0),
		 (q4, sym('a'), q1), (q4, sym('a'), q4), (q4, sym('b'), q5),
		 (q5, sym('a'), q4)}
	ghost const s_9c: State := q0
	ghost const A_9c: set<State> := {q2, q5}
	ghost const M_9c: NDFSM := (K_9c, sigma_9c, DELTA_9c, s_9c, A_9c)
	ghost const L_M9c := L_NDFSM(M_9c)

	// define the output of the ndfsmtodfsm algorithm here
	// or draw it in an attached pdf file (and state here clearly the page number of your solution)
	function f9c(): DFSM

	// no need to prove
	lemma {:verify false} Equivalent_9c_FSMs()
		ensures L_M9c == L(f9c())
	{
		// if you made no mistake and indeed f9c() is the result of the ndfsmtodfsm algorithm on M9c,
		// the languages accepted by the two FSMs are guaranteed to be equal
	}
}
