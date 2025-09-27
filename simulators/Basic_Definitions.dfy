module FormalLanguages { // from lectures 1 and 2
	type Symbol = char
	type String = seq<Symbol>
	type Language = iset<String> // slide 34

	// slide 23
	const EPSILON: String := "" // == []

	// slide 24
	function Length(s: String): nat { |s| }

	function Count(c: Symbol, s: String): nat
		decreases |s|
	{
		if |s| == 0 then
			0
		else if s[0] == c then
			1 + Count(c, s[1..])
		else
			Count(c, s[1..])
	}

	// slide 25
	function Concat(x: String, y: String): String
	{
		x+y
	}

	lemma ConcatenationLength(x: String, y: String)
		ensures |Concat(x, y)| == |x| + |y|
	{}

	lemma EpsilonIsIdentityOfConcatenation(x: String)
		ensures Concat(x, EPSILON) == x == Concat(EPSILON, x)
	{}

	lemma ConcatenationIsAssociative()
		ensures forall s,t,w :: Concat(Concat(s, t), w) == Concat(s, Concat(t, w))
	{}

	// slides 26-27: Replication
	function Rep(w: String, i: nat): String
		decreases i
	{
		if i == 0 then EPSILON else Concat(Rep(w, i-1), w)
	}

	// slides 29-30
	function Reverse(w: String): String
		decreases |w|
	{
		if |w| == 0 then
			EPSILON
		else
			var u: String, a: char := w[..|w|-1], w[|w|-1];
			Concat([a], Reverse(u))
	}

	lemma ConcatenationAndStringReversal(w: String, x: String)
		ensures Reverse(Concat(w, x)) == Concat(Reverse(x), Reverse(w))
		decreases |x| // |Concat(w, x)|
	{
		if |x| == 0
		{
			assert x == EPSILON;
			assert Reverse(Concat(w, EPSILON)) == Reverse(w) by {
				assert Concat(w, EPSILON) == w by { EpsilonIsIdentityOfConcatenation(w); }
			}
			// the above assertion helps in proving the second "==" below:
			assert Reverse(Concat(w, x)) == Reverse(Concat(w, EPSILON)) == Reverse(w) ==
			Concat(EPSILON, Reverse(w)) == Concat(Reverse(EPSILON), Reverse(w)) == Concat(Reverse(x), Reverse(w));
			// but we will write such proofs more cleanly using calculations ("calc", see below in the "else" case...)
		}
		else
		{
			var u: String, a: char := x[..|x|-1], x[|x|-1];
			calc {
				Reverse(Concat(w, x));
			== { assert x == Concat(u, [a]); }
				Reverse(Concat(w, Concat(u, [a])));
			== { ConcatenationIsAssociative(); }
				Reverse(Concat(Concat(w, u), [a]));
			== // definition of Reverse
				Concat([a], Reverse(Concat(w, u)));
			== { ConcatenationAndStringReversal(w, u); } // induction hypothesis
				Concat([a], Concat(Reverse(u), Reverse(w)));
			== { ConcatenationIsAssociative(); }
				Concat(Concat([a], Reverse(u)), Reverse(w));
			== // definition of Reverse
				Concat(Reverse(Concat(u, [a])), Reverse(w));
			== { assert x == Concat(u, [a]); }
				Concat(Reverse(x), Reverse(w));
			}
		}
	}

	// slide 31: relations on strings
	ghost predicate Substring(x: String, w: String) {
		exists u, v :: Concat(u, Concat(x, v)) == w
	}

	ghost predicate ProperSubstring(x: String, w: String) {
		Substring(x, w) && x != w
	}

	lemma EpsilonIsSubstring()
		ensures forall w :: Substring(EPSILON, w)
	{
		forall w ensures Substring(EPSILON, w) {
			var u, v := EPSILON, w;
			assert Concat(u, Concat(EPSILON, v)) == w;
		}
	}

	// slide 32
	ghost predicate Prefix(s: String, t: String) {
		exists x: String :: t == Concat(s, x)
	}

	ghost predicate ProperPrefix(x: String, w: String) {
		Prefix(x, w) && x != w
	}

	// slide 33
	ghost predicate Suffix(s: String, t: String) {
		exists x: String :: t == Concat(x, s)
	}

	ghost predicate ProperSuffix(x: String, w: String) {
		Suffix(x, w) && x != w
	}

	ghost predicate ValidString(w: String, sigma: set<Symbol>) {
		forall c :: c in w ==> c in sigma
	}

	const Alphabet_a_b: set<Symbol> := {'a', 'b'}

	ghost const Alphabet_0_1: set<Symbol> := {'0', '1'}
	
	const EMPTY_LANGUAGE: Language := iset{}

	// Slide 49
	ghost function LanguageUnion(L1: Language, L2: Language): Language {
		L1+L2
	}

	ghost function LanguageIntersection(L1: Language, L2: Language): Language {
		L1*L2
	}

	ghost function LanguageComplement(L1: Language, sigma: set<Symbol>): Language
		requires forall w :: w in L1 ==> ValidString(w, sigma)
	{
		iset w | ValidString(w, sigma) && w !in L1
	}

	lemma LanguageComplementBySetDifference(L1: Language, L_sigma_star: Language, sigma: set<Symbol>)
		requires forall w :: w in L1 ==> ValidString(w, sigma)
		requires L_sigma_star == iset w | ValidString(w, sigma)
		ensures LanguageComplement(L1, sigma) == L_sigma_star - L1
	{}

	// Slide 50
	ghost function LanguageConcat(L1: Language, L2: Language): Language {
		iset s, t | s in L1 && t in L2 :: Concat(s, t)
	}

	// Slide 51
	lemma SingletonEpsilonIsIdentityOfLanguageConcatenation(L: Language)
		ensures LanguageConcat(L, iset{EPSILON}) == L
		ensures LanguageConcat(iset{EPSILON}, L) == L
	{
		assert LanguageConcat(L, iset{EPSILON}) == L by { SingletonEpsilonIsRightIdentityOfLanguageConcatenation(L); }
		assert LanguageConcat(iset{EPSILON}, L) == L by { SingletonEpsilonIsLeftIdentityOfLanguageConcatenation(L); }
	}

	lemma SingletonEpsilonIsRightIdentityOfLanguageConcatenation(L: Language)
		ensures LanguageConcat(L, iset{EPSILON}) == L
	{
		var SingletonEpsilon := iset{EPSILON};
		calc {
			LanguageConcat(L, SingletonEpsilon);
		==
			iset s, t | s in L && t in SingletonEpsilon :: Concat(s, t);
		==
			iset s, t | s in L && t == EPSILON :: Concat(s, t);
		==
			iset s | s in L :: Concat(s, EPSILON);
		== { forall s | s in L ensures Concat(s, EPSILON) == s { EpsilonIsIdentityOfConcatenation(s); }  }
			iset s | s in L :: s;
		==
			L;
		}
	}

	lemma SingletonEpsilonIsLeftIdentityOfLanguageConcatenation(L: Language)
		ensures LanguageConcat(iset{EPSILON}, L) == L
	{
		var SingletonEpsilon := iset{EPSILON};
		calc {
			LanguageConcat(SingletonEpsilon, L);
		==
			iset s, t | s in SingletonEpsilon && t in L :: Concat(s, t);
		==
			iset s, t | s == EPSILON && t in L :: Concat(s, t);
		==
			iset t | t in L :: Concat(EPSILON, t);
		== { forall t | t in L ensures Concat(EPSILON, t) == t { EpsilonIsIdentityOfConcatenation(t); }  }
			iset t | t in L :: t;
		==
			L;
		}
	}

	lemma EmptyLanguageIsZeroOfLanguageConcatenation(L: Language)
		ensures LanguageConcat(L, iset{}) == iset{}
		ensures LanguageConcat(iset{}, L) == iset{}
	{}

	// Slide 53
	ghost function LanguageStar(L: Language): Language {
		iset q: seq<String> | (forall w :: w in q ==> w in L) :: SeqConcat(q)
	}

	ghost function SeqConcat(q: seq<String>): String {
		if |q| == 0 then EPSILON else Concat(q[0], SeqConcat(q[1..]))
	}

	// Slide 54
	ghost function LanguagePlus(L: Language): Language {
		LanguageConcat(L, LanguageStar(L))
	}

	lemma {:verify false} Language_Plus_Star_and_Epsilon(L: Language)
		ensures (LanguagePlus(L) == LanguageStar(L) - iset{EPSILON}) <==> (EPSILON !in L)
	{}
	
	// Slide 55
	ghost function LanguageReverse(L: Language): Language {
		iset w | w in L :: Reverse(w)
	}

	lemma Language_Concatenation_and_Reverse(L1: Language, L2: Language)
		ensures LanguageReverse(LanguageConcat(L1, L2)) == LanguageConcat(LanguageReverse(L2), LanguageReverse(L1))
	{
		calc {
			LanguageReverse(LanguageConcat(L1, L2));
		==
			iset w | w in LanguageConcat(L1, L2) :: Reverse(w);
		==
			iset w | w in (iset w1, w2 | w1 in L1 && w2 in L2 :: Concat(w1, w2)) :: Reverse(w);
		==
			iset w1,w2 | w1 in L1 && w2 in L2 :: Reverse(Concat(w1, w2));
		== { forall w1,w2 | w1 in L1 && w2 in L2 ensures Reverse(Concat(w1, w2)) == Concat(Reverse(w2), Reverse(w1)) 
				{ ConcatenationAndStringReversal(w1, w2); }
		   }
			iset w1,w2 | w1 in L1 && w2 in L2 :: Concat(Reverse(w2), Reverse(w1));
		==
			LanguageConcat(LanguageReverse(L2), LanguageReverse(L1));
		}
	}	
}

module DFSM { // from lecture 3
	import opened FormalLanguages

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

	ghost function L(M: DFSM): Language {
		iset w: String | ValidString(w, Sigma(M)) && AcceptedByDFSM(w, M)
	}

	ghost predicate AcceptedByDFSM(w: String, M: DFSM) {
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

	// Slide 12: regular language definition
	type RegularLanguage = lang: Language | exists M: DFSM :: L(M) == lang witness *
}

module NDFSM { // from lecture 4
	import opened FormalLanguages
	import opened DFSM

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
}
