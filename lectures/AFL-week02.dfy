include "AFL-week01.dfy"

module Tutorial02 {
	import opened Week01

	// Slide 36: "L = {x | exists y in {a, b}* : x = ya}"
	ghost const L_36: Language := iset x | ValidString(x, Alphabet_a_b) &&
		exists y :: ValidString(y, Alphabet_a_b) && x == Concat(y, "a")

	method M1()
	{
		assert EPSILON !in L_36 by {
			assert !exists y :: ValidString(y, Alphabet_a_b) && EPSILON == Concat(y, "a");
		}
		assert "a" in L_36 by {
			var x, y := "a", EPSILON;
			assert ValidString(x, Alphabet_a_b) &&	ValidString(y, Alphabet_a_b) && x == Concat(y, "a") by {
				calc {
					Concat(y, "a");
				==
					Concat(EPSILON, "a");
				==
					EPSILON + "a";
				==
					"a";
				==
					x;
				}
			}
		}
	}

	// Slide 41: "L = {w in {a, b}*: no prefix of w contains b}"
	ghost const L_41a: Language := iset w | ValidString(w, Alphabet_a_b) &&
		forall y ::
			ValidString(y, Alphabet_a_b) && Prefix(y, w) ==>
			Count('b', y) == 0 // shorter: 'b' !in y

	method M2()
	{
		assert EPSILON in L_41a;
		assert "a" in L_41a by {
			forall y | ValidString(y, Alphabet_a_b) && Prefix(y, "a") ensures Count('b', y) == 0 {
				if y == EPSILON {
					assert Count('b', EPSILON) == 0;
				}
				else {
					assert y == "a";
					assert Count('b', "a") == 0;
				}
			}
		}
	}

	// Exercise: formalize the other languages from slide 41
	// Exercise: prove that L41a is equivalent to the language "a"*
	lemma {:verify false} L_41a_is_a_star()
		ensures L_41a == (iset w | ValidString(w, {'a'}))
	{}
}

module Lecture02 {
	import opened Week01

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

	method M1() {
		ghost var L1 := iset{"cat", "dog"};
		ghost var L2 := iset{"apple", "pear"};
		ghost var L3 := LanguageConcat(L1, L2);
		assert L3 == iset{"catapple", "catpear", "dogapple", "dogpear"} by {
			var s1, s2, t1, t2 := "cat", "dog", "apple", "pear";
			assert L1 == iset{s1, s2};
			assert L2 == iset{t1, t2};
			assert "catapple" == "cat" + "apple" == s1 + t1 && s1 + t1 in L3;
			assert "catpear" == "cat" + "pear" == s1 + t2 && s1 + t2 in L3;
			assert "dogapple" == "dog" + "apple" == s2 + t1 && s2 + t1 in L3;
			assert "dogpear" == "dog" + "pear" == s2 + t2 && s2 + t2 in L3;
		}
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

	method M2() {
		assert SeqConcat(["ab", "cd", "ef"]) == "abcdef";
		assert SeqConcat(["ab", "cd", "ef"]) != "abcdeg";
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
	
	// Slide 74
	/*
	"aabbb" in the language a*b*

	initial state: 1
	input string: "aabbb"
	// after one step
	state: 1
	remaining string: "abbb"
	// after two steps
	state: 1
	remaining string: "bbb"
	// after three steps
	state: 2
	remaining string: "bb"
	// after four steps
	state: 2
	remaining string: "b"
	// after five steps
	state: 2
	remaining string: ""

	The FSM accepts the string "aabbb" because it ended in state 2 which is an accepting state

	"aba" is NOT in the language a*b*

	initial state: 1
	input string: "aba"
	// after one step
	state: 1
	remaining string: "ba"
	// after two steps
	state: 2
	remaining string: "a"
	// after three steps
	state: 3
	remaining string: ""

	Since the FSM ended in state 3 which is NOT accepting, the machine decides that "aba" !in a*b*
	*/
}