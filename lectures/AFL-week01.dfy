module Week01 {
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

	method M1()
	{
		assert Length(EPSILON) == 0;
		assert Length("1001101") == 7;
		assert Count('a', "abbaaa") == 4;
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

	method M2()
	{
		var x, y := "good", "bye";
		assert x == ['g', 'o', 'o', 'd'] && y == ['b', 'y', 'e']; // in Dafny too, strings are sequences of characters
		assert |x| == 4 && |y| == 3;
		assert Concat(x, y) == x+y == "goodbye" == ['g', 'o', 'o', 'd', 'b', 'y', 'e'];
		assert |Concat(x, y)| == |x| + |y| by { ConcatenationLength(x, y); }
	}

	// slides 26-27: Replication
	function Rep(w: String, i: nat): String
		decreases i
	{
		if i == 0 then EPSILON else Concat(Rep(w, i-1), w)
	}

	method M3()
	{
		assert Rep("a", 3) == "aaa";
		assert Rep("bye", 2) == "byebye";

		assert Concat(Rep("a", 0), Rep("b", 3)) == "bbb";
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

	method M4()
	{
		var x, y := "name", "tag";
		var z := "nametag";
		assert z == Concat(x, y);
		assert Reverse(z) == Concat(Reverse(y), Reverse(x)) by // == "gateman";
		{
			ConcatenationAndStringReversal(x, y);
		}
	}

	// slide 31: relations on strings
	ghost predicate Substring(x: String, w: String)
	{
		exists u, v :: Concat(u, Concat(x, v)) == w
	}

	ghost predicate ProperSubstring(x: String, w: String)
	{
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

	method M5()
	{
		assert Substring("aaa", "aaabbbaaa") by { assert "aaabbbaaa" == Concat(EPSILON, Concat("aaa", "bbbaaa")); }
		assert ProperSubstring("aaa", "aaabbbaaa");
		var z := "nametag";
		assert Substring(EPSILON, z) by { EpsilonIsSubstring(); }
	}

	// slide 32
	ghost predicate Prefix(s: String, t: String)
	{
		exists x: String :: t == Concat(s, x)
	}

	ghost predicate ProperPrefix(x: String, w: String)
	{
		Prefix(x, w) && x != w
	}

	method M6()
	{
		var z := "abba";
		assert Prefix(EPSILON, z) by { assert z == Concat(EPSILON, "abba"); }
		assert Prefix("a", z) by { assert z == Concat("a", "bba"); }
		assert Prefix("ab", z) by { assert z == Concat("ab", "ba"); }
		assert Prefix("abb", z) by { assert z == Concat("abb", "a"); }
		assert Prefix("abba", z) by { assert z == Concat("abba", EPSILON); }

		assert ProperPrefix(EPSILON, z) by { assert Prefix(EPSILON, z) && EPSILON != z; }
		assert ProperPrefix("a", z) by { assert Prefix("a", z) && "a" != z; }
		assert ProperPrefix("ab", z) by { assert Prefix("ab", z) && "ab" != z; }
		assert ProperPrefix("abb", z) by { assert Prefix("abb", z) && "abb" != z; }
		assert !ProperPrefix("abba", z) by { assert "abba" == z; }
	}

	// slide 33
	ghost predicate Suffix(s: String, t: String)
	{
		exists x: String :: t == Concat(x, s)
	}

	ghost predicate ProperSuffix(x: String, w: String)
	{
		Suffix(x, w) && x != w
	}

	ghost predicate ValidString(w: String, sigma: set<Symbol>)
	{
		forall c :: c in w ==> c in sigma
	}

	// slide 35
	const Alphabet_a_b: set<Symbol> := {'a', 'b'}
	ghost const L1: Language := iset x | ValidString(x, Alphabet_a_b) &&
		forall i,j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == 'a' && x[j] == 'b' ==> i < j

	method M7()
	{
		assert EPSILON in L1;
		assert "a" in L1;
		assert "aa" in L1;
		assert "aabbb" in L1;
		assert "bb" in L1;
		assert "aba" !in L1 by { var x := "aba"; var i, j := 2, 1; assert x[i] == 'a' && x[j] == 'b' && !(i < j); }
		assert "ba" !in L1 by { var x := "ba"; var i, j := 1, 0; assert x[i] == 'a' && x[j] == 'b' && !(i < j); }
		assert "abc" !in L1 by { var x := "abc"; assert !ValidString(x, Alphabet_a_b) by { assert x[2] !in Alphabet_a_b; } }
	}

	ghost const Alphabet_0_1: set<Symbol> := {'0', '1'}
	ghost const L2: Language := iset x | ValidString(x, Alphabet_0_1) &&
		Count('1', x) % 2 == 1
	
	method M8()
	{
		assert "10110001111" in L2;
		assert "10110101111" !in L2;
	}
}