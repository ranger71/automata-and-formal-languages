include "../lectures/AFL-week02.dfy"

/* Chapter 2: Languages and Strings */
module Assignment1_Chapter2 {
	import opened Week01
	import opened Lecture02

	// Exercise 2: language concatenation, language membership
	ghost const L2a := iset w,n | n > 0 && w == Concat(Rep("a", n), Rep("b", n)) :: w
	ghost const L2b := iset w,n | n > 0 && w == Rep("c", n) :: w
	ghost const L2aL2b := LanguageConcat(L2a, L2b)

	// Goal: define the following 4 functions correctly (returning either "true" or "false" in each) 
	function Q2a(): bool

	function Q2b(): bool

	function Q2c(): bool

	function Q2d(): bool

	// you may want to turn to "{:verify true}" to get a bit of help from the Dafny verifier
	method {:verify false} Q2() {
		var wa, wb, wc, wd := EPSILON, "aabbcc", "abbcc", "aabbcccc";
		// 2a)
		assert wa == EPSILON;
		assert Q2a() == true <==> wa in L2aL2b;

		// 2b)
		assert wb == "aabbcc";
		assert Q2b() == true <==> wb in L2aL2b by {
			var w1, w2 := "aabb", "cc";
			assert w1 in L2a by { assert "aabb" == Concat(Rep("a", 2), Rep("b", 2)); }
			assert w2 in L2b by { assert "cc" == Rep("c", 2); }
			assert wb == Concat(w1, w2);
		}
		// 2c)
		assert wc == "abbcc";
		assume Q2c() == true <==> wc in L2aL2b; // using "assume" instead of "assert since this one is not too trivial to prove
		// 2d)
		assert wd == "aabbcccc";
		assert Q2d() == true <==> wd in L2aL2b by {
			var w1, w2 := "aabb", "cccc";
			assert w1 in L2a by { assert "aabb" == Concat(Rep("a", 2), Rep("b", 2)); }
			assert w2 in L2b by { assert "cccc" == Rep("c", 4); }
			assert wd == Concat(w1, w2);
		}
	}

	// Exercise 6c: language definition and membership
	ghost const L6c := iset w | ValidString(w, Alphabet_a_b) && (exists x :: |x| > 0 && w == Concat("a", Concat(x, "a"))) :: w

	/* Two Goals:

	1) Give a simple English or Hebrew description of the following language.

	2) Show two strings that are in the language and two that are not, by providing a definition to the 4 functions below according to the assertions in the method
	
	*/
	function f6c1(): String

	function f6c2(): String

	function f6c3(): String

	function f6c4(): String

	method {:verify false} Q6() {
		var w1, w2, w3, w4 := f6c1(), f6c2(), f6c3(), f6c4();
		assert ValidString(w1, Alphabet_a_b) && ValidString(w2, Alphabet_a_b) && ValidString(w3, Alphabet_a_b) && ValidString(w4, Alphabet_a_b);
		assert w1 in L6c by { assert w1 == Concat("a", Concat("b", "a")); }
		assert w2 in L6c;
		assert w1 != w2;
		assert w3 !in L6c;
		assert w4 !in L6c;
		assert w3 != w4;
	}

	/* Exercise 8a

	If it is true that for any two languages L1,L2 the languages are equal if and only if L1* is equal to L2* try to prove Lemma8a_True.
	Otherwise, complete the proof of Lemma_8a_False by providing a counter example (specific two different languages L1 and L2 for which L1* == L2*)
	in the body of lemma Lemma_8a_False_Evidence. 

	Recall that L*, the star of a language L, is the language of all strings that can be composed by concatenation of a finite sequence of strings from L.
	*/
	lemma {:verify false} Lemma_8a_True(L1: Language, L2: Language)
		ensures L1 == L2 <==> LanguageStar(L1) == LanguageStar(L2)

	lemma Lemma_8a_False()
		ensures !forall L1, L2 :: L1 == L2 <==> LanguageStar(L1) == LanguageStar(L2)
	{
		assert exists L1, L2 :: L1 != L2 && LanguageStar(L1) == LanguageStar(L2) by {
			var L1, L2 := Lemma_8a_False_Evidence();
			assert L1 != L2 && LanguageStar(L1) == LanguageStar(L2);
		}
	}

	lemma {:verify false} Lemma_8a_False_Evidence() returns (L1: Language, L2: Language)
		ensures L1 != L2 && LanguageStar(L1) == LanguageStar(L2)
}
