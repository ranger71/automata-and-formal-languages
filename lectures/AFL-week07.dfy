include "AFL-week05.dfy"

// regular and nonregular languages (Chapter 8)
module Lecture07  {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04
	import opened Lecture05
	
	ghost predicate IsRegular(L1: Language) { exists M: DFSM :: ValidDFSM(M) && L(M) == L1 }

	method M1() {
		// slide 45
		ghost var Laibi: Language := LanguageAiBi();
		assert !IsRegular(Laibi) by {
			if IsRegular(Laibi)
			{
				PumpingLemma(Laibi);
				assert exists k :: k >= 1 && Pumping_K(Laibi, k);
				var k :| k >= 1 && Pumping_K(Laibi, k);
				assert forall w :: w in Laibi && |w| >= k ==> Pumping_K_w(Laibi, k, w);
				var w := Concat(Rep("a", k), Rep("b", k));
				assume w in Laibi && |w| == k+k >= k;
				assert false by { LaibiRegularityContradiction(k, w); }
			}
		}
	}

	// for slide 45
	ghost function LanguageAiBi(): Language
	{
		iset i | 0 <= i :: Concat(Rep("a", i), Rep("b", i))
	}

	lemma {:verify false} EqualAsAndBsInLanguageAiBi()
		ensures forall w :: w in LanguageAiBi() ==> Count('a', w) == Count('b', w)
	{}

	lemma {:verify false} LaibiRegularityContradiction(k: nat, w: String)
		requires k >= 1 && Pumping_K(LanguageAiBi(), k) && w == Concat(Rep(['a'], k), Rep(['b'], k))
		ensures false
	{
		// by showing "!Pumping_K_w(LanguageAiBi(), k, w)" we'll get a contradiction with the available "Pumping_K(LanguageAiBi(), k)"
		var Laibi := LanguageAiBi();
		assert !Pumping_K_w(Laibi, k, w) by {
	//		forall x, y, z | w == Concat(Concat(x, y), z) && |Concat(x, y)| <= k && y != EPSILON
			forall x: String, y: String, z: String | ((x+y)+z==w) && |x+y| <= k && y != EPSILON // inlined "Concat" just to avoid a triggers-related warning
				ensures exists q :: 0 <= q && Concat(Concat(x, Rep(y, q)), z) !in Laibi {
				var q := 2; // the string xyyz is NOT in Laibi
				var w' := Concat(Concat(x, Rep(y, q)), z);
				// recall that w is (a^k)(b^k) (== xyz)
				// therefore w' is (a^(k+p)(b^k) for some p > 0
				// and this w' is NOT in Laibi since it has more a's than b's
				assert exists p :: p > 0 && y == Rep(['a'], p) by { LemmaOnlyAs(x, y, z, w, k); }
				assert Count('a', w') > Count('b', w') by { LemmaMoreAs(x, y, z, w, w', k); }
				assert w' !in Laibi by { EqualAsAndBsInLanguageAiBi(); }
				// example with k=3 and p=1, such that w == aaabbb; x == aa, y == a, z == bbb; w' == xyyz == aaaabbb;
				// with more a's than b's it is not in (a^i)(b^i)
			}
		}
		assert false by {
			assert !Pumping_K_w(Laibi, k, w); // as proved above
			assert Pumping_K(LanguageAiBi(), k); // from the precondition
		}
	}

	// y lies in the first half of w (== (a^k)(b^k) == xyz) and it is not empty
	lemma {:verify false} LemmaOnlyAs(x: String, y: String, z: String, w: String, k: nat)
		requires k >= 1 && Pumping_K(LanguageAiBi(), k) && w == Concat(Rep(['a'], k), Rep(['b'], k))
		requires w == Concat(Concat(x, y), z) && |Concat(x, y)| <= k && y != EPSILON
		ensures exists p :: p > 0 && y == Rep(['a'], p)
	{}

	// w' is actually (a^k+|y|)(b^k), with y being a non-empty sequence of a's that was pumped in once
	lemma {:verify false} LemmaMoreAs(x: String, y: String, z: String, w: String, w': String, k: nat)
		requires k >= 1 && Pumping_K(LanguageAiBi(), k) && w == Concat(Rep(['a'], k), Rep(['b'], k))
		requires w == Concat(Concat(x, y), z) && |Concat(x, y)| <= k && y != EPSILON
		requires w' == Concat(Concat(x, Rep(y, 2)), z)
		ensures Count('a', w') > Count('b', w')
	{}

	// slide 13
	lemma {:verify false} RegularLanguagesAreClosedUnderUnion(L1: Language, L2: Language)
		requires IsRegular(L1) && IsRegular(L2)
		ensures IsRegular(LanguageUnion(L1, L2))
	{/* incomplete draft proof, based on the regextofsm construction
		var M1 :| ValidDFSM(M1) && L(M1) == L1;
		var M2 :| ValidDFSM(M2) && L(M2) == L2;
		var M2' := RenameAllStates_ND(M2, NewState(ND_K(M1)));
		var K := ND_K(M1) + ND_K(M2');
		var s := NewState(K);
		K := K + {s};
		var unionTransitions := {(s, epsilon, ND_s(M1)), (s, epsilon, ND_s(M2'))};
		var DELTA := ND_Delta(M1)+ND_Delta(M2')+unionTransitions;
		var M := (K, sigma, DELTA, s, ND_A(M1)+ND_A(M2'));
		assert IsRegular(LanguageUnion(L1, L2)) by {
			assume IsRegular(L_NDFSM(M));
			assume L_NDFSM(M) == LanguageUnion(L1, L2);
		}
	*/}

	// slide 38
	lemma {:verify false} LongStrings(M: DFSM, w: String) returns (i: nat, j: nat)
		requires ValidDFSM(M) && ValidString(w, Sigma(M)) && w in L(M) && |w| >= |K(M)|
		ensures i < j <= |K(M)| && Yield_Full(w[..i], M) == Yield_Full(w[..j], M)
	// Challenge: prove, using the pigeonhole principle
	{}

	// slide 41
	lemma PumpingLemma(L1: Language)
		ensures IsRegular(L1) ==> exists k :: k >= 1 && Pumping_K(L1, k)
	{
		if IsRegular(L1)
		{
			var M :| ValidDFSM(M) && L(M) == L1;
			var k := |K(M)|;
			assert k >= 1 by { assert s(M) in K(M); }
			assert Pumping_K(L1, k) by {
				forall w | w in L1 && |w| >= k ensures Pumping_K_w(L1, k, w) {
					var i, j := LongStrings(M, w);
					var x, y, z := w[..i], w[i..j], w[j..];

					assert Pumping_K_w_x_y_z(L1, k, w, x, y, z) by {
						assert |Concat(x, y)| == |w[..i]+w[i..j]| == |w[..j]| == j <= |K(M)| == k;
						assert y != EPSILON by { assert y == w[i..j] && i < j; }
						forall q | 0 <= q ensures Concat(Concat(x, Rep(y, q)), z) in L1 {
							assert Concat(Concat(x, y), z) == w;
							PumpInAndOut(L1, M, x, y, z, q); // x(y^q)z is also in L1
						}
					}
				}
			}
		}
	}

	lemma PumpingLemma'(L1: Language)
		requires forall k :: k >= 1 ==> !Pumping_K(L1, k)
		ensures !IsRegular(L1)
	{
		assert !exists k :: k >= 1 && Pumping_K(L1, k);
		PumpingLemma(L1);
	}

	lemma PumpInAndOut(L1: Language, M: DFSM, x: String, y: String, z: String, q: nat)
		requires ValidDFSM(M) && ValidString(x, Sigma(M)) && ValidString(y, Sigma(M)) && ValidString(z, Sigma(M))
		requires Concat(Concat(x, y), z) in L1 && L(M) == L1 && Yield_Full(x, M) == Yield_Full(Concat(x, y), M)
		ensures Concat(Concat(x, Rep(y, q)), z) in L1
	{
		if q == 0
		{
			// should prove (xz) is in L1 too
			assert Concat(Concat(x, Rep(y, 1)), z) == Concat(Concat(x, y), z);
			PumpOut(L1, M, x, y, z, 1);
		}
		else if q == 1
		{
			assert Rep(y, q) == y;
		}
		else
		{
			PumpInAndOut(L1, M, x, y, z, q-1);
			assert Concat(Concat(x, Rep(y, q-1)), z) in L1;
			PumpIn(L1, M, x, y, z, q);
		}
	}

	lemma {:verify false} PumpOut(L1: Language, M: DFSM, x: String, y: String, z: String, q: nat)
		requires ValidDFSM(M) && ValidString(x, Sigma(M)) && ValidString(y, Sigma(M)) && ValidString(z, Sigma(M))
		requires q > 0 && Concat(Concat(x, Rep(y, q)), z) in L1 && L(M) == L1 && Yield_Full(x, M) == Yield_Full(Concat(x, y), M)
		ensures Concat(Concat(x, Rep(y, q-1)), z) in L1
	{}

	lemma {:verify false} PumpIn(L1: Language, M: DFSM, x: String, y: String, z: String, q: nat)
		requires ValidDFSM(M) && ValidString(x, Sigma(M)) && ValidString(y, Sigma(M)) && ValidString(z, Sigma(M))
		requires q > 0 && Concat(Concat(x, Rep(y, q-1)), z) in L1 && L(M) == L1 && Yield_Full(x, M) == Yield_Full(Concat(x, y), M)
		ensures Concat(Concat(x, Rep(y, q)), z) in L1
	{}

	ghost predicate Pumping_K(L1: Language, k: nat)
		requires k >= 1
	{
		forall w :: w in L1 && |w| >= k ==> Pumping_K_w(L1, k, w)
	}

	ghost predicate Pumping_K_w(L1: Language, k: nat, w: String)
		requires k >= 1 && w in L1 && |w| >= k
	{
		exists x, y, z :: w == Concat(Concat(x, y), z) && Pumping_K_w_x_y_z(L1, k, w, x, y, z)
	}

	ghost predicate Pumping_K_w_x_y_z(L1: Language, k: nat, w: String, x: String, y: String, z: String)
		requires k >= 1 && w in L1 && |w| >= k && w == Concat(Concat(x, y), z)
	{
		|Concat(x, y)| <= k &&
		y != EPSILON &&
		forall q :: 0 <= q ==> Concat(Concat(x, Rep(y, q)), z) in L1
	}

	function Yield_Full(w: String, M: DFSM): (res: State)
		requires ValidDFSM(M) && ValidString(w, Sigma(M))
		ensures res in K(M)
	{
		Yield_Full_From(w, s(M), M)
	}

	function Yield_Full_From(w: String, state: State, M: DFSM): (res: State)
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
}
