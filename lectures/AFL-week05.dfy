include "AFL-week04.dfy"
/*
	Chapter 6: Regular Expressions

	In the tutorial session we demonstrated the ndfsmtodfsm algorithm from slide 72 of Chapter 5 on Exercise 9a from the book,
	turning the 6-states NDFSM into an equivalent DFSM with 4 states, one that simulates a parallel run on the original NDFSM
*/
module Tutorial05 {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04

	// Exercise 9a
	ghost const q0 := 0
	ghost const q1 := 1
	ghost const q2 := 2
	ghost const q3 := 3
	ghost const q4 := 4
	ghost const q5 := 5
	ghost const K_9a: set<State> := {q0, q1, q2, q3, q4, q5}
	ghost const sigma_9a: set<Symbol> := {'0', '1'}
	ghost const DELTA_9a: TransitionRelation :=
		{(q0, sym('1'), q0), (q0, epsilon, q1), (q0, sym('1'), q3), 
		 (q1, sym('0'), q2), (q1, epsilon, q3), 
		 (q2, sym('1'), q5), 
		 (q3, sym('0'), q4), 
		 (q4, sym('1'), q1), (q4, epsilon, q2), (q4, epsilon, q5),
		 (q5, sym('0'), q4)}
	ghost const s_9a: State := q0
	ghost const A_9a: set<State> := {q4, q5}
	ghost const M_9a: NDFSM := (K_9a, sigma_9a, DELTA_9a, s_9a, A_9a)
	ghost const L_M9a := L_NDFSM(M_9a)
	// the output of the ndfsmtofsm algorithm on the NDFSM M_9a is a DFSM as follows:
	ghost const q_0_1_3 := 0
	ghost const q_2_4_5 := 1
	ghost const q_5_1_3 := 2
	ghost const q_emptyset := 3
	ghost const K_9a': set<State> := {q_0_1_3, q_2_4_5, q_5_1_3, q_emptyset}
	ghost const sigma_9a': set<Symbol> := {'0', '1'}
	ghost function delta_9a'(q: State, c: Symbol): State
		requires q in K_9a' && c in sigma_9a'
	{
		if q == q_0_1_3 && c == '0' then q_2_4_5
		else if q == q_0_1_3 && c == '1' then q_0_1_3
		else if q == q_2_4_5 && c == '0' then q_2_4_5
		else if q == q_2_4_5 && c == '1' then q_5_1_3
		else if q == q_5_1_3 && c == '0' then q_2_4_5
		else if q == q_5_1_3 && c == '1' then q_emptyset
		else assert q == q_emptyset; q_emptyset // a "dead" state (we stay there on any input character/symbol: both on '0' and on '1')
	}
	ghost const s_9a': State := q_0_1_3
	ghost const A_9a': set<State> := {q_2_4_5, q_5_1_3}
	ghost const M_9a': DFSM := (K_9a', sigma_9a', delta_9a', s_9a', A_9a')
	ghost const L_M9a' := L(M_9a')

	lemma {:verify false} Equivalent_9a_FSMs()
		ensures L_M9a == L_M9a'
	{
		// if we made no mistake and indeed M9a' is the result of the ndfsmtodfsm algorithm on M9a,
		// the languages accepted by the two FSMs are guaranteed to be equal
	}
}

module Lecture05 {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04

	// regular expressions (Chapter 6)
	datatype RegularExpression = EmptyExp | EpsilonExp | SymbolExp(Symbol) | ConcatExp(RegularExpression, RegularExpression) |
		UnionExp(RegularExpression, RegularExpression) | StarExp(RegularExpression) | PlusExp(RegularExpression) | Parentheses(RegularExpression)

	// slide 5
	ghost function L_Regex(regex: RegularExpression, sigma: set<Symbol>): Language
		requires ValidRegularExpression(regex, sigma)
		decreases RegexVariant(regex), regex
	{
		match regex
		case EmptyExp => EMPTY_LANGUAGE
		case EpsilonExp => iset{EPSILON}
		case SymbolExp(symbol) => iset{[symbol]}
		case ConcatExp(left, right) => LanguageConcat(L_Regex(left, sigma), L_Regex(right, sigma))
		case UnionExp(left, right) => LanguageUnion(L_Regex(left, sigma), L_Regex(right, sigma))
		case StarExp(alpha) => LanguageStar(L_Regex(alpha, sigma))
		case PlusExp(alpha) =>
			var alpha_alphastar := ConcatExp(alpha, StarExp(alpha));
			assert RegexVariant(regex) == 2*RegexVariant(alpha)+1 > RegexVariant(alpha)+RegexVariant(alpha) == RegexVariant(alpha_alphastar);
			L_Regex(alpha_alphastar, sigma)
		case Parentheses(alpha) => L_Regex(alpha, sigma)
	}

	// to be sure the definition of L_Regex is well formed (not infinitely circular)
	ghost function RegexVariant(regex: RegularExpression): nat
	{
		match regex
		case EmptyExp => 0
		case EpsilonExp => 0
		case SymbolExp(symbol) => 0
		case ConcatExp(left, right) => RegexVariant(left)+RegexVariant(right)
		case UnionExp(left, right) => RegexVariant(left)+RegexVariant(right)
		case StarExp(regex1) => RegexVariant(regex1)
		case PlusExp(regex1) => 2*RegexVariant(regex1)+1
		case Parentheses(regex1) => RegexVariant(regex1)
	}

	// a valid regexp for a given alphabet contains only symbols from this alphabet (the sigma parameter)
	ghost predicate ValidRegularExpression(regex: RegularExpression, sigma: set<Symbol>)
		decreases regex
	{
		match regex
		case EmptyExp => true
		case EpsilonExp => true
		case SymbolExp(symbol) => symbol in sigma
		case ConcatExp(left, right) => ValidRegularExpression(left, sigma) && ValidRegularExpression(right, sigma)
		case UnionExp(left, right) => ValidRegularExpression(left, sigma) && ValidRegularExpression(right, sigma)
		case StarExp(regex) => ValidRegularExpression(regex, sigma)
		case PlusExp(regex) => ValidRegularExpression(regex, sigma)
		case Parentheses(regex) => ValidRegularExpression(regex, sigma)
	}

	method W5a()
	{
		// examples from slide 4
		var regex, regex1, regex2, regex3, regex4; 
		var sigma := {'a', 'b'};
		regex := EmptyExp;                      // iset{}
		regex1 := SymbolExp('a');               // iset{"a"}
		regex2 := SymbolExp('b');               // iset{"b"}
		regex3 := UnionExp(regex1, regex2);     // iset{"a", "b"}
		regex4 := StarExp(regex3);              // iset w | ValidString(w, sigma}

		// slide 9
		regex := ConcatExp(regex4, regex2); // ('a' or 'b')*'b'
		var lang_a := iset{['a']};
		var lang_b := iset{['b']};
		var lang_a_b := iset{['a'], ['b']};
		calc {
			L_Regex(regex, sigma);
		== // definition of regex
			L_Regex(ConcatExp(regex4, regex2), sigma);
		== // language of concatenation
			LanguageConcat(L_Regex(regex4, sigma), L_Regex(regex2, sigma));
		== // language of symbol
			LanguageConcat(L_Regex(regex4, sigma), lang_b);
		== // definition of regexp4
			LanguageConcat(L_Regex(StarExp(regex3), sigma), lang_b);
		== // language of kleene star
			LanguageConcat(LanguageStar(L_Regex(regex3, sigma)), lang_b);
		== // definition of regexp3
			LanguageConcat(LanguageStar(L_Regex(UnionExp(regex1, regex2), sigma)), lang_b);
		== // language of union
			LanguageConcat(LanguageStar(LanguageUnion(L_Regex(regex1, sigma), L_Regex(regex2, sigma))), lang_b);
		== // languages of symbols
			LanguageConcat(LanguageStar(LanguageUnion(lang_a, lang_b)), lang_b);
		== // union of languages (isets)
			LanguageConcat(LanguageStar(lang_a_b), lang_b);
		}
		// slide 15, 3rd example - no more than one b: "a* or a*ba*"
		regex := UnionExp(StarExp(regex1), ConcatExp(StarExp(regex1), ConcatExp(regex2, StarExp(regex1))));
		// slide 15, 4th example - no two consecutive letters in w are the same:
		// "(ab)*(a or epsilon) or (ba)*(b or epsilon)"
		regex := UnionExp(ConcatExp(StarExp(ConcatExp(regex1, regex2)), UnionExp(regex1, EpsilonExp)),
			ConcatExp(StarExp(ConcatExp(regex2, regex1)), UnionExp(regex2, EpsilonExp)));
	}

	// slide 21: "For Every Regular Expression There is a Corresponding FSM"
	lemma KleeneTheorem1(regex: RegularExpression, sigma: set<Symbol>) returns (M: NDFSM)
		requires ValidRegularExpression(regex, sigma)
		ensures ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma)
		decreases RegexVariant(regex), regex
	{
		match regex
		case EmptyExp =>
			M := ({0}, sigma, {}, 0, {});
			assert ValidNDFSM(M);
			assert L_NDFSM(M) == L_Regex(regex, sigma) by {
				assert ND_A(M) == {};
				L5a(M);
				assert L_Regex(regex, sigma) == iset{};
			}
		case EpsilonExp =>
			M := ({0}, sigma, {}, 0, {0});
			assume ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma); // Challenge: prove!
		case SymbolExp(symbol) =>
			M := ({0, 1}, sigma, {(0,sym(symbol),1)}, 0, {1});
			assume ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma); // Challenge: prove!
		case ConcatExp(left, right) =>
			var M1 := KleeneTheorem1(left, sigma);
			var M2 := KleeneTheorem1(right, sigma);
			var M2' := RenameAllStates_ND(M2, NewState(ND_K(M1)));
			var concatenationTransitions := (set p | p in ND_A(M1) :: (p, epsilon, ND_s(M2')));
			var DELTA := ND_Delta(M1)+ND_Delta(M2')+concatenationTransitions;
			M := (ND_K(M1) + ND_K(M2'), sigma, DELTA, ND_s(M1), ND_A(M2'));
			assume ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma); // Challenge: prove!
		case UnionExp(left, right) =>
			var M1 := KleeneTheorem1(left, sigma);
			var M2 := KleeneTheorem1(right, sigma);
			var M2' := RenameAllStates_ND(M2, NewState(ND_K(M1)));
			var K := ND_K(M1) + ND_K(M2);
			var s := NewState(K);
			K := K + {s};
			var unionTransitions := {(s, epsilon, ND_s(M1)), (s, epsilon, ND_s(M2'))};
			var DELTA := ND_Delta(M1)+ND_Delta(M2')+unionTransitions;
			M := (K, sigma, DELTA, s, ND_A(M1)+ND_A(M2'));
			assume ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma); // Challenge: prove!
		case StarExp(regex1) =>
			var M1 := KleeneTheorem1(regex1, sigma);
			var K := ND_K(M1);
			var s := NewState(K);
			K := K + {s};
			var starTransitions := {(s, epsilon, ND_s(M1))}+(set p | p in ND_A(M1) :: (p, epsilon, ND_s(M1)));
			var DELTA := ND_Delta(M1)+starTransitions;
			var A := ND_A(M1)+{s};
			M := (K, sigma, DELTA, s, A);
			assume ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma); // Challenge: prove!
		case PlusExp(regex1) =>
			var regex2 := ConcatExp(regex1, StarExp(regex1));
			assert RegexVariant(regex) == 2*RegexVariant(regex1)+1 > RegexVariant(regex1)+RegexVariant(regex1) == RegexVariant(regex2);
			M := KleeneTheorem1(regex2, sigma);
		case Parentheses(regex1) =>
			M := KleeneTheorem1(regex1, sigma);
			assert ValidNDFSM(M) && L_NDFSM(M) == L_Regex(regex, sigma);
	}

	lemma L5a(M: NDFSM)
		requires ValidNDFSM(M) && ND_A(M) == {}
		ensures L_NDFSM(M) == iset{}

	// slide 66: Simplifying Regular Expressions
	lemma UnionIsCommutative(alpha: RegularExpression, beta: RegularExpression, sigma: set<Symbol>)
		requires ValidRegularExpression(alpha, sigma) && ValidRegularExpression(beta, sigma)
		ensures L_Regex(UnionExp(alpha, beta), sigma) == L_Regex(UnionExp(beta, alpha), sigma)
	{}

	lemma {:verify false} ConcatenatioIsAssociative(alpha: RegularExpression, beta: RegularExpression, gamma: RegularExpression, sigma: set<Symbol>)
		requires ValidRegularExpression(alpha, sigma) && ValidRegularExpression(beta, sigma) && ValidRegularExpression(gamma, sigma)
		ensures L_Regex(ConcatExp(ConcatExp(alpha, beta), gamma), sigma) == L_Regex(ConcatExp(alpha, ConcatExp(beta, gamma)), sigma)
	{
		calc {
			L_Regex(ConcatExp(ConcatExp(alpha, beta), gamma), sigma);
		== // L_Regex of concatenation 
			LanguageConcat(L_Regex(ConcatExp(alpha, beta), sigma), L_Regex(gamma, sigma));
		== // L_Regex of concatenation
			LanguageConcat(LanguageConcat(L_Regex(alpha, sigma), L_Regex(beta, sigma)), L_Regex(gamma, sigma));
		== // definition of RegLangConcat
			LanguageConcat((iset w1, w2 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) :: Concat(w1, w2)), L_Regex(gamma, sigma));
		== // definition of RegLangConcat
			(iset w1', w2' | w1' in (iset w1, w2 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) :: Concat(w1, w2)) &&
				w2' in L_Regex(gamma, sigma) :: Concat(w1', w2'));
		==
			(iset w1, w2, w3 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) && w3 in L_Regex(gamma, sigma) ::
				Concat(w1+w2, w3));
		==
			(iset w1, w2, w3 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) && w3 in L_Regex(gamma, sigma) ::
				(w1+w2)+w3);
		== { L5b(alpha, beta, gamma, sigma); }
			(iset w1, w2, w3 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) && w3 in L_Regex(gamma, sigma) ::
				w1+(w2+w3));
		==
			(iset w1, w2, w3 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) && w3 in L_Regex(gamma, sigma) ::
				Concat(w1, w2+w3));
		==
			(iset w1, w2, w3 | w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) && w3 in L_Regex(gamma, sigma) ::
				Concat(w1, Concat(w2, w3)));
		==
			(iset w1', w2' | w1' in L_Regex(alpha, sigma) &&
				w2' in (iset w1, w2 | w1 in L_Regex(beta, sigma) && w2 in L_Regex(gamma, sigma) :: Concat(w1, w2)) :: Concat(w1', w2'));
		== // definition of RegLangConcat
			LanguageConcat(L_Regex(alpha, sigma), (iset w1, w2 | w1 in L_Regex(beta, sigma) && w2 in L_Regex(gamma, sigma) :: Concat(w1, w2)));
		== // definition of RegLangConcat
			LanguageConcat(L_Regex(alpha, sigma), LanguageConcat(L_Regex(beta, sigma), L_Regex(gamma, sigma)));
		== // L_Regex of concatenation
			LanguageConcat(L_Regex(alpha, sigma), L_Regex(ConcatExp(beta, gamma), sigma));
		== // L_Regex of concatenation
			L_Regex(ConcatExp(alpha, ConcatExp(beta, gamma)), sigma);
		}
	}

	lemma L5b(alpha: RegularExpression, beta: RegularExpression, gamma: RegularExpression, sigma: set<Symbol>)
		requires ValidRegularExpression(alpha, sigma) && ValidRegularExpression(beta, sigma) && ValidRegularExpression(gamma, sigma)
		ensures forall w1, w2, w3 :: w1 in L_Regex(alpha, sigma) && w2 in L_Regex(beta, sigma) && w3 in L_Regex(gamma, sigma) ==>
			(w1+w2)+w3 == w1+(w2+w3)
}