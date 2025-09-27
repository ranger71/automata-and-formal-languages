include "AFL-week01.dfy"

// context-free grammars (Chapter 11)
module Lecture08 {
	import opened Week01

	type Symbol = char
	type String = seq<Symbol>

	type Language = iset<String>

	// definition of a context-free grammar (slide 22)
	type CFG = (seq<Variable>, seq<Symbol>, seq<Rule>, string)

	datatype Variable = NT(name: string) | T(c: Symbol)
	type Rule = (string, seq<Variable>)

	function CFG_V(G: CFG): seq<Variable> { G.0 }
	function CFG_Sigma(G: CFG): seq<Symbol> { G.1 }
	function CFG_R(G: CFG): seq<Rule> { G.2 }
	function CFG_S(G: CFG): string { G.3 }

	function Rule_LHS(R: Rule): string { R.0 }
	function Rule_RHS(R: Rule): seq<Variable> { R.1 }

	ghost predicate ValidCFG(G: CFG) {
		(forall c :: c in CFG_Sigma(G) ==> T(c) in CFG_V(G)) &&
		NT(CFG_S(G)) in CFG_V(G) &&
		(forall rule :: rule in CFG_R(G) ==> NT(Rule_LHS(rule)) in CFG_V(G) && (forall v :: v in Rule_RHS(rule) ==> v in CFG_V(G)))
	}

	// see slide 23
	ghost predicate ValidDerivationStep(G: CFG, x: seq<Variable>, y: seq<Variable>)
		requires ValidCFG(G)
	{
		(forall a :: a in x || a in y ==> a in CFG_V(G)) &&
		(exists alpha, A, beta, gamma :: x == alpha + [NT(A)] + beta && (A, gamma) in CFG_R(G) && y == alpha + gamma + beta)
	}

	ghost predicate ValidDerivation(G: CFG, X: seq<seq<Variable>>)
		requires ValidCFG(G) && forall x, v :: x in X && v in x ==> v in CFG_V(G)
	{
		|X| >= 1 && forall i :: 0 <= i && i+1 < |X| ==> ValidDerivationStep(G, X[i], X[i+1])
	}

	function StringToTerminals(w: String): seq<Variable> {
		if w == [] then [] else [T(w[0])] + StringToTerminals(w[1..])
	}

	function TerminalsToString(X: seq<Variable>): String
		requires TerminalsOnly(X) // forall x :: x in X ==> x.T?
	{
		if X == [] then "" else [X[0].c] + TerminalsToString(X[1..])
	}

	ghost function L_CFG(G: CFG): Language
		requires ValidCFG(G)
	{
		iset w | ValidString(w, set c | c in CFG_Sigma(G)) &&
			exists X: seq<seq<Variable>> ::
				|X| >= 2 && X[0] == [NT(CFG_S(G))] && X[|X|-1] == StringToTerminals(w) && 
				(forall x, v :: x in X && v in x ==> v in CFG_V(G)) && ValidDerivation(G, X)
	}

	const EPSILON: String := []
	const EMPTY_LANGUAGE: Language := iset{}

	method {:verify false} PrintDerivations_BreadthFirst_LeftToRight(G: CFG, max_derivation_length: nat) returns (strings: seq<String>)
		requires ValidCFG(G) && max_derivation_length > 0
		ensures forall w :: w in strings ==> w in L_CFG(G)
	{
		strings := [];
		var DerivationQueue := [([NT(CFG_S(G))], 0)];
		while DerivationQueue != []
			invariant ValidCFG(G) && forall D, len, V :: (D, len) in DerivationQueue && V in D ==> 0 <= len < max_derivation_length && V in CFG_V(G)
		{
			var top := DerivationQueue[0];
			var Derivation, depth := top.0, top.1;
			DerivationQueue := DerivationQueue[1..];
			print "\nThe current variable sequence (at derivation depth ", depth, ") is ";
			PrintVariables_NoCommaSeparation(Derivation);
			if TerminalsOnly(Derivation) {
				var w := TerminalsToString(Derivation);
				strings := strings + [w];
				print ": terminals only! String #", |strings|, " is \"", w, "\".";
			}
			else {
				print ": non-terminals exist.";
				if depth == max_derivation_length {
					print "\nReached the derivation-length bound. Quit this derivation.";
				}
				else {
					var count_matches := 0;
					var i := 0;
					while i != |Derivation|
						invariant 0 <= i <= |Derivation| && 0 <= depth < max_derivation_length
						invariant ValidCFG(G) && forall V :: V in Derivation ==> V in CFG_V(G)
						decreases |Derivation|-i
					{
						var V := Derivation[i];
						match V {
						case NT(n) =>
							var rules := MatchRules(G, V);
							var j := 0;
							while j != |rules|
								invariant 0 <= j <= |rules|
							{
								var Derivation' := Derivation[..i] + Rule_RHS(rules[j]) + Derivation[i+1..];
								PrintDerivationStep(Derivation, Derivation');
								DerivationQueue := DerivationQueue + [(Derivation', depth + 1)];
								count_matches := count_matches + 1;
								j := j + 1;
							}
						case T(c) => // skip
						}
						i := i + 1;
					}
					if count_matches == 0 {
						print "\nEnd of this derivation: no rule matches any non-terminal in this variable sequence.";
					}
					else if count_matches == 1 {
						print "\nAdded one derivation of length ", depth + 1, " to the queue.";
					}
					else {
						print "\nAdded ", count_matches, " derivations of length ", depth + 1, " to the queue.";
					}
				}
			}
		}
	}

	predicate TerminalsOnly(vars: seq<Variable>)
		decreases |vars|
	{
		vars == [] || (vars[0].T? && TerminalsOnly(vars[1..]))
	}

	method PrintDerivationStep(before: seq<Variable>, after: seq<Variable>) {
		print "\n";
		PrintVariables_NoCommaSeparation(before);
		print " => ";
		PrintVariables_NoCommaSeparation(after);
	}

	method PrintVariables_NoCommaSeparation(vars: seq<Variable>) {
		PrintVariableSequence(vars, false); // no comma
	}

	method PrintVariables(vars: seq<Variable>) {
		PrintVariableSequence(vars, true); // comma-separated
	}

	method PrintVariableSequence(vars: seq<Variable>, comma_separated: bool) {
		print "[";
		if |vars| > 0 {
			PrintVariable(vars[0]);
			var i := 1;
			while i != |vars|
				invariant 1 <= i <= |vars|
			{
				print if comma_separated then ", " else " "; 
				PrintVariable(vars[i]);
				i := i + 1;
			}
		}
		print "]";
	}

	method PrintVariable(V: Variable) {
		match V {
			case NT(n) => print n;
			case T(c) => print c;
		}
	}

	method PrintRules(rules: seq<Rule>) {
		var i := 0;
		print "[";
		while i != |rules|
			invariant 0 <= i <= |rules|
			decreases |rules| - i
		{
			print "[";
			PrintVariable(NT(Rule_LHS(rules[i])));
			print " --> ";
			PrintVariables_NoCommaSeparation(Rule_RHS(rules[i]));
			i := i + 1;
			print if i == |rules| then "]" else "], ";
		}
		print "]";
	}
	
	method PrintCFG(G: CFG) {
		print "\n(variables: ";
		PrintVariables(CFG_V(G));
		print ", alphabet: [";
		var alphabet := CFG_Sigma(G);
		if alphabet != []
		{
			print alphabet[0];
			var i := 1;
			while i != |alphabet|
				invariant 1 <= i <= |alphabet|
			{
				print ", ", alphabet[i]; 
				i := i + 1;
			}
		}
		print "], rules: ";
		PrintRules(CFG_R(G));
		print ", starting non-terminal: ", CFG_S(G), ")";
	}

	method {:verify false} MatchRules(G: CFG, V: Variable) returns (matched_rules: seq<Rule>)
		requires ValidCFG(G) && V in CFG_V(G) && V.NT?
		ensures (set r | r in matched_rules) == (set r | r in CFG_R(G) && NT(Rule_LHS(r)) == V)
	{
		matched_rules := [];
		var i := 0;
		var all_rules := CFG_R(G);
		while i != |all_rules|
			invariant 0 <= i <= |all_rules| && all_rules == CFG_R(G)
			decreases |all_rules| - i
		{
			if NT(Rule_LHS(all_rules[i])) == V {
				matched_rules := matched_rules + [all_rules[i]];
			}
			i := i + 1;
		}
	}

	method {:verify false} SimulateCFG(G: CFG, max_derivation_length: nat)
		requires ValidCFG(G)
	{
		print "\nDefine the context free grammar G as follows: \n";
		PrintCFG(G);
		print "\n\nPerform derivations of up to length ", max_derivation_length, " on G starting with the non-terminal ", CFG_S(G), ":\n";
		var strings := PrintDerivations_BreadthFirst_LeftToRight(G, max_derivation_length);
		if |strings| == 0 {
			print "\n\nNo strings could be generated by grammar G in at most ", max_derivation_length, " derivation steps.\n";
		}
		else if |strings| == 0 {
			print "\n\nAll derivations of length up to ", max_derivation_length, " by grammar G generated one string: \"", strings[0], "\"\n";
		}
		else {
			print "\n\nAll derivations of length up to ", max_derivation_length, " by grammar G generated ", |strings|, " strings: [";
			var i := 0;
			while i != |strings|
				invariant 0 <= i <= |strings|
				decreases |strings| - i
			{
				print "\"", strings[i], "\"", if i + 1 != |strings| then ", " else "";
				i := i + 1;
			}
			print "]\n";
		}
	}

	method Main'() {
		// slide 22: example grammar
		var G := ([NT("S"), T('a'), T('b')],
			['a', 'b'], [("S", [T('a'), NT("S"), T('b')]), ("S", [])], "S");
		assert ValidDerivationStep(G, [NT("S")], []) by {
			var x, y := [NT("S")], [];
			var alpha, A, beta, gamma := [], "S", [], [];
			assert x == alpha + [NT(A)] + beta && (A, gamma) in CFG_R(G) && y == alpha + gamma + beta;
		}
		SimulateCFG(G, 5);
		SimulateCFG(G, 10);
	}
}