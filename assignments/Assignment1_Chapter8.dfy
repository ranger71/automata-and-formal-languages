include "../lectures/AFL-week07.dfy"

module Assignment1_Chapter8 {
	import opened Week01
	import opened Lecture02
	import opened Lecture03
	import opened Lecture04
	import opened Lecture05
	import opened Lecture07

	/* Exercise 2.
	
		For each of the following languages L, state whether L is regular or not and prove your answer.

		To prove that a language is regular you can either
		(1) show a finite state machine that accepts it (explain why this is true),
		(2) provide a regular expression that defines it (again, explain why this is so), or
		(3) use the closure properties of Chapter 8.

		To prove a language is NOT regular you can use the pumping theorem for regular languages
		and possibly combine it with closure properties, assuming that the lanuguage *is* regular and reaching a contradiction.

		If your answer is included in an attached pdf file, state here clearly the page number.
	*/
	ghost const L_2a := iset w | ValidString(w, {'a', 'b', 'c'}) && 
		forall x :: Prefix(x, w) ==> Count('a', w) == Count('b', w) == Count('c', w)
	ghost const L_2b := iset w | ValidString(w, {'a', 'b', 'c'}) && 
		exists x :: Prefix(x, w) && Count('a', w) == Count('b', w) == Count('c', w)
	ghost const L_2c := iset w | ValidString(w, {'a', 'b', 'c'}) && 
		exists x :: Prefix(x, w) && x != EPSILON && Count('a', w) == Count('b', w) == Count('c', w)
}