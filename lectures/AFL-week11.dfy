module Week11 {
/*
	Tutorial #11:

	Chapter 12 Exercise 1b

	L1b := iset w, i, j | ValidString(w, {'a, 'b'}) && 0 <= i && 0 <= j && 2*i == 3*j + 1 && w == Concat(Rep("a", i), Rep("b", j) :: w;

	"aab"

	state: 1
	stack: epsilon
	suffix: "aab"

	state: 1
	stack: "aa"
	suffix: "ab"

	state: 1
	stack: "aaaa"
	suffix: "b"

	state: 2
	stack: "a"
	suffix: ""

	state: 3 // accepting state!
	stack: "" // the stack is empty!
	suffix: "" // the string suffix is empty: we read all the input string!

	i == 2
	j == 1

		2*i
	==
		2*2
	==
		4
	==
		3*1+1
	==
		3*j+1

	exercise: try the next string: "aaaaabbb"
	i == 5
	j == 3


	Exerise 1c

	"aaaabb"

	state: 1
	stack: ""
	suffix: "aaaabb"

	// after 4 steps
	state: 1
	stack: "aaaa"
	suffix: "bb"

	// after 2 more steps
	state: 1
	stack: ""
	suffix: ""


	"bbaaaa"

	state: 1
	stack: ""
	suffix: "bbaaaa"

	// after two steps
	state: 1
	stack: "bbbb"
	suffix: "aaaa"

	// after four more steps
	state: 1
	stack: ""
	suffix: ""

	Our initial PDA was not good enough: it did not accept the string: "aba"

	Try it! And then try to add more transitions to accept such cases too!

	Need to add a transition: b / a / b

	*/


	/*
	Lecture #11

	12:29

	say for example k=5, [just for illustration; we never write the proof with just an example]

	w = aaaaabbbbbccccc

	case 1: v or y spans regions

	q=2,

	say v = aab, y=epsilon

	w' = uvvxyyz = aaaaaabaabbbbbccccc !in L


	13:51

	Chapter 17 slide 9:
	       1
	_ aaab 2
	_aaab  3
	$_aab  3
	$a_ab  3
	$aa_b  4
	$a_a#  4
	$a$_#  3
	$a$_## 3

	$$$###

	aaabbb

	// trying again (after the lecture), let's write the configuration using 4 parts:

	// (the state, the string left of the tape head (= the scanner), the scanned square, and the string to the right of the scanner)

	// and for illustration, on the left column, let's write the contents of the tape as a single string
	// with the ^ symbol showing the location of the scanner at each step

	Tape     | Configuration            
	---------+--------------------------
	 aaab    | (1, "", ' ', "aaab")   |-
	^        |
	 aaab    | (2, "", 'a', "aab")    |-
	 ^
	 $aab    | (3, "$", 'a', "ab")    |-
	  ^
	 $aab    | (3, "$a", 'a', "b")    |-
	   ^
	 $aab    | (3, "$aa", 'b', "")    |-
	    ^
	 $aa#    | (4, "$a", 'a', "#")    |-
	   ^
	 $a$#    | (3, "$a$", '#', "")    |-
	    ^
	 $a$#    | (3, "$a$#", ' ', "")   |-
	     ^
	 $a$##   | (4, "$a$", '#', "#")   |-
	    ^
	 $a$##   | (4, "$a", '$', "##")   |-
	   ^
	 $a$##   | (4, "$", 'a', "$##")   |-
	  ^
	 $$$##   | (3, "$$", '$', "##")   |-
	   ^
	 $$$##   | (3, "$$$", '#', "#")   |-
	    ^
	 $$$##   | (3, "$$$#", '#', "")   |-
	     ^
	 $$$##   | (3, "$$$##", ' ', "")   |-
	      ^
	 $$$###  | (4, "$$$#", '#', "#")   |-
	     ^
	 $$$###  | (4, "$$$", '#', "##")   |-
	    ^
	 $$$###  | (4, "$$", '$', "###")   |-
	   ^
	 $$$###  | (4, "$", '$', "$###")   |-
	  ^
	 $$$###  | (4, "", '$', "$$###")   |-
	 ^
	 $$$###  | (4, "", ' ', "$$$###")  |-
	^
	 $$$###  | (5, "", '$', "$$###")   |-
	 ^
	 a$$###  | (5, "a", '$', "$###")  |-
	  ^
	 aa$###  | (5, "aa", '$', "###")  |-
	   ^
	 aaa###  | (5, "aaa", '#', "##")  |-
	    ^
	 aaab##  | (5, "aaab", '#', "#")  |-
	     ^
	 aaabb#  | (5, "aaabb", '#', "")  |-
	      ^
	 aaabbb  | (5, "aaabbb", ' ', "") |-
	       ^
	 aaabbb  | (6, "aaabb", 'b', "")  |-
	      ^

	The machine halts in state 6 with the expected output on the tape: "aaabbb"

	*/
}