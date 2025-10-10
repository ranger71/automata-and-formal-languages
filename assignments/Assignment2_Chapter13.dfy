include "../simulators/PDA_Simulator.dfy"

/* Chapter 13: Context-Free and Noncontext-Free Languages */
module Assignment2_Chapter13 {
  import opened FormalLanguages

  // Exercise 3: show the L3 is NOT context free
  const alphabet3 := ['a', 'b', 'c', 'd']
  ghost const L3 := iset wa, wb, wc, wd, n, m | n >= 1 && m >=1 && 
    ValidString(wa, {'a'}) && ValidString(wb, {'b'}) && ValidString(wc, {'c'}) && ValidString(wd, {'d'}) && 
    |wa| == |wc| == n && |wb| == |wd| == m :: Concat(wa, Concat(wb, Concat(wc, wd)))
}
