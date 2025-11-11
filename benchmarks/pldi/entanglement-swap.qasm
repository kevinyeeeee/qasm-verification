// An example meant to show the ability to perform local reasoning in
// an entangled context. Notably, invoking teleport uses a type of frame rule
// which is inadmissible in typical quantum separation logics, where the 
// separating conjunction asserts separability of states.
//
// It's an interesting example because without some notion of basis locality,
// this fairly trivial property is challenging to express. In particular, the
// obvious specification for teleport would have the form
//          {t == |psi> && ...} teleport {b == |psi>}
// but this obviously can't be applied in the entanglement swapping case below,
// as a & b are not separable. The basis-independent entanglement-modular 
// specification of teleport is hence
//          { |psi> } teleport { (I_{frame} \otimes teleport_{t,a,b})|psi> }
// where |psi> is the state of the entire memory, but obviously this tells us
// nothing useful about teleport.
//
// On a side note, it also gives an example where:
//   1. we want a post condition that doesn't describe all qubits, and
//   2. initializing qubits in |0> rather than resetting

include "stdgates.inc";


@pre  (a,b) ~> |0,0>
@post (a,b) ~> sum{x:bit}.|x,x>
def bellPrep(qubit a, qubit b) {
  h a;
  cx a,b;
}

@pre  t ~> |x:bit>,  (a,b) ~> sum{x:bit}.|x,x>
@post b ~> |x>, discard (t,a)
def teleport(qubit t, qubit a, qubit b) {
  bit[2] res;

  // Bell measurement
  cx t,a;
  h t;
  measure t -> res[0];
  measure a -> res[1];

  // Classical correction
  if (res[0] == 1) { z b; }
  if (res[1] == 1) { x b; }
}

@pre  (a,b[0]) ~> sum{x:bit}.|x,x>, (b[1],c) ~> sum{x:bit}.|x,x>
@post (a,c) ~> sum{x:bit}.|x,x>, discard (b[0],b[1])
def distributeBell(qubit a, qubit[2] b, qubit c) {

  // Teleport b[0] to c
  teleport(b[0],b[1],c);

}
