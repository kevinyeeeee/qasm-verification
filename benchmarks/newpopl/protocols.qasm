OPENQASM 3.0;

include "stdgates.inc";

// ============================================================================
// CONSTANTS
// ============================================================================

const uint n = 10;  // For QFT

// ============================================================================
// COMMON: BELL STATE PREPARATION
// ============================================================================

// Bell state preparation (array version)
@pre    q ~> |0,0>
@post   q ~> sum{r}.|r,r>
def bell_state_prep (qubit[2] q) {
    h q[0];
    cx q[0], q[1];
}


// ============================================================================
// ENTANGLEMENT SWAP / TELEPORTATION
// ============================================================================

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

@pre  t ~> |q:bit>,  (a,b) ~> sum{q:bit}.|q,q>
@post b ~> |q>, discard (t,a)
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

@pre  (a,b[0]) ~> sum{q:bit}.|q,q>, (b[1],c) ~> sum{q:bit}.|q,q>
@post (a,c) ~> sum{q:bit}.|q,q>, discard (b[0],b[1])
def distributeBell(qubit a, qubit[2] b, qubit c) {

  // Teleport b[0] to c
  teleport(b[0],b[1],c);

}

// ============================================================================
// QUANTUM FOURIER TRANSFORM
// ============================================================================

@pre a ~> |q:uint[n]>
@post a ~> sum{r:uint[n]}.exp(2*q*r/(2^n))|r>
def qftn(qubit[n] a) {
    for int i in [0:(n/2)-1] {
      swap a[i], a[n-1-i];
    }
    for int i in [0:n-1] {
        h a[i];
        for int j in [i+1:n-1] {
            crz(2*pi/(2**(j-i+1))) a[i], a[j];
        }
    }
}

// ============================================================================
// SUPERDENSE CODING
// ============================================================================

@pre q ~> |0>|0> + |1>|1> , a ~> c:bit[2] , b ~> 0
@post b ~> c
def sd(qubit[2] q, bit[2] a, bit[2] b) {
  if (a[1] == 1) {
    x q[0];
  }
  if (a[0] == 1) {
    z q[0];
  }
  cx q[0], q[1];
  h q[0];
  b[0] = measure q[0];
  b[1] = measure q[1];
}

// ============================================================================
// T-GATE TELEPORTATION
// ============================================================================

@pre    tstate            ~> |0> , data               ~> |psi:bit>
@post   tstate            ~> |0> , data               ~> exp(psi/4)|psi>
def t_gate_teleportation (qubit tstate, qubit data) {
    //prepare T-state
    h tstate;
    t tstate;

    //entangle
    cx data, tstate;

    //conditional S correction on data
    bit m = measure tstate;
    if ( m == 1 ){
        x tstate;
        s data;
    }
}

@pre psi ~> |a:bit>, anc ~> |0,0>
@post psi ~> |a>, anc ~> |0,0>
def rus(qubit psi, qubit[2] anc) {
  uint[2] flags;
  flags = 3;

  @assert psi ~> sum{b:bit,c:bit}.exp(b*c/2 + a*b*c + b*flags[0] + c*flags[1] + 3*a/2)|a>, anc ~> |0,0>
  while(flags != 0) {
    h anc[0];
    h anc[1];
    ccx anc[0], anc[1], psi;
    s psi;
    ccx anc[0], anc[1], psi;
    z psi;
    h anc[0];
    h anc[1];
    //t anc[0];
    //t anc[1];
    //cz anc[0],anc[1];
    //ct anc[0],anc[1];
    measure anc[0] -> flags[0];
    measure anc[1] -> flags[1];
    reset anc;
  }
}