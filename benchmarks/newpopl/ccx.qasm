OPENQASM 3.0;

include "stdgates.inc";

// ============================================================================
// CONSTANTS
// ============================================================================

const uint nodd = 9;   // For clean ancilla n-qubit CCX (odd n only)
const uint neven = 8;  // For conditionally clean toffoli (even/odd n)

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

// AND for uint arrays
def ANDuint(uint[nodd] reg)-> bool {
    bool out = 1;
    for int i in [0:nodd-1] { out = out * reg[i]; }
    return out;
}

// AND for bit arrays
def ANDbit(bit[neven] reg)->bit {
    bit out=1;
    for int i in [0:neven-1] { out = out * reg[i]; }
    return out;
}

// ============================================================================
// CLEAN ANCILLA N-QUBIT TOFFOLI (odd n=9)
// ============================================================================

@pre    c   ~> |cval:uint[nodd]>  ,  tar   ~> |tval:bit>          ,  anc ~> |0>
@post   c   ~> |cval>      ,     tar   ~> |tval+ANDuint(cval)>    ,  anc ~> |0>
def cleanancillanqubitccx (qubit[nodd] c, qubit tar, qubit anc) {
    //Step-1
    ccx c[0], c[1], anc;
    for uint i in [1:nodd/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
    for uint i in [0:nodd-4]   { x c[i]; }
    //Step-2
    ccx c[nodd-1], c[nodd-4], c[nodd-5];
    for uint i in [3:nodd/2] { ccx c[nodd-2*i+1], c[nodd-2*i], c[nodd-2*i-1]; }
    //Step-3
    ccx anc, c[0], tar;
    //Step-4
    for uint i in [0:nodd/2-3] { ccx c[2*i+2], c[2*i+1], c[2*i]; }
    ccx c[8], c[5], c[4];
    for uint i in [0:nodd-4]   { x c[i]; }
    for uint i in [1:nodd/2-1] { ccx c[nodd-2*i], c[nodd-2*i-1], c[nodd-2*i-2]; }
    ccx c[0], c[1], anc;
}

// ============================================================================
// CONDITIONALLY CLEAN TOFFOLI (even/odd n=8)
// Implements the Section 5.2 / Figure 3 construction from
// Khattar–Gidney (arXiv:2407.17966): the 2n−3 Toffoli, O(n)-depth
// n-bit Toffoli using one clean ancilla.
// ============================================================================

@pre    c   ~> |cval:bit[neven]>  ,  target   ~> |tval:bit>          ,  anc ~> |0>, neven>=5
@post   c   ~> |cval>      ,     target   ~> |tval+ANDbit(cval)>    ,  anc ~> |0>
def cleanancillanqubittoffoli (qubit[neven] c, qubit target, qubit anc) {
    if (neven%2 == 0) {
        //Step-1
        ccx c[0], c[1], anc;
        for uint i in [1:neven/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
        for uint i in [0:neven-5]   { x c[i]; }
        x c[neven-3];
        //Step-2
        ccx c[neven-3], c[neven-5], c[neven-6];
        for uint i in [4:neven/2] { ccx c[neven-2*i+2], c[neven-2*i+1], c[neven-2*i]; }
        // //Step-3
        ccx anc, c[0], target;
        // //Step-4
        for uint i in [4:neven/2] { ccx c[2*i-6], c[2*i-7], c[2*i-8]; }
        ccx c[neven-3], c[neven-5], c[neven-6];
        for uint i in [0:neven-5]   { x c[i]; }
        x c[neven-3];
        for uint i in [1:neven/2-1] { ccx c[neven-2*i+1], c[neven-2*i], c[neven-2*i-1]; }
        ccx c[0], c[1], anc;
    }
    if (neven%2 == 1){
        //Step-1
        ccx c[0], c[1], anc;
        for uint i in [1:neven/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
        for uint i in [0:neven-4]   { x c[i]; }
        //Step-2
        ccx c[neven-1], c[neven-4], c[neven-5];
        for uint i in [3:neven/2] { ccx c[neven-2*i+1], c[neven-2*i], c[neven-2*i-1]; }
        //Step-3
        ccx anc, c[0], target;
        //Step-4
        for uint i in [0:neven/2-3] { ccx c[2*i+2], c[2*i+1], c[2*i]; }
        ccx c[neven-1], c[neven-4], c[neven-5];
        for uint i in [0:neven-4]   { x c[i]; }
        for uint i in [1:neven/2-1] { ccx c[neven-2*i], c[neven-2*i-1], c[neven-2*i-2]; }
        ccx c[0], c[1], anc;
    }
}

// ============================================================================
// DIRTY ANCILLA 4-QUBIT TOFFOLI
// ============================================================================

@pre    c   ~> |cval:bit[3]>   ,  t   ~> |tval:bit>                        ,  anc ~> |ancval:bit>
@post   c   ~> |cval>       ,  t   ~> |tval+cval[0]*cval[1]*cval[2]>    ,  anc ~> |ancval>
def dirtyancillacccx (qubit[3] c, qubit t, qubit anc) {
    ccx c[0], c[1], anc;
    ccx anc, c[2], t;
    ccx c[0], c[1], anc;
    ccx anc, c[2], t;
}

// ============================================================================
// GIDNEY AND GATE
// ============================================================================

@pre  a ~> |q:bit>, b ~> |r:bit>, c ~> |0> + exp(1/4)|1>
@post a ~> |q>,     b ~> |r>,     c ~> |q*r>
gate and a, b, c {
    cx a, c;
    cx b, c;
    cx c, a;
    cx c, b;
    tdg a;
    tdg b;
    t c;
    cx c, a;
    cx c, b;
    h c;
    s c;
}

@pre    a   ~> |q:bit> ,  b   ~> |r:bit> ,    c   ~> |q*r>
@post   a   ~> |q> ,      b   ~> |r> ,        c   ~> |0>
def cgtof2 (qubit a, qubit b, qubit c) {
    h c;
    bit meas = measure c;
    if (meas == 1){
        cz a, b;
        x c;
    }
}

// ============================================================================
// JONES TOFFOLI
// ============================================================================

@pre  a ~> |A:bit>, b ~> |B:bit>, c ~> |C:bit>, anc ~> |0>
@post a ~> |A>,     b ~> exp(-(A*B)/2)|B>,     c ~> |C+A*B>, anc ~> |0>
gate cjtofstar a, b, c, anc {
    h c;
    cx a, anc;
    cx c, a;
    cx c, b;
    cx b, anc;
    tdg a;
    tdg b;
    t c;
    t anc;
    cx b, anc;
    cx c, b;
    cx c, a;
    cx a, anc;
    h c;
}

@pre    a   ~> |q:bit>,  b  ~> |r:bit>,   c ~> |w:bit> , anc1 ~> |0>, anc2~> |0>
@post   a   ~> |q>,  b  ~> |r> ,  c ~> |w + q*r>, anc1 ~> |0> , anc2 ~> |0>
def cjtof (qubit a, qubit b, qubit c, qubit anc1, qubit anc2) {
    cjtofstar a, b, anc1, anc2;
    s anc1;
    cx anc1, c;
    h anc1;
    bit meas = measure anc1;
    if (meas == 1){
        cz a, b;
        x anc1;
    }
}
