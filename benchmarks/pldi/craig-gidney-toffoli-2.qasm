include "stdgates.inc";

@pre    a   ~> |q:bit> ,  b   ~> |r:bit> ,    c   ~> |p:bit>, p == q*r
@post   a   ~> |q> ,      b   ~> |r> ,        c   ~> |0>
def cg_tof_2 (qubit a, qubit b, qubit c) {
    bit meas = measure c;
    if (meas == 1){ 
        cz a, b; 
        x c;
    }
}