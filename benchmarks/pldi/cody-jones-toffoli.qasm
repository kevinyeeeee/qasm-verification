include "stdgates.inc";

@pre  a ~> |A:bit>, b ~> |B:bit>, c ~> |C:bit>, anc ~> |0>
@post a ~> |A>,     b ~> exp(-(A*B)/2)|B>,     c ~> |C+A*B>, anc ~> |0>
gate cj_tof_star a, b, c, anc {
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

@pre    a   ~> |q:bit>,  b  ~> |r:bit>,   c ~> |s:bit> , anc1 ~> |0>, anc2~> |0>
@post   a   ~> |q>,  b  ~> |r> ,  c ~> |s + q*r>, anc1 ~> |0> , anc2 ~> |0> 
def cj_tof (qubit a, qubit b, qubit c, qubit anc1, qubit anc2) {
    cj_tof_star a, b, anc1, anc2;
    s anc1;
    cx anc1, c;
    h anc1;
    bit meas = measure anc1;
    if (meas == 1){ 
        cz a, b;
        x anc1;
    }
}