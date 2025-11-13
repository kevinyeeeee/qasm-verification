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
def cg_tof_2 (qubit a, qubit b, qubit c) {
    h c;
    bit meas = measure c;
    if (meas == 1){ 
        cz a, b; 
        x c;
    }
}