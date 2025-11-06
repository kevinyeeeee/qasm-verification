include "stdgates.inc";

@pre    a   == |x>
    &&  b   == |y>
    &&  c   == |0>+(exp(1/4) * |1>)
@post   a   == |x>
    &&  b   == |y>
    &&  c   == |x*y>
def cg_tof (qubit a, qubit b, qubit c) {
    cx a, c;
    cx b, c;
    cx c, b;
    cx c, a;
    tdg a;
    tdg b;
    t c;
    cx c, a;
    cx c, b;
    h c;
    s c;
}