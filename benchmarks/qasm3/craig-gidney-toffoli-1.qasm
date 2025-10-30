include "stdgates.inc";

@pre    a   == |x>
    &&  b   == |y>
    &&  c   == |0>
@post   a   == |x>
    &&  b   == |y>
    &&  c   == |x*y>
def cj_tof (qubit a, qubit b, qubit c) {
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