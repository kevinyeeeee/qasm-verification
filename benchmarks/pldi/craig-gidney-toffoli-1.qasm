include "stdgates.inc";

@pre    a   == |aval> &  b   == |bval> &  c   == |0>+(exp(1/4) * |1>)
@post   a   == |aval> &  b   == |bval> &  c   == |aval*bval>
def cg_tof_1 (qubit a, qubit b, qubit c) {
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