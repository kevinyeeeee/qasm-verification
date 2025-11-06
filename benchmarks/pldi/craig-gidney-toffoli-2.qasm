include "stdgates.inc";

@pre    a   == |aval> &  b   == |bval> &  c   == |aval*bval>
@post   a   == |aval> &  b   == |bval> &  c   == |0>
def cg_tof_2 (qubit a, qubit b, qubit c) {
    bit meas = measure c;
    if (meas == 1){ 
        cz a, b; 
        x c;
    }
}