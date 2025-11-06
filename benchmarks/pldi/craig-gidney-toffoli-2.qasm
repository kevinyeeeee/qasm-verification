include "stdgates.inc";

@pre    a   == |x>
    &&  b   == |y>
    &&  c   == |x*y>
@post   a   == |x>
    &&  b   == |y>
    &&  c   == |0>
def cg_tof_2 (qubit a, qubit b, qubit c) {
    bit meas = measure c;
    if (meas == 1){ 
        cz a, b; 
        x c;
    }
}