include "stdgates.inc";

@pre    a   == |x>
    &&  b   == |y>
    &&  c   == |x*y>
@post   a   == |x>
    &&  b   == |y>
    &&  c   == |0>
def cj_tof (qubit a, qubit b, qubit c) {
    bit[1] meas = measure c;
    if (meas == 1){ 
        cz a, b; 
        x c;
    }
}