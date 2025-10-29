include "stdgates.inc";

// @pre    a   == |x>
//     &&  b   == |y>
//     &&  c   == |z>
//     &&  anc == |0>
// @post   a   == |x>
//     &&  b   == |y>
//     &&  c   == |z+xy>
//     &&  anc == |0>  
def cj_tof (qubit a, qubit b, qubit c, qubit anc) {
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
    s anc;
    cx anc, c;
    h anc;
    bit[1] meas = measure anc;
    if (meas == 1){ 
        cz a, b;
        x anc;
    }
}