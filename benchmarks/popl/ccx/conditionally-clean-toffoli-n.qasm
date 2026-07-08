// Implements the Section 5.2 / Figure 3 construction from
// Khattar–Gidney (arXiv:2407.17966): the 2n−3 Toffoli, O(n)-depth
// n-bit Toffoli using one clean ancilla.
include "stdgates.inc";

const uint n = 8;

def AND(bit[n] reg)->bit {
    bit out=1;
    for int i in [0:n-1] { out = out * reg[i]; }
    return out;
}

@pre    c   ~> |cval:bit[n]>  ,  target   ~> |tval:bit>          ,  anc ~> |0>, n>=5
@post   c   ~> |cval>      ,     target   ~> |tval+AND(cval)>    ,  anc ~> |0>
def clean_ancilla_n_qubit_toffoli (qubit[n] c, qubit target, qubit anc) {
    if (n%2 == 0) {
        //Step-1
        ccx c[0], c[1], anc;
        for uint i in [1:n/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
        for uint i in [0:n-5]   { x c[i]; }
        x c[n-3];
        //Step-2
        ccx c[n-3], c[n-5], c[n-6]; 
        for uint i in [4:n/2] { ccx c[n-2*i+2], c[n-2*i+1], c[n-2*i]; }
        // //Step-3 
        ccx anc, c[0], target;
        // //Step-4
        for uint i in [4:n/2] { ccx c[2*i-6], c[2*i-7], c[2*i-8]; }
        ccx c[n-3], c[n-5], c[n-6]; 
        for uint i in [0:n-5]   { x c[i]; }
        x c[n-3];
        for uint i in [1:n/2-1] { ccx c[n-2*i+1], c[n-2*i], c[n-2*i-1]; }
        ccx c[0], c[1], anc;
    }
    if (n%2 == 1){
        //Step-1
        ccx c[0], c[1], anc;
        for uint i in [1:n/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
        for uint i in [0:n-4]   { x c[i]; }
        //Step-2
        ccx c[n-1], c[n-4], c[n-5];
        for uint i in [3:n/2] { ccx c[n-2*i+1], c[n-2*i], c[n-2*i-1]; }
        //Step-3 
        ccx anc, c[0], target;
        //Step-4
        for uint i in [0:n/2-3] { ccx c[2*i+2], c[2*i+1], c[2*i]; }
        ccx c[n-1], c[n-4], c[n-5];
        for uint i in [0:n-4]   { x c[i]; }
        for uint i in [1:n/2-1] { ccx c[n-2*i], c[n-2*i-1], c[n-2*i-2]; }
        ccx c[0], c[1], anc;
    }
}
