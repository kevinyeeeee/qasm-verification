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

//n is even such that n>=6:
//
// @pre    c   ~> |cval:bit[n]>  ,  target   ~> |tval:bit>          ,  anc ~> |0>
// @post   c   ~> |cval>      ,     target   ~> |tval+AND(cval)>    ,  anc ~> |0>
// def clean_ancilla_n_qubit_toffoli (qubit[n] c, qubit target, qubit anc) {
//     //Step-1
//     ccx c[0], c[1], anc;
//     for uint i in [1:n/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
//     for uint i in [0:n-5]   { x c[i]; }
//     x c[n-3];
//     //Step-2
//     ccx c[n-3], c[n-5], c[n-6]; 
//     for uint i in [4:n/2] { ccx c[n-2*i+2], c[n-2*i+1], c[n-2*i]; }
//     // //Step-3 
//     ccx anc, c[0], target;
//     // //Step-4
//     for uint i in [4:n/2] { ccx c[2*i-6], c[2*i-7], c[2*i-8]; }
//     ccx c[n-3], c[n-5], c[n-6]; 
//     for uint i in [0:n-5]   { x c[i]; }
//     x c[n-3];
//     for uint i in [1:n/2-1] { ccx c[n-2*i+1], c[n-2*i], c[n-2*i-1]; }
//     ccx c[0], c[1], anc;
// }

//n=8:
//
// @pre    c   ~> |cval:bit[n]>  ,  target   ~> |tval:bit>          ,  anc ~> |0>
// @post   c   ~> |cval>      ,     target   ~> |tval+AND(cval)>    ,  anc ~> |0>
// def clean_ancilla_n_qubit_toffoli (qubit[n] c, qubit target, qubit anc) {
//     ccx c[0], c[1], anc;    // (anc,0,1)
//     ccx c[3], c[2], c[1];   // (1,2,3)
//     ccx c[5], c[4], c[3];   // (3,4,5)
//     ccx c[7], c[6], c[5];   // (5,6,7)

//     // Xs on all non-ancilla pivot indices
//     x c[0];
//     x c[1];
//     x c[2];
//     x c[3];
//     x c[5];

//     ccx c[5], c[3], c[2];   // (2,3,5)
//     ccx c[2], c[1], c[0];   // (0,1,2)

//     ccx anc, c[0], target;

//     // undo Step 2
//     ccx c[2], c[1], c[0];
//     ccx c[5], c[3], c[2];

//     // undo Xs
//     x c[5];
//     x c[3];
//     x c[2];
//     x c[1];
//     x c[0];

//     // undo Step 1 ladder
//     ccx c[7], c[6], c[5];
//     ccx c[5], c[4], c[3];
//     ccx c[3], c[2], c[1];
//     ccx c[0], c[1], anc;
// }

//n is odd such that n>=5:
//
// @pre    c   ~> |cval:bit[n]>  ,  target   ~> |tval:bit>          ,  anc ~> |0>
// @post   c   ~> |cval>      ,     target   ~> |tval+AND(cval)>    ,  anc ~> |0>
// def clean_ancilla_n_qubit_toffoli (qubit[n] c, qubit target, qubit anc) {
//     //Step-1
//     ccx c[0], c[1], anc;
//     for uint i in [1:n/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
//     for uint i in [0:n-4]   { x c[i]; }
//     //Step-2
//     ccx c[n-1], c[n-4], c[n-5];
//     for uint i in [3:n/2] { ccx c[n-2*i+1], c[n-2*i], c[n-2*i-1]; }
//     //Step-3 
//     ccx anc, c[0], target;
//     //Step-4
//     for uint i in [0:n/2-3] { ccx c[2*i+2], c[2*i+1], c[2*i]; }
//     ccx c[n-1], c[n-4], c[n-5];
//     for uint i in [0:n-4]   { x c[i]; }
//     for uint i in [1:n/2-1] { ccx c[n-2*i], c[n-2*i-1], c[n-2*i-2]; }
//     ccx c[0], c[1], anc;
// }