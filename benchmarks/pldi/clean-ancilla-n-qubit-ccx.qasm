include "stdgates.inc";

const uint n = 9;

def AND(uint[n] reg)-> bool {
    bool out = 1;
    for int i in [0:n-1] { out = out * reg[i]; }
    return out;
}

@pre    c   ~> |cval:uint[n]>  ,  tar   ~> |tval:bit>          ,  anc ~> |0>
@post   c   ~> |cval>      ,     tar   ~> |tval+AND(cval)>    ,  anc ~> |0>
def clean_ancilla_n_qubit_ccx (qubit[n] c, qubit tar, qubit anc) {
    //Step-1
    ccx c[0], c[1], anc;
    for uint i in [1:n/2-1] { ccx c[2*i+1], c[2*i], c[2*i-1]; }
    for uint i in [0:n-4]   { x c[i]; }
    //Step-2
    ccx c[n-1], c[n-4], c[n-5];
    for uint i in [3:n/2] { ccx c[n-2*i+1], c[n-2*i], c[n-2*i-1]; }
    //Step-3
    ccx anc, c[0], tar;
    //Step-4
    for uint i in [0:n/2-3] { ccx c[2*i+2], c[2*i+1], c[2*i]; }
    ccx c[8], c[5], c[4];
    for uint i in [0:n-4]   { x c[i]; }
    for uint i in [1:n/2-1] { ccx c[n-2*i], c[n-2*i-1], c[n-2*i-2]; }
    ccx c[0], c[1], anc;
}