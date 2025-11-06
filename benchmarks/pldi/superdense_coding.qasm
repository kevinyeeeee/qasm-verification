include "stdgates.inc";

@pre    bob          == |0>
@post   bob          == |alice>
def superdense_coding (bit[2] alice, qubit[2] bob) {
    //prepare bell state
    h bob[0];
    cx bob[0], bob[1];

    //encode
    if ( alice[0]==1 ){ z bob[0]; }
    if ( alice[1]==1 ){ x bob[0]; }

    //decode
    cx bob[0], bob[1];
    h bob[0];
}   