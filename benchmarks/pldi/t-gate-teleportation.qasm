include "stdgates.inc";

@pre    tstate            ~> |0> , data               ~> |psi:int[1]>
@post   tstate            ~> |0> , data               ~> exp(psi/4)|psi>
def t_gate_teleportation (qubit tstate, qubit data) {
    //prepare T-state
    h tstate;
    t tstate;

    //entangle
    cx data, tstate;

    //conditional S correction on data
    bit m = measure tstate;
    if ( m == 1 ){
        x tstate;
        s data;
    }
}   

