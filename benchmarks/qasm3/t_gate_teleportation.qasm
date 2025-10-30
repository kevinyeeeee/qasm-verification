include "stdgates.inc";

@pre    t_state            == |0>
        data               == |ψ>
@post   t_state            == |0>
        data               == exp(pi/4)|ψ>
def t_gate_teleportation (qubit t_state, qubit data) {
    //prepare T-state
    h t_state;
    t t_state;

    //entangle
    cx data, t_state;

    //conditional S correction on data
    bit m = measure t_state;
    if ( m == 1 ){
        x t_state;
        s data;
    }
}   