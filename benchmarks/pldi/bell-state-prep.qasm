include "stdgates.inc";

@pre    q   == |0:uint[2]>
@post   q   == 1/sqrt(2) * sum{x}|x,x>
def bell_state_prep (qubit[2] q) {
    h q[0];
    cx q[0], q[1];
}