include "stdgates.inc";

@pre    q   == |0>,|0>
@post   q   == sum{x:uint[1]}.|x>,|x>
def bell_state_prep (qubit[2] q) {
    h q[0];
    cx q[0], q[1];
}