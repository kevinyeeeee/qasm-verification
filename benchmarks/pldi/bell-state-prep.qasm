include "stdgates.inc";

@pre c == |0>,|0>
@post c == sum{q}.(|q>,|q>)
def bell_state_prep (qubit[2] q) {
    h q[0];
    cx q[0], q[1];
}gi