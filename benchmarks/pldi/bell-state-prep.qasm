include "stdgates.inc";
@pre c == |0>,|0>
@post c == sum{q}.(|q>,|q>)
def bell_state_prep (qubit[2] c) {
    h c[0];
    cx c[0], c[1];
}