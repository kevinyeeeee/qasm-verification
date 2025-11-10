include "stdgates.inc";

@pre    msg             == |psi> & (alice, bob)    == sum{j}. (|j>,|j>)
@post   bob             == |psi>
def teleportation (qubit msg, qubit alice, qubit bob) {
    // msg    = qubit carrying the unknown state |ψ⟩ to be teleported
    // alice  = Alice's half of the Bell pair (entangled with bob)
    // bob    = Bob's half of the Bell pair (the receiver)
    cx msg, alice;
    h msg;
    bit m0 = measure msg;
    bit m1 = measure alice;
    if (m1 == 1){ x bob; }
    if (m0 == 1){ z bob; }
}