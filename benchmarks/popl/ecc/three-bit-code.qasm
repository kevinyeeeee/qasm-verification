OPENQASM 3.0;

def pc(uint[3] b) -> uint[2] {
    uint[2] i = 0;
    if (b[0] == 1) { i += 1; }
    if (b[1] == 1) { i += 1; }
    if (b[2] == 1) { i += 1; }
    return i;
}

// also works with user defined pc in place of popcount
@pre e ~> b:bit[3], popcount(b) <= 1 , anc ~> |0,0> , q ~> |a:bit, a, a>
@post q ~> |a, a, a >
def err(qubit[3] q, qubit[2] anc, bit[3] e) {
    for int i in [0:2] {
        if (e[i] == 1) { x q[i]; }
    }

    cx q[0], anc[0];
    cx q[1], anc[0];
    cx q[1], anc[1];
    cx q[2], anc[1];

    uint[2] u = 0;
    u = measure anc;

    if (u == 1) { x q[0]; }
    if (u == 2) { x q[2]; }
    if (u == 3) { x q[1]; }
}
