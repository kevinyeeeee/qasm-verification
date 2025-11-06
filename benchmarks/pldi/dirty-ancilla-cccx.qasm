include "stdgates.inc";

@pre    c   == |x:uint[3]>
    &&  t   == |y>
    &&  anc == |z>
@post   c   == |x>
    &&  t   == |y+x[0]*x[1]*x[2]>
    &&  anc == |z>
def dirty_ancilla_cccx (qubit[3] c, qubit t, qubit anc) {
    ccx c[0], c[1], anc;
    ccx anc, c[2], t;
    ccx c[0], c[1], anc;
    ccx anc, c[2], t;
}