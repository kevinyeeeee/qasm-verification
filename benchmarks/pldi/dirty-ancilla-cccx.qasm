include "stdgates.inc";

@pre    c   == |cval>              &&  t   == |tval>                            &&  anc == |ancval>
@post   c   == |cval>              &&  t   == |tval+cval[0]*cval[1]*cval[2]>    &&  anc == |ancval>
def dirty_ancilla_cccx (qubit[3] c, qubit t, qubit anc) {
    ccx c[0], c[1], anc;
    ccx anc, c[2], t;
    ccx c[0], c[1], anc;
    ccx anc, c[2], t;
}