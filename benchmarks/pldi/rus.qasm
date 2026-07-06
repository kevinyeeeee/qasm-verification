/*
 * Repeat-until-success circuit for Rz(theta),
 * cos(theta-pi)=3/5, from Nielsen and Chuang, Chapter 4.
 */
//include "stdgates.inc";

@pre psi ~> |a:bit>, anc ~> |0,0>
@post psi ~> |a>, anc ~> |0,0>
def rus(qubit psi, qubit[2] anc) {
  uint[2] flags;
  flags = 3;

  @assert psi ~> sum{b:bit,c:bit}.exp(b*c/2 + a*b*c + b*flags[0] + c*flags[1] + 3*a/2)|a>, anc ~> |0,0>
  while(flags != 0) {
    h anc[0];
    h anc[1];
    ccx anc[0], anc[1], psi;
    s psi;
    ccx anc[0], anc[1], psi;
    z psi;
    h anc[0];
    h anc[1];
    //t anc[0];
    //t anc[1];
    //cz anc[0],anc[1];
    //ct anc[0],anc[1];
    measure anc[0] -> flags[0];
    measure anc[1] -> flags[1];
    reset anc;
  }
}

