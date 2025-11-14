OPENQASM 3.0;
include "stdgates.inc";
const uint n = 4; 
def majority(bool a, bool b, bool c) -> bool { 
  return (a&&b) ^ (a&&c) ^ (b&&c);
}

@pre  q ~>  |a:bit>     , r ~>  |b:bit>, s ~>  |c:bit>
@post q ~>  |majority(a,b,c)>, r ~>  |a + b>, s ~>  |a + c>
gate maj q, r, s {                 
  cx q, r;
  cx q, s; 
  ccx s, r, q;    
}

//@pre    q ~>  |majority(a,b,c)>, r ~>  |a+b>, s ~>  |a+c>
//@post   q ~>  |a>, r ~>  |a+b+c>, s ~>  |c>
gate uma q, r, s {      
  ccx s, r, q;
  cx q, s;      
  cx s, r;
}

@pre    ctl ~> |c:bit>, A ~> |a:uint[n]>, B ~> |b:uint[n]>, X ~> |0>
@post   ctl ~> |c>,     A ~> |a>        , B ~> |b - c*a>, X ~> |0>
def ctrlInvCuccaro(qubit ctl, qubit[n] A, qubit[n] B, qubit X) {
    ccx ctl, A[0], B[0];
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:n-2] {
        ccx ctl, A[i-1], B[i];
        ccx ctl, A[i], B[i];
        maj A[i],B[i],A[i-1];
    }
    ccx ctl, A[n-2], B[n-1];
    ccx ctl, A[n-1], B[n-1];
    for uint t in [2:n-1] {           // Reverse UMA ripple
        uint i = n - t;
        inv @ maj A[i], B[i], A[i-1]; 
    }
    inv @ maj A[0], B[0], X;
}


@pre  q ~> |a:uint[n]>, r ~> |b:uint[n]>, cmp ~> |c:bit>,        anc ~> |0>
@post q ~> |a>,         r ~> |b>,         cmp ~> |c + (a <= b)>, anc ~> |0>
def comparator(qubit[n] q, qubit[n] r, qubit cmp, qubit anc) {
  // Complement q
  for uint i in [0:n-1] {
    x q[i];
  } 
  // Reverse addition to compute high order bit
  x anc;
  maj q[0], r[0], anc;
  for uint i in [1:n-1] {
    maj q[i], r[i], q[i-1];
  }
  // Copy high-order bit
  cx q[n-1],cmp;
  // Uncompute
  for uint i in [1:n-1] {
    inv @ maj q[n-i], r[n-i], q[n-i-1];
  }
  inv @ maj q[0], r[0], anc;
  x anc;
  for uint i in [0:n-1] {
    x q[i];
  } 
}

// Failing, kills processor
@pre  m ~> |M:uint[n]{M > 1}>, q ~> |a:uint[n]{a < 2*M}>, cnd ~> |0>,       anc ~> |0>
@post m ~> |M>,                q ~> |a % M>,              cnd ~> |(a >= M)>, anc ~> |0>
def modRed(qubit[n] q, qubit[n] m, qubit cnd, qubit anc) {
  // Compare
  comparator(m,q,cnd,anc);

  // Controlled subtraction
  ctrlInvCuccaro(cnd,m,q,anc);
}
