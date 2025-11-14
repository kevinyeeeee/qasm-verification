const uint n = 10;

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

@pre    A ~> |a:uint[n]>, B ~> |b:uint[n]>, X ~> |0>
@post   A ~> |a>        , B ~> |a+b>      , X ~> |0>
def cuccaro(qubit[n] A, qubit[n] B, qubit X) {
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:n-2] {
        maj A[i],B[i],A[i-1];
    }
    cx A[n-2], B[n-1];
    cx A[n-1], B[n-1];
    for uint t in [2:n-1] {           // Reverse UMA ripple
        uint i = n - t; 
        uma A[i], B[i], A[i-1]; 
    }
    uma A[0], B[0], X;
}

@pre    ctl ~> |c:bit>, A ~> |a:uint[n]>, B ~> |b:uint[n]>, X ~> |0>
@post   ctl ~> |c>,     A ~> |a>,         B ~> |b + c*a>, X ~> |0>
def cCuccaro(qubit ctl, qubit[n] A, qubit[n] B, qubit X) {
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:n-2] {
        maj A[i],B[i],A[i-1];
    }
    ccx ctl, A[n-2], B[n-1];
    ccx ctl, A[n-1], B[n-1];
    for uint t in [2:n-1] {           // Reverse UMA ripple
        uint i = n - t; 
        inv @ maj A[i], B[i], A[i-1]; 
        ccx ctl, A[i-1], B[i];
        ccx ctl, A[i], B[i];
    }
    inv @ maj A[0], B[0], X; 
    ccx ctl, A[0], B[0];
}

@pre    A ~>  |a:uint[n]> , (B,Z) ~>  |b:uint[n+1]> , X ~>  |0>
@post   A ~>  |a>         , (B,Z) ~>  |b+a>         , X ~>  |0>
def cuccaro_carry(qubit[n] A, qubit[n] B, qubit X, qubit Z) {
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:n-1] {
        maj A[i],B[i],A[i-1];
    }
    cx A[n-1], Z;                     // Copy final carry s_n to Z
    for uint t in [1:n-1] {           // Reverse UMA ripple
        uint i = n - t; 
        uma A[i], B[i], A[i-1]; 
    }
    uma A[0], B[0], X;
}
