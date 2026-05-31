OPENQASM 3.0;

include "stdgates.inc";

const uint n = 3;                   

@pre    a ~>  |qa:bit>            , b ~>  |qb:bit>, c ~>  |qc:bit>
@post   a ~>  |qa*qb+qa*qc+qb*qc> , b ~>  |qa+qb> , c ~>  |qa+qc>
gate maj a, b, c {                  // In-place majority
  cx a, b;
  cx a, c; 
  ccx c, b, a;                      // a=|x+(x+y)*(x+z)>
}

//@pre    a ~>  |qa*qb+qa*qc+qb*qc> , b ~>  |qa+qb> , c ~>  |qa+qc>
//@post   a ~>  |qa>                , b ~>  |qb>    , c ~>  |qc>
gate unmaj a, b, c {                // Inverse of MAJ
  ccx c, b, a;   
  cx  a, c;
  cx  a, b;
}

//@pre    a ~>  |qa*qb+qa*qc+qb*qc> , b ~>  |qa+qb>     , c ~>  |qa+qc>
//@post   a ~>  |qa>                , b ~>  |qa+qb+qc>  , c ~>  |qc>
gate uma a, b, c{                   // Unmajority and add (2-CNOT form)
  ccx c, b, a;
  cx a, c;      
  cx c, b;
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, ctl ~> |c:bit>, B ~> |b:uint[n]>, C ~> |0>,   X ~> |0>
@post                                ctl ~> |c>    , B ~> |b>,         C ~> |c*a*b>, X ~> |0>
def contMult(qubit ctl, uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  for uint j in [0:n-2] {
    uint m = n - j;
    maj B[0], C[j], X;                // Forward MAJ ripple
    for uint i in [1:m-2] {
        maj B[i],C[i+j],B[i-1];
    }
    if (A[j] == 1) {
      ccx ctl, B[m-2], C[n-1];
      ccx ctl, B[m-1], C[n-1];
    }
    for uint t in [2:m-1] {           // Reverse UMA ripple
        uint i = m - t; 
        inv @ maj B[i], C[i+j], B[i-1]; 
        if (A[j] == 1) {
          ccx ctl, B[i-1], C[i+j];
          ccx ctl, B[i], C[i+j];
        }
    }
    inv @ maj B[0], C[j], X; 
    if (A[j] == 1) {ccx ctl, B[0], C[j];}
  }
  if (A[n-1] == 1) {ccx ctl, B[0], C[n-1]; }
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, ctl ~> |c:bit>, B ~> |b:uint[n]>, C ~> |a*b>,   X ~> |0>
@post                                ctl ~> |c>    , B ~> |b>,         C ~> |(~c)*a*b>,     X ~> |0>
def contUnmult(qubit ctl, uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  if (A[n-1] == 1) {ccx ctl, B[0], C[n-1]; }
  for uint k in [0:n-2] {
    uint j = n-2-k;
    uint m = n - j;
    if (A[j] == 1) {ccx ctl, B[0], C[j];}
    maj B[0], C[j], X; 
    for uint i in [1:m-2] {         
        if (A[j] == 1) {
          ccx ctl, B[i-1], C[i+j];
          ccx ctl, B[i], C[i+j];
        }
        maj B[i], C[i+j], B[i-1]; 
    }
    if (A[j] == 1) {
      ccx ctl, B[m-2], C[n-1];
      ccx ctl, B[m-1], C[n-1];
    }
    for uint i in [1:m-2] {
        uint f = m-1-i;
        inv @ maj B[f],C[f+j],B[f-1];
    }
    inv @ maj B[0], C[j], X;    
  }
}

@pre  A ~> |a:uint[n]>, B ~> |b:uint[n]>
@post A ~> |b>,         B ~> |a>
def SWAP(qubit[n] A, qubit[n] B) {
  for uint i in [0:n-1] { swap A[i], B[i]; }
}

@pre  ctl ~> |c:bit>, A ~> |a:uint[n]>,     B ~> |b:uint[n]>
@post ctl ~> |c>,     A ~> |c*b + (~c)*a>, B ~> |c*a + (~c)*b>
def cSWAP(qubit ctl, qubit[n] A, qubit[n] B) {
  for uint i in [0:n-1] { ctrl @ swap ctl, A[i], B[i]; }
}

def minv(uint[n] a)-> uint[n] {
  uint[n] ret = 1;
  bool flag = false;
  for uint i in [1:2**n]{      
    if (((a * i) % 2**n) == 1 && flag == false){
      ret = i;
      flag == true;
    }
  }
  return ret;
}

@pre  A ~> a:uint[n], B ~> b:uint[n], a % 2 == 1
@post B ~> 1
def check(uint[n] A, uint[n] B) {
  B = A * minv(A);
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, ctl ~> |c:bit>, B ~> |b:uint[n]>,    C ~> |0>,   X ~> |0>
@post                                ctl ~> |c>    , B ~> |c*b*a+(~c)*b>, C ~> |0>,   X ~> |0>
def cMult(qubit ctl, uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  contMult(ctl,A, B, C, X);
  cSWAP(ctl,B, C);
  contUnmult(ctl,minv(A), B, C, X);
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |0>,     ANC ~> |0>, X ~> |0>
@post                                B ~> |b>,         C ~> |a ^ b>, ANC ~> |0>, X ~> |0>
def modExp(uint[n] A, qubit[n] B, qubit[n] C, qubit[n] ANC, qubit X) {
  x C[0];
  for int i in [0:n-1] {
    cMult(B[i], A, C, ANC);
    A = A * A;
  }
}
