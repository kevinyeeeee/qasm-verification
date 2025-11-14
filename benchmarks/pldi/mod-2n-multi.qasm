OPENQASM 3.0;

include "stdgates.inc";

const uint n = 4;

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

def carry(uint[n] a, uint[n] b)-> bit{
  return a+b < a;
}

                                      // a,b are typed as uint so + is the sum rather than XOR
@pre    A ~>  |a:uint[n]> , (B,Z) ~>  |b:uint[n+1]> , X ~>  |0>
@post   A ~>  |a>         , (B,Z) ~>  |b+a>         , X ~>  |0>
def cuccaro(qubit[n] A, qubit[n] B, qubit X, qubit Z) {
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

@pre   A ~> |a:uint[n]>, B ~> |b:uint[n]>, C ~> |0>,   X ~> |0>
@post  A ~> |a>,         B ~> |b>,         C ~> |a*b>, X ~> |0>
def oopMult(qubit[n] A, qubit[n] B, qubit[n] C, qubit X) {
  for uint j in [0:n-2] {
    // controlled add (B[j], A[0:n-j-1], C[j:n-1])
    uint m = n - j;

    maj A[0], C[j], X;                
    for uint i in [1:m-2] {
      maj A[i],C[i+j],A[i-1];
    }
    ccx B[j], A[m-2], C[n-1];
    ccx B[j], A[m-1], C[n-1];
    for uint t in [2:m-1] {           
      uint i = m - t; 
      inv @ maj A[i], C[i+j], A[i-1]; 
      ccx B[j], A[i-1], C[i+j];
      ccx B[j], A[i], C[i+j];
    }
    inv @ maj A[0], C[j], X; 
    ccx B[j], A[0], C[j];
  }

  ccx B[n-1], A[0], C[n-1];
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |0>,   X ~> |0>
@post                                B ~> |b>,         C ~> |a*b>, X ~> |0>
def constOopMult(uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  for uint j in [0:n-2] {
    uint m = n - j;
    if (A[j] == 1) {
      maj B[0], C[j], X;                // Forward MAJ ripple
      for uint i in [1:m-2] {
        maj B[i],C[i+j],B[i-1];
      }
      cx B[m-2], C[n-1];
      cx B[m-1], C[n-1];
      for uint t in [2:m-1] {           // Reverse UMA ripple
        uma B[m-t], C[m-t+j], B[m-t-1]; 
      }
      uma B[0], C[j], X;
    }
  }
  if (A[n-1] == 1) {cx B[0], C[n-1];}
}

// unworking 
//@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |a*b>,   X ~> |0>
//@post                                B ~> |b>,         C ~> |0>,     X ~> |0>
def unConstOopMult(uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  if (A[n-1] == 1) {cx B[0], C[n-1];}
  for uint k in [0:n-2] {
    uint j = n-2-k;
    uint m = n - j;
    if (A[j] == 1) {
      inv @ uma B[0], C[j], X;
      for uint t in [2:m-1] {
        inv @ uma B[t-1], C[t+j-1], B[t-2]; 
      }
      cx B[m-1], C[n-1];
      cx B[m-2], C[n-1];
      for uint i in [1:m-2] {
        inv @ maj B[m-1-i],C[m-1-i+j],B[m-2-i];
      }
      inv @ maj B[0], C[j], X; 
    }
  }
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |0>,   X ~> |0>
@post                                B ~> |b>,         C ~> |a*b>,     X ~> |0>
def ccmult(uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  for uint j in [0:n-2] {
    uint m = n - j;
    maj B[0], C[j], X;                // Forward MAJ ripple
    for uint i in [1:m-2] {
        maj B[i],C[i+j],B[i-1];
    }
    if (A[j] == 1) {
      cx B[m-2], C[n-1];
      cx B[m-1], C[n-1];
    }
    for uint t in [2:m-1] {           // Reverse UMA ripple
        uint i = m - t; 
        inv @ maj B[i], C[i+j], B[i-1]; 
        if (A[j] == 1) {
          cx B[i-1], C[i+j];
          cx B[i], C[i+j];
        }
    }
    inv @ maj B[0], C[j], X; 
    if (A[j] == 1) {cx B[0], C[j];}
  }
  if (A[n-1] == 1) {cx B[0], C[n-1]; }
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |a*b>,   X ~> |0>
@post                                B ~> |b>,         C ~> |0>,     X ~> |0>
def constUnmult(uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  if (A[n-1] == 1) {cx B[0], C[n-1]; }
  for uint k in [0:n-2] {
    uint j = n-2-k;
    uint m = n - j;
    if (A[j] == 1) {cx B[0], C[j];}
    maj B[0], C[j], X; 
    for uint i in [1:m-2] {         
        if (A[j] == 1) {
          cx B[i-1], C[i+j];
          cx B[i], C[i+j];
        }
        maj B[i], C[i+j], B[i-1]; 
    }
    if (A[j] == 1) {
      cx B[m-2], C[n-1];
      cx B[m-1], C[n-1];
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

def minv(uint[n] a)-> uint[n] {
  uint[n] ret = 1;
  for uint i in [1:2**n]{      
    if (a * i ==  1){
      ret = i;
    }
  }
  return ret;
}

@pre  A ~> a:uint[n], B ~> b:uint[n], a % 2 == 1
@post B ~> 1
def check(uint[n] A, uint[n] B) {
  B = A * minv(A);
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |0>,   X ~> |0>
@post                                B ~> |b*a>,       C ~> |0>,   X ~> |0>
def inPlaceMult(uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  constOopMult(A, B, C, X);
  SWAP(B, C);
  constUnmult(minv(A), B, C, X);
}

