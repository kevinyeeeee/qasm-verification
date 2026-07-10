OPENQASM 3.0;

include "stdgates.inc";

// Two different sizes for the two implementations
const uint n = 3;        // For power-of-2 version (shor.qasm)
const uint nmod = 2;     // For modular arithmetic version (shorM.qasm)

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

// ============================================================================
// POWER-OF-2 VERSION (n=3)
// For moduli that are powers of 2
// ============================================================================

@pre  ctl ~> |c:bit>, A ~> |a:uint[n]>,    B ~> |b:uint[n]>
@post ctl ~> |c>,     A ~> |c*b + (~c)*a>, B ~> |c*a + (~c)*b>
def cSWAP(qubit ctl, qubit[n] A, qubit[n] B) {
  for uint i in [0:n-1] { ctrl @ swap ctl, A[i], B[i]; }
}

@pre  A ~> |a:uint[n]>, B ~> |b:uint[n]>
@post A ~> |b>,         B ~> |a>
def SWAP(qubit[n] A, qubit[n] B) {
  for uint i in [0:n-1] { swap A[i], B[i]; }
}

@pre a ~> |q:uint[n]>
@post a ~> sum{r:uint[n]}.exp(-2*q*r/(2^n))|r>
def iqft(qubit[n] a) {
    for int i in [0:(n/2)-1] {
      swap a[i], a[n-1-i];
    }
    for int i in [0:n-1] {
        h a[i];
        for int j in [i+1:n-1] {
            crz(-2*pi/(2**(j-i+1))) a[i], a[j];
        }
    }
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
@post  A ~> a,                       B ~> |b>,         C ~> |a*b>, X ~> |0>
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
@post  A ~> a,                       B ~> |b>,         C ~> |a*b>,     X ~> |0>
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
@post  A ~> a,                       B ~> |b>,         C ~> |0>,     X ~> |0>
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

def minv(uint[n] a)-> uint[n] {
  uint[n] ret = 1;
  for uint i in [1:2**n]{
    if ((a * i) % 2**n == 1){
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
@post  A ~> a,                       B ~> |b*a>,       C ~> |0>,   X ~> |0>
def inPlaceMult(uint[n] A, qubit[n] B, qubit[n] C, qubit X) {
  constOopMult(A, B, C, X);
  SWAP(B, C);
  constUnmult(minv(A), B, C, X);
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, ctl ~> |c:bit>, B ~> |b:uint[n]>,      C ~> |0>,D ~> |0>,   X ~> |0>
@post  A ~> a,                       ctl ~> |c>,     B ~> |c*b*a + (~c)*b>, C ~> |0>,D ~> |0>,   X ~> |0>
def cMult(qubit ctl, uint[n] A, qubit[n] B, qubit[n] C, qubit[n] D, qubit X) {
  x ctl;
  cSWAP(ctl, B, C);
  inPlaceMult(A, B, D, X);
  cSWAP(ctl, B, C);
  x ctl;
}

@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |0>,   ANC1 ~> |0>, ANC2 ~> |0>,  X ~> |0>
@post  A ~> a,                       B ~> |b>,         C ~> |a^b>, ANC1 ~> |0>, ANC2 ~> |0>,  X ~> |0>
def modExp(uint[n] A, qubit[n] B, qubit[n] C, qubit[n] ANC1, qubit[n] ANC2, qubit X) {
  uint[n] tmp = 1;
  tmp = A;
  x C[0];
  for int i in [0:n-1] {
    cMult(B[i], A, C, ANC1, ANC2, X);
    A = A * A;
  }
  A = tmp;
}

def order(uint[n] a) -> uint[n] {
  uint[n] current = 1;
  uint[n] ret = 0;
  uint[n] flag = 0;
  for uint i in [1:(2**n)-1] {
    current = (current * a) % 2**n;
    if (current == 1 && flag == 0) {
      ret = uint[n](i);
      flag = 1;
    }
  }
  return ret;
}

@pre  a ~> 3, ret ~> 0
@post ret ~> 2
def orderconst(uint[n] a, uint[n] ret) {
  uint[n] current = 1;
  uint[n] flag = 0;
  for uint i in [1:(2**n)-1] {
    current = (current * a) % 2**n;
    if (current == 1 && flag == 0) {
      ret = uint[n](i);
      flag = 1;
    }
  }
}

@pre  a ~> 3, ret ~> 0
@post ret ~> 2
def orderconst2(uint[n] a, uint[n] ret) {
  uint tmp = order(a);
  ret = tmp;
}

@pre  A ~> a:uint[n], a % 2 == 1, a != 1, ret ~> 1
@post ret ~> 1
def checkOrd(uint[n] A, uint[n] ret) {
  uint[n] tmp = 0;
  tmp = order(A);
  ret = 1;
  for uint i in [1:2**n] {
    if (uint[n](i) <= tmp) {
    	ret = ret * A;
    }
  }
}

@pre  A ~> a:uint[n], a % 2 == 1, a != 1, B ~> |order(a)>, C ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>
@post B ~> |order(a)>, C ~> |1>
def checkModExp(uint[n] A, qubit[n] B, qubit[n] C, qubit[n] ANC1, qubit[n] ANC2, qubit X) {
  modExp(A, B, C, ANC1, ANC2, X);
}

@pre  A ~> a:uint[n] { a % 2 == 1 }, B ~> |0>, C ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>
@post result ~> 0
def shora(uint[n] A, qubit[n] B, qubit[n] C, qubit[n] ANC1, qubit[n] ANC2, qubit X, uint[n] result) {
  h B;
  modExp(A, B, C, ANC1, ANC2, X);
  iqft(B);
  uint[n] cc = 0;
  cc = measure C;
  result = measure B;

  result = result % 2;
}

@pre  A ~> a:uint[n], a % 2 == 1, a != 1, B ~> |0>, C ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>
@post result ~> 0
def shorb(uint[n] A, qubit[n] B, qubit[n] C, qubit[n] ANC1, qubit[n] ANC2, qubit X, uint[n] result) {
  h B;
  modExp(A, B, C, ANC1, ANC2, X);
  iqft(B);
  uint[n] cc = 0;
  cc = measure C;
  result = measure B;

  result = result % order(A);
}

@pre  A ~> a:uint[n] { a % 2 == 1}, B ~> |0>, C ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>
@post (B,C) ~> sum{b:uint[n]}.sum{c:uint[n]}.exp(-2*b*c/(2^n))|c,a^b>
def shorc(uint[n] A, qubit[n] B, qubit[n] C, qubit[n] ANC1, qubit[n] ANC2, qubit X) {
  h B;
  modExp(A, B, C, ANC1, ANC2, X);
  iqft(B);
}

// ============================================================================
// MODULAR ARITHMETIC VERSION (nmod=2)
// For arbitrary moduli M > 1
// ============================================================================

@pre  ctl ~> |c:bit>, A ~> |a:uint[nmod]>,     B ~> |b:uint[nmod]>
@post ctl ~> |c>,     A ~> |c*b + (~c)*a>, B ~> |c*a + (~c)*b>
def cSWAPm(qubit ctl, qubit[nmod] A, qubit[nmod] B) {
  for uint i in [0:nmod-1] { ctrl @ swap ctl, A[i], B[i]; }
}

@pre  A ~> |a:uint[nmod]>, B ~> |b:uint[nmod]>
@post A ~> |b>,         B ~> |a>
def SWAPm(qubit[nmod] A, qubit[nmod] B) {
  for uint i in [0:nmod-1] { swap A[i], B[i]; }
}

@pre a ~> |q:uint[nmod]>
@post a ~> sum{r:uint[nmod]}.exp(-2*q*r/(2^nmod))|r>
def iqftm(qubit[nmod] a) {
    for int i in [0:(nmod/2)-1] {
      swap a[i], a[nmod-1-i];
    }
    for int i in [0:nmod-1] {
        h a[i];
        for int j in [i+1:nmod-1] {
            crz(-2*pi/(2**(j-i+1))) a[i], a[j];
        }
    }
}

@pre    A ~> |a:uint[nmod]>, (B,C) ~> |b:uint[nmod+1]>, X ~> |0>
@post   A ~> |a>        , (B,C) ~> |b+a>      , X ~> |0>
def cc(qubit[nmod] A, qubit[nmod] B, qubit C, qubit X) {
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:nmod-1] {
        maj A[i],B[i],A[i-1];
    }
    cx A[nmod-1], C;
    for uint t in [1:nmod-1] {           // Reverse UMA ripple
        uma A[nmod - t], B[nmod - t], A[nmod - t - 1];
    }
    uma A[0], B[0], X;
}

@pre    A ~> |a:uint[nmod]>, (B,C) ~> |b:uint[nmod+1]>, X ~> |0>
@post   A ~> |a>        , (B,C) ~> |b-a>      , X ~> |0>
def ccinv(qubit[nmod] A, qubit[nmod] B, qubit C, qubit X) {
    inv @ uma A[0], B[0], X;
    for uint t in [1:nmod-1] {           // Reverse UMA ripple
        inv @ uma A[t], B[t], A[t-1];
    }
    cx A[nmod-1], C;
    for uint i in [1:nmod-1] {
        inv @ maj A[nmod-i],B[nmod-i],A[nmod-i-1];
    }

    inv @ maj A[0], B[0], X;                // Forward MAJ ripple
}

@pre   ctl ~> |c:bit>, S ~> a:uint[nmod], (B,C) ~> |b:uint[nmod+1]>, X ~> |0>, A ~> |0>
@post  ctl ~> |c>,     S ~> a,         (B,C) ~> |b+c*a>      , X ~> |0>, A ~> |0>
def cadd(qubit ctl, uint[nmod] S, qubit[nmod] B, qubit C, qubit X, qubit[nmod] A) {
    for uint j in [0:nmod-1] {
      if (S[j] == 1) { cx ctl, A[j]; }
    }

    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:nmod-1] {
        maj A[i],B[i],A[i-1];
    }
    cx A[nmod-1], C;
    for uint t in [1:nmod-1] {           // Reverse UMA ripple
        uma A[nmod - t], B[nmod - t], A[nmod - t - 1];
    }
    uma A[0], B[0], X;

    for uint k in [0:nmod-1] {
      if (S[k] == 1) { cx ctl, A[k]; }
    }
}

@pre    ctl ~> |c:bit>, m ~> a:uint[nmod], (B, C) ~> |b:uint[nmod+1]>, X ~> |0>, A ~> |0>
@post   ctl ~> |c>,     m ~> a,         (B, C) ~> |b - c*a>    , X ~> |0>, A ~> |0>
def csub(qubit ctl, uint[nmod] m, qubit[nmod] B, qubit C, qubit X, qubit[nmod] A) {
    for uint i in [0:nmod-1] {
      if (m[i] == 1) { x A[i]; }
    }
    ccx ctl, A[0], B[0];
    maj A[0], B[0], X;
    for uint i in [1:nmod-1] {
      ccx ctl, A[i-1], B[i];
      ccx ctl, A[i], B[i];
      maj A[i], B[i], A[i-1];
    }
    ccx ctl, A[nmod-1], C;
    for uint t in [1:nmod-1] {           // Reverse UMA ripple
        inv @ maj A[nmod - t], B[nmod - t], A[nmod - t - 1];
    }
    inv @ maj A[0], B[0], X;
    for uint i in [0:nmod-1] {
      if (m[i] == 1) { x A[i]; }
    }
}

@pre    ctl ~> |c:bit>, m ~> a:uint[nmod], (B, C) ~> |b:uint[nmod+1]>, X ~> |0>, A ~> |0>
@post   ctl ~> |c>, m ~> a, (B, C) ~> |b>, X ~> |0>, A ~> |0>
def checkAddSub(qubit ctl, uint[nmod] m, qubit[nmod] B, qubit C, qubit X, qubit[nmod] A) {
  cadd(ctl,m,B,C,X,A);
  csub(ctl,m,B,C,X,A);
}

@pre    ctl ~> |c:bit>, m ~> a:uint[nmod], (B, C) ~> |b:uint[nmod+1]>, X ~> |0>, A ~> |0>
@post   ctl ~> |c>, m ~> a, (B, C) ~> |b>, X ~> |0>, A ~> |0>
def checkSubAdd(qubit ctl, uint[nmod] m, qubit[nmod] B, qubit C, qubit X, qubit[nmod] A) {
  csub(ctl,m,B,C,X,A);
  cadd(ctl,m,B,C,X,A);
}

@pre  m ~> a:uint[nmod], r ~> |b:uint[nmod]>, cmp ~> |c:bit>,        anc ~> |0>, anc2 ~> |0>
@post m ~> a,         r ~> |b>,         cmp ~> |c + (a <= b)>, anc ~> |0>, anc2 ~> |0>
def comparator_m(uint[nmod] m, qubit[nmod] r, qubit cmp, qubit anc, qubit[nmod] anc2) {

  for uint i in [0:nmod-1] {
    if (m[i] == 0) { x anc2[i]; }
  }
  // Reverse addition to compute high order bit
  x anc;
  maj anc2[0], r[0], anc;
  for uint i in [1:nmod-1] {
    maj anc2[i], r[i], anc2[i-1];
  }
  // Copy high-order bit
  cx anc2[nmod-1],cmp;
  // Uncompute
  for uint i in [1:nmod-1] {
    inv @ maj anc2[nmod-i], r[nmod-i], anc2[nmod-i-1];
  }
  inv @ maj anc2[0], r[0], anc;
  x anc;

  for uint i in [0:nmod-1] {
    if (m[i] == 0) { x anc2[i]; }
  }
}

@pre  q ~> |a:uint[nmod]>, r ~> |b:uint[nmod]>, cmp ~> |c:bit>,       anc ~> |0>
@post q ~> |a>,         r ~> |b>,         cmp ~> |c + (a < b)>, anc ~> |0>
def ncomparator(qubit[nmod] q, qubit[nmod] r, qubit cmp, qubit anc) {
  // Complement q
  for uint i in [0:nmod-1] {
    x q[i];
  }
  // Reverse addition to compute high order bit
  maj q[0], r[0], anc;
  for uint i in [1:nmod-1] {
    maj q[i], r[i], q[i-1];
  }
  // Copy high-order bit
  cx q[nmod-1],cmp;
  // Uncompute
  for uint i in [1:nmod-1] {
    inv @ maj q[nmod-i], r[nmod-i], q[nmod-i-1];
  }
  inv @ maj q[0], r[0], anc;
  for uint i in [0:nmod-1] {
    x q[i];
  }
}

@pre  m ~> M:uint[nmod]{M > 1}, q ~> |a:uint[nmod]{a < M}>, r ~> |b:uint[nmod]{b < M}>, anc ~> |0,0,0>, store ~> |0>
@post m ~> M,                q ~> |a>,                r ~> |(a+b) % M>,        anc ~> |0,0,0>, store ~> |0>
def addModM(uint[nmod] m, qubit[nmod] q, qubit[nmod] r, qubit[3] anc, qubit[nmod] store) {
  // Add, putting carry bit in anc[2]
  cc(q,r,anc[2],anc[0]);

  // Compare, anc[0] <- [M <= (a+b mod N)]
  comparator_m(m,r,anc[0],anc[1], store);

  // anc[0] <- (carry XOR [M <= (a+b mod N)]), note that carry=1 => a+b mod N < M
  // so anc[0] <- (carry OR [M <= (a+b mod N)])
  cx anc[2], anc[0];

  // Controlled subtraction
  csub(anc[0],m,r, anc[2],anc[1], store);

  // Clear the comparison bit
  ncomparator(r,q,anc[0],anc[1]);
}

@pre  m ~> M:uint[nmod]{M > 1}, q ~> |a:uint[nmod]{a < M}>, r ~> |b:uint[nmod]{b < M}>, anc ~> |0,0,0>, store ~> |0>
@post m ~> M,                q ~> |a>,                r ~> |(a-b) % M>,      anc ~> |0,0,0>, store ~> |0>
def subModM(uint[nmod] m, qubit[nmod] q, qubit[nmod] r, qubit[3] anc, qubit[nmod] store) {
  // Clear the comparison bit
  ncomparator(r,q,anc[0],anc[1]);

  // Controlled subtraction
  cadd(anc[0],m,r, anc[2],anc[1], store);

  // anc[0] <- (carry XOR [M <= (a+b mod N)]), note that carry=1 => a+b mod N < M
  // so anc[0] <- (carry OR [M <= (a+b mod N)])
  cx anc[2], anc[0];

  // Compare, anc[0] <- [M <= (a+b mod N)]
  comparator_m(m,r,anc[0],anc[1], store);

  // Add, putting carry bit in anc[2]
  ccinv(q,r,anc[2],anc[0]);
}

@pre  m ~> M:uint[nmod]{M > 1}, q ~> |a:uint[nmod]{a < M}>, r ~> |b:uint[nmod]{b < M}>, anc ~> |0,0,0>, store ~> |0>
@post  m ~> M, q ~> |a>, r ~> |b>, anc ~> |0,0,0>, store ~> |0>
def checkAddSubModM(uint[nmod] m, qubit[nmod] q, qubit[nmod] r, qubit[3] anc, qubit[nmod] store) {
  addModM(m, q, r, anc, store);
  subModM(m, q, r, anc, store);
}

@pre  m ~> M:uint[nmod]{M > 1}, r ~> |b:uint[nmod]{b < M}>, carry ~> |0>, cmp ~> |0>         , anc ~> |0>, store ~> |0>
@post m ~> M,                r ~> |(2*b) % M>,        carry ~> |0>, cmp ~> |(M <= 2*b)>, anc ~> |0>, store ~> |0>
def shift(uint[nmod] m, qubit[nmod] r, qubit carry, qubit cmp, qubit anc, qubit[nmod] store) {
  swap r[nmod-1], carry;
  for uint i in [1:nmod-1] {
    swap r[nmod-i], r[nmod-i-1];
  }
  comparator_m(m,r,cmp,anc, store);
  cx carry, cmp;
  csub(cmp,m,r, carry,anc, store);
}

def unshift(uint[nmod] m, qubit[nmod] r, qubit carry, qubit cmp, qubit anc, qubit[nmod] store) {
  cadd(cmp, m, r, carry, anc, store);
  cx carry, cmp;
  comparator_m(m,r,cmp,anc, store);
  for uint i in [1:nmod-1] {
    swap r[i], r[i-1];
  }
  swap r[nmod-1], carry;
}

@pre  m ~> M:uint[nmod]{M > 1}, r ~> |b:uint[nmod]{b < M}>, carry ~> |0>, cmp ~> |0>, anc ~> |0>, store ~> |0>
@post m ~> M,                r ~> |b>,                carry ~> |0>, cmp ~> |0>, anc ~> |0>, store ~> |0>
def checkUnshift(uint [nmod] m, qubit[nmod] r, qubit carry, qubit cmp, qubit anc, qubit[nmod] store) {
  shift(m, r, carry, cmp, anc, store);
  unshift(m, r, carry, cmp, anc, store);
}

def gcdm(uint[nmod] a, uint[nmod] b) -> uint[nmod] {
  uint[nmod] ret = 0;
  uint[nmod] flag = 0;
  uint[nmod] aa = 0;
  uint[nmod] bb = 0;
  aa = a;
  bb = b;
  for uint i in [0:3*nmod] {
    if (flag == 0) {
      if (aa > bb) { aa = aa % bb; } else { bb = bb % aa; }
      if (aa == 0) { ret = bb; flag = 1; }
      if (bb == 0) { ret = aa; flag = 1; }
    }
  }
  return ret;
}

def minvm(uint[nmod] M, uint[nmod] a)-> uint[nmod] {
  uint[nmod] ret = 1;
  for uint i in [1:2**nmod]{
    if (i < M && ((a * i) % M) == 1){
      ret = i;
    }
  }
  return ret;
}

@pre  M ~> m:uint[nmod], A ~> a:uint[nmod]{ (gcdm(a, m) == 1) && (a > 0) && (a < m) }, B ~> b:uint[nmod]
@post B ~> 1
def checkm(uint[nmod] M, uint[nmod] A, uint[nmod] B) {
  B = (A * minvm(M, A)) % M;
}

def orderm(uint[nmod] M, uint[nmod] a) -> uint[nmod] {
  uint[nmod] current = 1;
  uint[nmod] ret = 0;
  uint[nmod] flag = 0;
  for uint i in [1:(2**nmod)-1] {
    current = (current * a) % M;
    if (i < M && current == 1 && flag == 0) {
      ret = uint[nmod](i);
      flag = 1;
    }
  }
  return ret;
}

@pre  M ~> m:uint[nmod]{m > 1}, A ~> a:uint[nmod], gcdm(a, M) == 1, a > 1, ret ~> 1
@post ret ~> 1
def checkOrdm(uint[nmod] M, uint[nmod] A, uint[nmod] ret) {
  uint[nmod] tmp;
  tmp = orderm(M, A);
  ret = 1;
  for uint i in [1:2**nmod] {
    if (uint[nmod](i) <= tmp) {
    	ret = (ret * A) % M;
    }
  }
}

@pre  B ~> |b:uint[nmod] { b < 3 }>, C ~> |0>,         carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post B ~> |b>,                   C ~> |(2*b) % 3>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def constOopMultinfty(qubit[nmod] B, qubit[nmod] C, qubit carry, qubit[nmod] cmps, qubit[3] X, qubit[nmod] ANC) {
  uint[nmod] M = 3;
  uint[nmod] A;
  A = 2;

  for uint j in [0:nmod-1] {
    if (A[j] == 1) {
      addModM(M, B, C, X, ANC);
    }
    shift(M, B, carry, cmps[j], X[0], ANC);
  }

  for uint k in [1:nmod] {
    unshift(M, B, carry, cmps[nmod-k], X[0], ANC);
  }
}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod] { (gcdm(a, M) == 1) && (a < M) },  B ~> |b:uint[nmod] { b < M }>, C ~> |0>,         carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post M ~> m,                  A ~> a,                                          B ~> |b>,                   C ~> |(a*b) % M>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def constOopMultm(uint[nmod] M, uint[nmod] A, qubit[nmod] B, qubit[nmod] C, qubit carry, qubit[nmod] cmps, qubit[3] X, qubit[nmod] ANC) {
  for uint j in [0:nmod-1] {
    if (A[j] == 1) {
      addModM(M, B, C, X, ANC);
    }
    shift(M, B, carry, cmps[j], X[0], ANC);
  }

  for uint k in [1:nmod] {
    unshift(M, B, carry, cmps[nmod-k], X[0], ANC);
  }
}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod] { (gcdm(a, M) == 1) && (a < M) }, B ~> |b:uint[nmod] { b < M }>, C ~> |(a*b) % M>,         carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post M ~> m,                  A ~> a,                                         B ~> |b>,                   C ~> |0>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def constUnMultm(uint[nmod] M, uint[nmod] A, qubit[nmod] B, qubit[nmod] C, qubit carry, qubit[nmod] cmps, qubit[3] X, qubit[nmod] ANC) {
  for uint k in [1:nmod] {
    shift(M, B, carry, cmps[k-1], X[0], ANC);
  }

  for uint j in [0:nmod-1] {
    unshift(M, B, carry, cmps[nmod-1-j], X[0], ANC);
    if (A[nmod-1-j] == 1) {
      subModM(M, B, C, X, ANC);
    }
  }

}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod] { (gcdm(a, M) == 1) && (a < M) }, B ~> |b:uint[nmod] { b < M }>, C ~> |0>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post M ~> m, A ~> a, B ~> |(a*b) % M>, C ~> |0>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def inPlaceMultm(uint[nmod] M, uint[nmod] A, qubit[nmod] B, qubit[nmod] C, qubit carry, qubit[nmod] cmps, qubit[3] X, qubit[nmod] ANC) {
  constOopMultm(M, A, B, C, carry, cmps, X, ANC);
  SWAPm(B, C);
  constUnMultm(M, minvm(M, A), B, C, carry, cmps, X, ANC);
}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod]{ (gcdm(m, a) == 1) && (a < m) }, ctl ~> |c:bit>, B ~> |b:uint[nmod]>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
@post M ~> m, A ~> a, ctl ~> |c>, B ~> |c*((b*a) % m) + (~c)*b>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
def cMultm(uint[nmod] M, uint[nmod] A, qubit ctl, qubit[nmod] B, qubit[nmod] dummy, qubit[nmod] ANC1, qubit[nmod] ANC2, qubit[3] X, qubit carry, qubit[nmod] ANC3) {
  x ctl;
  cSWAPm(ctl, B, dummy);
  inPlaceMultm(M, A, B, ANC1, carry, ANC2, X, ANC3);
  cSWAPm(ctl, B, dummy);
  x ctl;
}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod]{ gcdm(m, a) == 1 }, B ~> |b:uint[nmod]>, C ~> |0>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
@post                                                            B ~> |b>, C ~> |(a^b) % m>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
def modExpm(uint[nmod] M, uint[nmod] A, qubit[nmod] B, qubit[nmod] C, qubit[nmod] dummy, qubit[nmod] ANC1, qubit[nmod] ANC2, qubit[3] X, qubit carry, qubit[nmod] ANC3) {
  x C[0];
  for int i in [0:nmod-1] {
    cMultm(M, A, B[i], C, dummy, ANC1, ANC2, X, carry, ANC3);
    A = (A * A) % M;
  }
}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod] { (gcdm(a, m) == 1) && (a < m)}, B ~> |0>, C ~> |0>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
@post (B,C) ~> sum{b:uint[nmod]}.sum{c:uint[nmod]}.exp(-2*b*c/(2^nmod))|c,(a^b) % m>
def shorm(uint[nmod] M, uint[nmod] A, qubit[nmod] B, qubit[nmod] C, qubit[nmod] dummy, qubit[nmod] ANC1, qubit[nmod] ANC2, qubit[3] X, qubit carry, qubit[nmod] ANC3) {
  h B;
  modExpm(M, A, B, C, dummy, ANC1, ANC2, X, carry, ANC3);
  iqftm(B);
}

@pre  M ~> m:uint[nmod]{ m > 1 }, A ~> a:uint[nmod] { (gcdm(a, m) == 1) && (a < m) && ((orderm(M,a) % M) == 0) && (a > 1)}, B ~> |0>, C ~> |0>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>, result ~> 0
@post result ~> 0
def checkShorm(uint[nmod] M, uint[nmod] A, qubit[nmod] B, qubit[nmod] C, qubit[nmod] dummy, qubit[nmod] ANC1, qubit[nmod] ANC2, qubit[3] X, qubit carry, qubit[nmod] ANC3, uint[nmod] result) {
  shorm(M,A,B,C,dummy,ANC1,ANC2,X,carry,ANC3);

  uint[nmod] res = 0;
  res = measure C;
  uint[nmod] tmp = 0;
  tmp = measure B;

  result = tmp;  // % orderm(M, A);
}
