const uint n = 2;

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

@pre  ctl ~> |c:bit>, A ~> |a:uint[n]>,     B ~> |b:uint[n]>
@post ctl ~> |c>,     A ~> |c*b + (~c)*a>, B ~> |c*a + (~c)*b>
def cSWAP(qubit ctl, qubit[n] A, qubit[n] B) {
  for uint i in [0:n-1] { ctrl @ swap ctl, A[i], B[i]; }
}

@pre    A ~> |a:uint[n]>, (B,C) ~> |b:uint[n+1]>, X ~> |0>
@post   A ~> |a>        , (B,C) ~> |b+a>      , X ~> |0>
def cc(qubit[n] A, qubit[n] B, qubit C, qubit X) {
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:n-1] {
        maj A[i],B[i],A[i-1];
    }
    cx A[n-1], C;
    for uint t in [1:n-1] {           // Reverse UMA ripple
        uma A[n - t], B[n - t], A[n - t - 1]; 
    }
    uma A[0], B[0], X;
}

@pre    A ~> |a:uint[n]>, (B,C) ~> |b:uint[n+1]>, X ~> |0>
@post   A ~> |a>        , (B,C) ~> |b-a>      , X ~> |0>
def ccinv(qubit[n] A, qubit[n] B, qubit C, qubit X) {
    inv @ uma A[0], B[0], X;
    for uint t in [1:n-1] {           // Reverse UMA ripple
        inv @ uma A[t], B[t], A[t-1]; 
    }
    cx A[n-1], C;
    for uint i in [1:n-1] {
        inv @ maj A[n-i],B[n-i],A[n-i-1];
    }

    inv @ maj A[0], B[0], X;                // Forward MAJ ripple
}

@pre   ctl ~> |c:bit>, S ~> a:uint[n], (B,C) ~> |b:uint[n+1]>, X ~> |0>, A ~> |0>
@post  ctl ~> |c>,     S ~> a,         (B,C) ~> |b+c*a>      , X ~> |0>, A ~> |0>
def cadd(qubit ctl, uint[n] S, qubit[n] B, qubit C, qubit X, qubit[n] A) {
    for uint j in [0:n-1] {
      if (S[j] == 1) { cx ctl, A[j]; }
    }
    
    maj A[0], B[0], X;                // Forward MAJ ripple
    for uint i in [1:n-1] {
        maj A[i],B[i],A[i-1];
    }
    cx A[n-1], C;
    for uint t in [1:n-1] {           // Reverse UMA ripple
        uma A[n - t], B[n - t], A[n - t - 1]; 
    }
    uma A[0], B[0], X;

    for uint k in [0:n-1] {
      if (S[k] == 1) { cx ctl, A[k]; }
    }
}

@pre    ctl ~> |c:bit>, m ~> a:uint[n], (B, C) ~> |b:uint[n+1]>, X ~> |0>, A ~> |0>
@post   ctl ~> |c>,     m ~> a,         (B, C) ~> |b - c*a>    , X ~> |0>, A ~> |0>
def csub(qubit ctl, uint[n] m, qubit[n] B, qubit C, qubit X, qubit[n] A) {
    for uint i in [0:n-1] {
      if (m[i] == 1) { x A[i]; }
    }
    ccx ctl, A[0], B[0];
    maj A[0], B[0], X;
    for uint i in [1:n-1] {
      ccx ctl, A[i-1], B[i];
      ccx ctl, A[i], B[i];
      maj A[i], B[i], A[i-1];
    }
    ccx ctl, A[n-1], C;
    for uint t in [1:n-1] {           // Reverse UMA ripple 
        inv @ maj A[n - t], B[n - t], A[n - t - 1];
    }
    inv @ maj A[0], B[0], X;
    for uint i in [0:n-1] {
      if (m[i] == 1) { x A[i]; }
    }
} 

@pre    ctl ~> |c:bit>, m ~> a:uint[n], (B, C) ~> |b:uint[n+1]>, X ~> |0>, A ~> |0>
@post   ctl ~> |c>, m ~> a, (B, C) ~> |b>, X ~> |0>, A ~> |0>
def checkAddSub(qubit ctl, uint[n] m, qubit[n] B, qubit C, qubit X, qubit[n] A) {
  cadd(ctl,m,B,C,X,A);
  csub(ctl,m,B,C,X,A);
}

@pre    ctl ~> |c:bit>, m ~> a:uint[n], (B, C) ~> |b:uint[n+1]>, X ~> |0>, A ~> |0>
@post   ctl ~> |c>, m ~> a, (B, C) ~> |b>, X ~> |0>, A ~> |0>
def checkSubAdd(qubit ctl, uint[n] m, qubit[n] B, qubit C, qubit X, qubit[n] A) {
  csub(ctl,m,B,C,X,A);
  cadd(ctl,m,B,C,X,A);
}

@pre  m ~> a:uint[n], r ~> |b:uint[n]>, cmp ~> |c:bit>,        anc ~> |0>, anc2 ~> |0>
@post m ~> a,         r ~> |b>,         cmp ~> |c + (a <= b)>, anc ~> |0>, anc2 ~> |0>
def comparator_m(uint[n] m, qubit[n] r, qubit cmp, qubit anc, qubit[n] anc2) {

  for uint i in [0:n-1] {
    if (m[i] == 0) { x anc2[i]; }
  } 
  // Reverse addition to compute high order bit
  x anc;
  maj anc2[0], r[0], anc;
  for uint i in [1:n-1] {
    maj anc2[i], r[i], anc2[i-1];
  }
  // Copy high-order bit
  cx anc2[n-1],cmp;
  // Uncompute
  for uint i in [1:n-1] {
    inv @ maj anc2[n-i], r[n-i], anc2[n-i-1];
  }
  inv @ maj anc2[0], r[0], anc;
  x anc;

  for uint i in [0:n-1] {
    if (m[i] == 0) { x anc2[i]; }
  } 
}

@pre  q ~> |a:uint[n]>, r ~> |b:uint[n]>, cmp ~> |c:bit>,       anc ~> |0>
@post q ~> |a>,         r ~> |b>,         cmp ~> |c + (a < b)>, anc ~> |0>
def ncomparator(qubit[n] q, qubit[n] r, qubit cmp, qubit anc) {
  // Complement q
  for uint i in [0:n-1] {
    x q[i];
  } 
  // Reverse addition to compute high order bit
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
  for uint i in [0:n-1] {
    x q[i];
  } 
}

@pre  m ~> M:uint[n]{M > 1}, q ~> |a:uint[n]{a < M}>, r ~> |b:uint[n]{b < M}>, anc ~> |0,0,0>, store ~> |0>
@post m ~> M,                q ~> |a>,                r ~> |(a+b) % M>,        anc ~> |0,0,0>, store ~> |0>
def addModM(uint[n] m, qubit[n] q, qubit[n] r, qubit[3] anc, qubit[n] store) {
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

//@pre  m ~> M:uint[n]{M > 1}, q ~> |a:uint[n]{a < M}>, r ~> |(a + (b:uint[n]{b < M})) % M>, anc ~> |0,0,0>, store ~> |0>
//@post m ~> M,                q ~> |a>,                r ~> |b>,      anc ~> |0,0,0>, store ~> |0>
@pre  m ~> M:uint[n]{M > 1}, q ~> |a:uint[n]{a < M}>, r ~> |b:uint[n]{b < M}>, anc ~> |0,0,0>, store ~> |0>
@post m ~> M,                q ~> |a>,                r ~> |(a-b) % M>,      anc ~> |0,0,0>, store ~> |0>
def subModM(uint[n] m, qubit[n] q, qubit[n] r, qubit[3] anc, qubit[n] store) {
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

@pre  m ~> M:uint[n]{M > 1}, q ~> |a:uint[n]{a < M}>, r ~> |b:uint[n]{b < M}>, anc ~> |0,0,0>, store ~> |0>
@post  m ~> M, q ~> |a>, r ~> |b>, anc ~> |0,0,0>, store ~> |0>
def checkAddSubModM(uint[n] m, qubit[n] q, qubit[n] r, qubit[3] anc, qubit[n] store) {
  addModM(m, q, r, anc, store);
  subModM(m, q, r, anc, store);
}

@pre  m ~> M:uint[n]{M > 1}, r ~> |b:uint[n]{b < M}>, carry ~> |0>, cmp ~> |0>         , anc ~> |0>, store ~> |0>
@post m ~> M,                r ~> |(2*b) % M>,        carry ~> |0>, cmp ~> |(M <= 2*b)>, anc ~> |0>, store ~> |0>
def shift(uint[n] m, qubit[n] r, qubit carry, qubit cmp, qubit anc, qubit[n] store) {
  swap r[n-1], carry;
  for uint i in [1:n-1] {
    swap r[n-i], r[n-i-1];
  }
  comparator_m(m,r,cmp,anc, store);
  cx carry, cmp;
  csub(cmp,m,r, carry,anc, store);
}

def unshift(uint[n] m, qubit[n] r, qubit carry, qubit cmp, qubit anc, qubit[n] store) {
  cadd(cmp, m, r, carry, anc, store);
  cx carry, cmp;
  comparator_m(m,r,cmp,anc, store);
  for uint i in [1:n-1] {
    swap r[i], r[i-1];
  }
  swap r[n-1], carry;
}

@pre  m ~> M:uint[n]{M > 1}, r ~> |b:uint[n]{b < M}>, carry ~> |0>, cmp ~> |0>, anc ~> |0>, store ~> |0>
@post m ~> M,                r ~> |b>,                carry ~> |0>, cmp ~> |0>, anc ~> |0>, store ~> |0>
def checkUnshift(uint [n] m, qubit[n] r, qubit carry, qubit cmp, qubit anc, qubit[n] store) {
  shift(m, r, carry, cmp, anc, store);
  unshift(m, r, carry, cmp, anc, store);
}

def gcd(uint[n] a, uint[n] b) -> uint[n] {
  uint[n] ret = 0;
  uint[n] flag = 0;
  uint[n] aa = 0;
  uint[n] bb = 0;
  aa = a;
  bb = b;
  for uint i in [0:3*n] {
    if (flag == 0) {
      if (aa > bb) { aa = aa % bb; } else { bb = bb % aa; }
      if (aa == 0) { ret = bb; flag = 1; }
      if (bb == 0) { ret = aa; flag = 1; }
    }
  }
  return ret;
}

def minv(uint[n] M, uint[n] a)-> uint[n] {
  uint[n] ret = 1;
  for uint i in [1:2**n]{      
    if (i < M && ((a * i) % M) == 1){
      ret = i;
    }
  }
  return ret;
}

@pre  M ~> m:uint[n], A ~> a:uint[n]{ (gcd(a, m) == 1) && (a > 0) && (a < m) }, B ~> b:uint[n]
@post B ~> 1
def check(uint[n] M, uint[n] A, uint[n] B) {
  B = (A * minv(M, A)) % M;
}

def order(uint[n] M, uint[n] a) -> uint[n] {
  uint[n] current = 1;
  uint[n] ret = 0;
  uint[n] flag = 0;
  for uint i in [1:(2**n)-1] {
    current = (current * a) % M;
    if (i < M && current == 1 && flag == 0) {
      ret = uint[n](i);
      flag = 1;
    }
  }
  return ret;
}

@pre  M ~> m:uint[n]{m > 1}, A ~> a:uint[n], gcd(a, M) == 1, a > 1, ret ~> 1
@post ret ~> 1
def checkOrd(uint[n] M, uint[n] A, uint[n] ret) {
  uint[n] tmp;
  tmp = order(M, A);
  ret = 1;
  for uint i in [1:2**n] {
    if (uint[n](i) <= tmp) {
    	ret = (ret * A) % M;
    }
  }
}

@pre  B ~> |b:uint[n] { b < 3 }>, C ~> |0>,         carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post B ~> |b>,                   C ~> |(2*b) % 3>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def constOopMultinfty(qubit[n] B, qubit[n] C, qubit carry, qubit[n] cmps, qubit[3] X, qubit[n] ANC) {
  uint[n] M = 3;
  uint[n] A;
  A = 2;

  for uint j in [0:n-1] {
    if (A[j] == 1) {
      addModM(M, B, C, X, ANC);
    }
    shift(M, B, carry, cmps[j], X[0], ANC);
  }

  for uint k in [1:n] {
    unshift(M, B, carry, cmps[n-k], X[0], ANC);
  }
}

@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n] { (gcd(a, M) == 1) && (a < M) },  B ~> |b:uint[n] { b < M }>, C ~> |0>,         carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post M ~> m,                  A ~> a,                                          B ~> |b>,                   C ~> |(a*b) % M>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def constOopMult(uint[n] M, uint[n] A, qubit[n] B, qubit[n] C, qubit carry, qubit[n] cmps, qubit[3] X, qubit[n] ANC) {
  for uint j in [0:n-1] {
    if (A[j] == 1) {
      addModM(M, B, C, X, ANC);
    }
    shift(M, B, carry, cmps[j], X[0], ANC);
  }

  for uint k in [1:n] {
    unshift(M, B, carry, cmps[n-k], X[0], ANC);
  }
}

@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n] { (gcd(a, M) == 1) && (a < M) }, B ~> |b:uint[n] { b < M }>, C ~> |(a*b) % M>,         carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post M ~> m,                  A ~> a,                                         B ~> |b>,                   C ~> |0>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def constUnMult(uint[n] M, uint[n] A, qubit[n] B, qubit[n] C, qubit carry, qubit[n] cmps, qubit[3] X, qubit[n] ANC) {
  for uint k in [1:n] {
    shift(M, B, carry, cmps[k-1], X[0], ANC);
  }

  for uint j in [0:n-1] {
    unshift(M, B, carry, cmps[n-1-j], X[0], ANC);
    if (A[n-1-j] == 1) {
      subModM(M, B, C, X, ANC);
    }
  }

}

@pre  A ~> |a:uint[n]>, B ~> |b:uint[n]>
@post A ~> |b>,         B ~> |a>
def SWAP(qubit[n] A, qubit[n] B) {
  for uint i in [0:n-1] { swap A[i], B[i]; }
}

//@pre   A ~> a:uint[n]{ a % 2 == 1 }, B ~> |b:uint[n]>, C ~> |0>,   X ~> |0>
//@post                                B ~> |b*a>,       C ~> |0>,   X ~> |0>
@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n] { (gcd(a, M) == 1) && (a < M) }, B ~> |b:uint[n] { b < M }>, C ~> |0>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
@post M ~> m, A ~> a, B ~> |(a*b) % M>, C ~> |0>, carry ~> |0>, cmps ~> |0>, X ~> |0>, ANC ~> |0>
def inPlaceMult(uint[n] M, uint[n] A, qubit[n] B, qubit[n] C, qubit carry, qubit[n] cmps, qubit[3] X, qubit[n] ANC) {
  constOopMult(M, A, B, C, carry, cmps, X, ANC);
  SWAP(B, C);
  constUnMult(M, minv(M, A), B, C, carry, cmps, X, ANC);
}

@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n]{ (gcd(m, a) == 1) && (a < m) }, ctl ~> |c:bit>, B ~> |b:uint[n]>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
@post M ~> m, A ~> a, ctl ~> |c>, B ~> |c*((b*a) % m) + (~c)*b>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
def cMult(uint[n] M, uint[n] A, qubit ctl, qubit[n] B, qubit[n] dummy, qubit[n] ANC1, qubit[n] ANC2, qubit[3] X, qubit carry, qubit[n] ANC3) {
  x ctl;
  cSWAP(ctl, B, dummy);
  inPlaceMult(M, A, B, ANC1, carry, ANC2, X, ANC3);
  cSWAP(ctl, B, dummy);
  x ctl;
}

@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n]{ gcd(m, a) == 1 }, B ~> |b:uint[n]>, C ~> |0>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
@post                                                            B ~> |b>, C ~> |(a^b) % m>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
def modExp(uint[n] M, uint[n] A, qubit[n] B, qubit[n] C, qubit[n] dummy, qubit[n] ANC1, qubit[n] ANC2, qubit[3] X, qubit carry, qubit[n] ANC3) {
  x C[0];
  for int i in [0:n-1] {
    cMult(M, A, B[i], C, dummy, ANC1, ANC2, X, carry, ANC3);
    A = (A * A) % M;
  }
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

@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n] { (gcd(a, m) == 1) && (a < m)}, B ~> |0>, C ~> |0>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>
@post (B,C) ~> sum{b:uint[n]}.sum{c:uint[n]}.exp(-2*b*c/(2^n))|c,(a^b) % m>
def shor(uint[n] M, uint[n] A, qubit[n] B, qubit[n] C, qubit[n] dummy, qubit[n] ANC1, qubit[n] ANC2, qubit[3] X, qubit carry, qubit[n] ANC3) {
  h B;
  modExp(M, A, B, C, dummy, ANC1, ANC2, X, carry, ANC3);
  iqft(B);
}

@pre  M ~> m:uint[n]{ m > 1 }, A ~> a:uint[n] { (gcd(a, m) == 1) && (a < m) && ((order(m,a) % 2^n) == 0) && (a > 1)}, B ~> |0>, C ~> |0>, dummy ~> |0>, ANC1 ~> |0>, ANC2 ~> |0>, X ~> |0>, carry ~> |0>, ANC3 ~> |0>, result ~> 0
@post result ~> 0
def checkShor(uint[n] M, uint[n] A, qubit[n] B, qubit[n] C, qubit[n] dummy, qubit[n] ANC1, qubit[n] ANC2, qubit[3] X, qubit carry, qubit[n] ANC3, uint[n] result) {
  shor(M,A,B,C,dummy,ANC1,ANC2,X,carry,ANC3);

  uint[n] res = 0;
  res = measure C;
  uint[n] tmp = 0;
  tmp = measure B;

  result = tmp % (2**n / order(M, A));
}
