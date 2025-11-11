OPENQASM 3.0;

include "stdgates.inc";

const uint n = 4;                   // ceil(log2(10)) = 4
const uint N = 10;                  // Select a,N coprime.
const uint[n] a = 3;
const uint csize = 6;               // The size of the control register determines the accuracy of the rational approximation.

                                    // Variables inside ket are bit-variables by default, so + is XOR and * is AND.
@pre    a ~>  |qa:bit>            , b ~>  |qb:bit>, c ~>  |qc:bit>
@post   a ~>  |qa*qb+qa*qc+qb*qc> , b ~>  |qa+qb> , c ~>  |qa+qc>
gate maj a, b, c {                  // In-place majority
  cx a, b;
  cx a, c; 
  ccx c, b, a;                      // a=|x+(x+y)*(x+z)>
}

@pre    a ~>  |qa*qb+qa*qc+qb*qc> , b ~>  |qa+qb> , c ~>  |qa+qc>
@post   a ~>  |qa>                , b ~>  |qb>    , c ~>  |qc>
gate unmaj a, b, c {                // Inverse of MAJ
  ccx c, b, a;   
  cx  a, c;
  cx  a, b;
}

@pre    a ~>  |qa*qb+qa*qc+qb*qc> , b ~>  |qa+qb>     , c ~>  |qa+qc>
@post   a ~>  |qa>                , b ~>  |qa+qb+qc>  , c ~>  |qc>
gate uma a, b, c{                   // Unmajority and add (2-CNOT form)
  ccx c, b, a;
  cx a, c;      
  cx c, b;
}

def carry(uint[n] a, uint[n] b)-> bit{
  return int(a)+int(b) >= (1<<n);
}

                                      // a,b are typed as uint so + is the sum rather than XOR
@pre    A ~>  |a:uint[n]> , B ~>  |b:uint[n]>  , Z ~>  |z:bit>        , X ~>  |0>
@post   A ~>  |a>         , B ~>  |a+b>        , Z ~>  |z+carry(a,b)> , X ~>  |0>
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

@pre    control ~>  |c:bit> , A ~>  |a:uint[n]>  , B ~>  |b:uint[n]>  , anc ~>  |0>
@post   control ~>  |c> ,     A ~>  |a>          , B ~>  |a+c*b>      , anc ~>  |0>
def ctrl_cuccaro_no_carry(
  qubit control, 
  qubit[n] A, 
  qubit[n] B, 
  qubit anc) {                      
    ctrl @ maj control, A[0], B[0], anc;         // Forward MAJ ripple
    for uint i in [1:n-1] {
        ctrl @ maj control, A[i],B[i],A[i-1];
    }
    for uint t in [1:n-1] {           // Reverse UMA ripple
        uint i = n - t; 
        ctrl @ uma control, A[i], B[i], A[i-1]; 
    }
    ctrl @ uma control, A[0], B[0], anc;
}

@pre    A ~>  |a:uint[n]> , B ~>  |b:uint[n]>  , f ~>  |0>            , anc ~> |0>
@post   A ~>  |a>         , B ~>  |b>          , f ~>  |z+carry(a,b)> , anc ~> |0>
def cuccaro_carry_only(qubit[n] A,    
                  qubit[n] B,      
                  qubit anc,         
                  qubit f) {      
    maj A[0], B[0], anc;              // Forward MAJ ripple
  for uint i in [1:n-1]  { maj A[i], B[i], A[i-1]; }
  cx A[n-1], f;                       // Final carry lives in A[n-1]; copy to t
  for uint i in [1:n-1]  {            // Uncompute forward MAJ ripple with inverse-MAJ
    uint k=(n-1)-i;
    unmaj A[k], B[k], A[k-1]; 
  }
  unmaj A[0], B[0], anc;
}
def lt(uint[n] a, uint[n] b)->bit{
  return a<b;
}

@pre    A ~>  |a:uint[n]> , B ~>  |b:uint[n]>  , Z ~>  |0>          , X ~>  |0>
@post   A ~>  |a>         , B ~>  |b>          , Z ~>  |z+lt(a,b)>  , X ~>  |0>
def sub_cuccaro_carry_only(qubit[n] A, qubit[n] B, qubit X, qubit Z) {
    uma A[0], B[0], X;                // Forward UMA  ripple 
    for uint i in [1:n-1] {
        uma A[i], B[i], A[i-1]; 
    }
    cx A[n-1], Z;                     // Copy final carry s_n to Z
    for uint t in [1:n-1] {           // Uncompute forward UMA ripple with inverse-MAJ
        uint i = n - t; 
        inv @ uma A[i], B[i], A[i-1]; 
    }
    inv @ uma A[0], B[0], X;
}

@pre A       ~>  |r  :uint[n]> 
  , B        ~>  |s  :uint[n]> 
  , CONST_N  ~>  |N  :uint> 
  , CONST_TN ~>  |TN :uint> 
  , anc      ~>  |0>
  , f_1      ~>  |0>
  , f_2      ~>  |0>
  , 0 <= N   ,  N<(1<<n) 
  , 0 <= TN  ,  TN<(1<<n)
  , N+TN     ~>  (1<<n)
@post A       ~>  |r> 
  , B        ~>  |int(r)+int(s)%N> 
  , CONST_N  ~>  |N> 
  , CONST_TN ~>  |TN> 
  , anc      ~>  |0>
  , f_1      ~>  |0>
  , f_2      ~>  |0>
def add_mod_N_in_place(
  qubit[n] A,         //=|r>
  qubit[n] B,         //=|s>
  qubit[n] CONST_N,   //=|N>
  qubit[n] CONST_TN,  //=|2^n-N>
  qubit anc,          //=|0>
  qubit f_1,          //=|0>
  qubit f_2           //=|0>
){
  cuccaro(A,B,anc,f_1);
  cuccaro(CONST_TN, B, anc, f_2);
  cx f_1, f_2;
  x f_2;
  ctrl_cuccaro_no_carry(f_2,CONST_TN, B, anc);
  x f_2;
  sub_cuccaro_carry_only(A,B,anc,f_2);
}

@pre c        ~>  |c> 
  , X        ~>  |xval  :uint[n]>
  , Y        ~>  |yval  :uint[n]> 
  , CONST_N  ~>  |N  :uint> 
  , CONST_TN ~>  |TN :uint> 
  , A        ~>  |0  :uint[n]>
  , anc      ~>  |0>
  , f_1      ~>  |0>
  , f_2      ~>  |0>
  , 0 < N    ,  N<(1<<n) 
  , 0 < TN   ,  TN<(1<<n)
  , N+TN     ~>  1<<n
@post c       ~>  |c> 
  , X        ~>  |xval>
  , Y        ~>  |(yval+c*a*xval)%N> 
  , CONST_N  ~>  |N> 
  , CONST_TN ~>  |TN> 
  , A        ~>  |0>
  , anc      ~>  |0>
  , f_1      ~>  |0>
  , f_2      ~>  |0>
def ctrl_mul_mod_N_oo_place(
  uint[n] a,          // shadows global const uint[n] a
  qubit c,
  qubit[n] X,         //=|x>
  qubit[n] Y,         //=|0>
  qubit[n] CONST_N,   //=|N>
  qubit[n] CONST_TN,  //=|2^n-N>
  qubit[n] A,         //=|0>
  qubit anc,          //=|0>
  qubit f_1,          //=|0>
  qubit f_2           //=|0>
){
                                // Classical precomputation loop variable: t = a * 2^i mod N (updated each i)
  uint t  = uint(a) % N;        // t = a mod N initially.
  for uint i in [0:n-1]{        // For each control bit X[i], conditionally add constant t to Y (mod N).
    for uint j in [0:n-1] {     // If c~>1, load A := X[i] * t (mask-and-add pattern).
      if ( ((t >> j) , 1) ==  1 ) {
        ccx c, X[i], A[j];      // Single-control load of the j-th bit of t into A[j] if X[i]=1
      }
    }
                                //  Unconditional modular add: Y <- Y + A (mod N)
    add_mod_N_in_place(A, Y, CONST_N, CONST_TN, anc, f_1, f_2);
    for uint j in [0:n-1] {     //  Uncompute A register.
      if ( ((t >> j) , 1) ==  1 ) {
        ccx c, X[i], A[j];      // Single-control load of the j-th bit of t into A[j] if X[i]=1
      }
    }
    t = (t << 1) % N;           // Update t <- (2*t) mod N for the next bit
  }
}
def mod_inv(uint a)-> uint{     // As a,N are coprime, the existence of an inverse is guaranteed. 
  for uint i in [1:N-1]{        // An efficient way to find this is the extended euclidean algorithm, but this also works. 
    if (a*i % N ==  1){
      return i;
    }
  }
  return 0;
}

@pre c        ~>  |c> 
  , X        ~>  |xval  :uint[n]>
  , CONST_N  ~>  |N  :uint> 
  , CONST_TN ~>  |TN :uint> 
  , Y        ~>  |0  :uint[n]> 
  , A        ~>  |0  :uint[n]>
  , anc      ~>  |0>
  , f_1      ~>  |0>
  , f_2      ~>  |0>
  , 0 < N   ,  N   < (1<<n) 
  , 0 < TN  ,  TN  < (1<<n)
  , N+TN     ~>  1<<n
@post c       ~>  |(c*a*xval)%N> 
  , X        ~>  |xval>
  , CONST_N  ~>  |N> 
  , CONST_TN ~>  |TN> 
  , Y        ~>  |0> 
  , A        ~>  |0>
  , anc      ~>  |0>
  , f_1      ~>  |0>
  , f_2      ~>  |0>
def ctrl_mul_mod_N_in_place(
  uint[n] a,          
  qubit c,            
  qubit[n] X,         //=|x>
  qubit[n] CONST_N,   //=|N>
  qubit[n] CONST_TN,  //=|2^n-N>
  qubit[n] Y,         //=|0>
  qubit[n] A,         //=|0>
  qubit anc,          //=|0>
  qubit f_1,          //=|0>
  qubit f_2           //=|0>
){
  ctrl_mul_mod_N_oo_place(
    a, c, X, Y, CONST_N, CONST_TN, A, anc, f_1, f_2
  );
  for uint i in [0: n-1]{
    swap X[i], Y[i];
  }
  uint ainv = mod_inv(a);                       // a^{-1} mod N
  uint a_neg_u = (N - ainv) % N;                // -a^{-1} mod N

  ctrl_mul_mod_N_oo_place((N - ainv) % N, c, X, Y, CONST_N, CONST_TN, A, anc, f_1, f_2);
}

@pre control      ~>  |j: uint[csize]> 
  , target       ~>  |1: uint[n]>
  , CONST_N      ~>  |0: uint[n]>
  , CONST_TN     ~>  |0: uint[n]>
  , anc_1        ~>  |0>
  , anc_2        ~>  |0>
  , anc_3        ~>  |0>
  , 0 < N        ,  N  <  (1<<n) 
@post 
  (control,target)~>  |j>
  , CONST_N      ~>  |(a^j) % N>
  , CONST_TN     ~>  |0>
  , anc_1        ~>  |0>
  , anc_2        ~>  |0>
  , anc_3        ~>  |0>
def modular-exponentiation(
    uint csize,
    uint[n] a, 
    uint N,
    qubit[csize] control,
    qubit[n] target,
    qubit[n] CONST_N,
    qubit[n] CONST_TN,
    qubit anc_1, 
    qubit anc_2, 
    qubit anc_3 
  ){
  uint TN = (1<<n) - N;     // =2^n - N
  for uint i in [0:n-1] {   // Initialize “constant registers”.
    if (((int(N)  >> i) , 1) == 1) { x CONST_N[i]; }
    if (((int(TN) >> i) , 1) == 1) { x CONST_TN[i]; }
  }
  for uint i in [0:csize-1] {
    ctrl_mul_mod_N_in_place (a*(1<<i), control[i], target, CONST_N, CONST_TN, anc_reg_1, anc_reg_2,anc_1, anc_2,anc_3 );
  }
  for uint i in [0:n-1] {    // Reset “constant registers”.
    if (((int(N)  >> i) , 1) == 1) { x CONST_N[i]; }
    if (((int(TN) >> i) , 1) == 1) { x CONST_TN[i]; }
  }
}
