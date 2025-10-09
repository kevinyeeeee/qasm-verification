OPENQASM 3.0;

include "stdgates.inc";

const uint n = 4;                     // ceil(log2(10)) = 4
const uint N = 10;                // choose a,N coprime
const uint[n] a = 3;
const uint TN = (1<<n) - N;    // 2^n - N

// global “constant registers”
qubit[n] CONST_N;   // |N>
qubit[n] CONST_TN;  // |2^n - N>

//initialize “constant registers”
for uint i in [0:n-1] {
  if (((int(N)  >> i) & 1) == 1) { x CONST_N[i]; }
  if (((int(TN) >> i) & 1) == 1) { x CONST_TN[i]; }
}

qubit[n] control;            // allocates in |0>^n
qubit[n] target;             // allocates in |0>^n
x target[0];
//initialize ancilla registers
qubit[n] anc_reg_1;
qubit[n] anc_reg_2;
qubit anc_1;
qubit anc_2;
qubit anc_3;
//initialize classical output register
bit[n] out=0;


def qft(qubit[n] q) {
  for int i in [0:n-1] {
    h q[i];
    for int j in [i+1:n-1] {
      // angle = pi / 2^(j - i)
      int one = 1;
      cp(pi / (one << (j-i))) q[j], q[i];
    }
  }
  for uint i in [0:n/2-1] {
    swap q[i], q[n-1-i];
  }
}

def iqft(qubit[n] q) {
  for uint i in [0:n/2-1] {
    swap q[i], q[n-1-i];
  }
  for int i in [0:n-1] {
    int i_ = (n-1)-i;
    for int j in [i_+1:n-1] {
      // angle = pi / 2^(j - i)
      int one = 1;
      cp(-pi / (one << (j-i_))) q[j], q[i_];
    }
    h q[i_];
  }
}

@pre a=|x> && b=|y> && c=|z>
@post a=|x*y+x*z+y*z> && b=|x+y> && c=|x+z>
gate maj a, b, c {  // in-place majority
  cx a, b;
  cx a, c; 
  ccx c, b, a;    //a=|x+(x+y)*(x+z)>
}

@pre a=|x*y+x*z+y*z> && b=|x+y> && c=|x+z>
@post a=|x> && b=|y> && c=|z>
gate unmaj a, b, c {
  ccx c, b, a;   // Inverse of MAJ
  cx  a, c;
  cx  a, b;
}

@pre a=|x*y+x*z+y*z> && b=|x+y> && c=|x+z>
@post a=|x> && b=|x+y+z> && c=|z>
gate uma a, b, c{  // unmajority and add (2-CNOT form)
  ccx c, b, a;
  cx a, c;      
  cx c, b;
}


/* Ripple-carry adder 
   Inputs:  A[i]=a_i, B[i]=b_i, Z = z,       X=|0⟩
   Outputs: A[i]=a_i, B[i]=s_i, Z = z ⊕ s_n, X =|0⟩ */
def cuccaro(qubit[n] A, qubit[n] B, qubit X, qubit Z) {

    // Forward MAJ ripple
    maj A[0], B[0], X;
    for uint i in [1:n-1] {
        maj A[i],B[i],A[i-1];
    }

    // Copy final carry s_n to Z
    cx A[n-1], Z;

    // Reverse UMA ripple
    for uint t in [1:n-1] {
        uint i = n - t; 
        uma A[i], B[i], A[i-1]; 
    }
    uma A[0], B[0], X;
}
/* Same as cuccaro with no final carry */
def cuccaro_no_carry(
  qubit[n] A, 
  qubit[n] B, 
  qubit anc) {

    // Forward MAJ ripple
    maj A[0], B[0], anc;
    for uint i in [1:n-1] {
        maj A[i],B[i],A[i-1];
    }

    // Reverse UMA ripple
    for uint t in [1:n-1] {
        uint i = n - t; 
        uma A[i], B[i], A[i-1]; 
    }
    uma A[0], B[0], anc;
}
def ctrl_cuccaro_no_carry(
  qubit control, 
  qubit[n] A, 
  qubit[n] B, 
  qubit anc) {

    // Forward MAJ ripple
    ctrl @ maj control, A[0], B[0], anc;
    for uint i in [1:n-1] {
        ctrl @ maj control, A[i],B[i],A[i-1];
    }

    // Reverse UMA ripple
    for uint t in [1:n-1] {
        uint i = n - t; 
        ctrl @ uma control, A[i], B[i], A[i-1]; 
    }
    ctrl @ uma control, A[0], B[0], anc;
}
def cuccaro_carry_only(qubit[n] A,    
                  qubit[n] B,      
                  qubit anc,         
                  qubit f) {      
  // forward MAJ ripple for B+A
  maj A[0], B[0], anc;
  for uint i in [1:n-1]  { maj A[i], B[i], A[i-1]; }
  // final carry lives in A[n-1]; copy to t
  cx A[n-1], f;
  // undo with inverse-MAJ to restore b and KTA exactly
  for uint i in [1:n-1]  { 
    uint k=(n-1)-i;
    unmaj A[k], B[k], A[k-1]; 
  }
  unmaj A[0], B[0], anc;
}
def sub_cuccaro_carry_only(qubit[n] A, qubit[n] B, qubit X, qubit Z) {

    // Forward UMA  ripple
    uma A[0], B[0], X;
    for uint i in [1:n-1] {
        uma A[i], B[i], A[i-1]; 
    }

    // Copy final carry s_n to Z
    cx A[n-1], Z;

    // Reverse inverse UMA ripple
    for uint t in [1:n-1] {
        uint i = n - t; 
        inv @ uma A[i], B[i], A[i-1]; 
    }
    inv @ uma A[0], B[0], X;
}
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

def ctrl_mul_mod_N_oo_place(
  uint[n] a, //shadows global const uint[n] a
  qubit c,
  qubit[n] X, //=|x>
  qubit[n] Y, //=|0>
  qubit[n] CONST_N,//=|N>
  qubit[n] CONST_TN, //=|2^n-N>
  qubit[n] A, //=|0>
  qubit anc, //=|0>
  qubit f_1, //=|0>
  qubit f_2 //=|0>
){
  // Classical precomputation loop variable: t = a * 2^i mod N (updated each i)

  uint t  = uint(a) % N;     // t = a mod N initially

  // For each control bit X[i], conditionally add constant t to Y (mod N)
  for uint i in [0:n-1]{

    // --- prepare A := X[i] * t (mask-and-add pattern)
    for uint j in [0:n-1] {
      if ( ((t >> j) & 1) == 1 ) {
        // Single-control load of the j-th bit of t into A[j] if X[i]=1
        ccx c, X[i], A[j];
      }
    }

    // --- unconditional modular add: Y <- Y + A (mod N)
    add_mod_N_in_place(A, Y, CONST_N, CONST_TN, anc, f_1, f_2);

    // --- unprepare A back to |0^n>
    for uint j in [0:n-1] {
      if ( ((t >> j) & 1) == 1 ) {
        // Single-control load of the j-th bit of t into A[j] if X[i]=1
        ccx c, X[i], A[j];
      }
    }

    // Update t <- (2*t) mod N for the next bit (schoolbook shift-add)
    t = (t << 1) % N;
  }

}
def mod_inv(uint a)-> uint{
  //as a,N are coprime, so the existence of an inverse is guaranteed. 
  //an efficient way to find this is the extended euclidean algorithm, but this also works. 
  for uint i in [1:N-1]{
    if (a*i % N==1){
      return i;
    }
  }
  return 0;
}

def ctrl_mul_mod_N_in_place(
  uint[n] a, //shadows global const uint[n] a
  qubit c, //shadows global const uint[n] a
  qubit[n] X, //=|x>
  qubit[n] CONST_N,//=|N>
  qubit[n] CONST_TN, //=|2^n-N>
  qubit[n] Y, //=|0>
  qubit[n] A, //=|0>
  qubit anc, //=|0>
  qubit f_1, //=|0>
  qubit f_2 //=|0>
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
//
//ORDER-FINDING 
//
for uint i in [0:n-1] {
  h control[i];
  ctrl_mul_mod_N_in_place (a, control[i], target, CONST_N, CONST_TN, anc_reg_1, anc_reg_2,anc_1, anc_2,anc_3 );
}
//reset “constant registers”
for uint i in [0:n-1] {
  if (((int(N)  >> i) & 1) == 1) { x CONST_N[i]; }
  if (((int(TN) >> i) & 1) == 1) { x CONST_TN[i]; }
}
iqft(control);
out =measure control;