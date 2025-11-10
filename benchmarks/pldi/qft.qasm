include "stdgates.inc";

const uint n=4;

@pre    q ==  |qx>
@post   q == sum{j:uint[n]} exp(2*qx*j/2^n)*|j>
def qft(qubit[n] q) {
  for int i in [0:n-1] {
    h q[i];
    for int j in [i+1:n-1] {  
      int one = 1;                  // angle = pi / 2^(j - i)
      cp(pi / (one << (j-i))) q[j], q[i];
    }
  }
  for uint i in [0:n/2-1] {
    swap q[i], q[n-1-i];
  }
}