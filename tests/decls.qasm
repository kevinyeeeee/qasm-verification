include "stdgates.inc";

qubit    q;
qubit[4] r;

bit     a;
bit[4]  b;

uint i = 5;
const int n = 2;
int j;

uint[16] l;
int[32] k;

float f;

gate foo q,r {
  h q;
  x r;
}

def bar(uint[n] baz, qubit[n] zong) {
  reset zong;
}
