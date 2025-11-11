@pre q ~> |0>|0> + |1>|1> , a ~> c:bit[2] , b ~> 0
@post b ~> c
def sd(qubit[2] q, bit[2] a, bit[2] b) {
  if (a[1] == 1) {
    x q[0];
  }
  if (a[0] == 1) {
    z q[0];
  }
  cx q[0], q[1];
  h q[0];
  b[0] = measure q[0];
  b[1] = measure q[1];
}
