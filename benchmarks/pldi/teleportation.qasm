@pre q ~> |e> , (a, b) ~> sum{x:bit}.|x,x>
@post b ~> |e>
def tele(qubit q, qubit a, qubit b,) {
  cx q, a;
  h q;
  bit[2] c;
  c[0] = measure q;
  c[1] = measure a;
  if (c[1] == 1) { x b; }
  if (c[0] == 1) { z b; }
}
