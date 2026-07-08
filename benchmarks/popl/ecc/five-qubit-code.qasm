gate m1 a, b, c, d, e { x a; z b; z c; x d;      }
gate m2 a, b, c, d, e {      x b; z c; z d; x e; }
gate m3 a, b, c, d, e { x a;      x c; z d; z e; }
gate m4 a, b, c, d, e { z a; x b;      x d; z e; }

gate encode a, b, c, d, e {
  h a;
  s a;
  z e;
  cz a, b;
  cz a, d; 
  cy a, e;
  h b;
  cz b, c;
  cz b, d;
  cx b, e;
  h c;
  cz c, a;
  cz c, b;
  cx c, e;
  h d;
  s d;
  cz d, a;
  cz d, c;
  cy d, e;
}

def correct(uint[4] syn, qubit[5] q) {
  if (syn == 1) { x q[0]; }
  if (syn == 8) { x q[1]; }
  if (syn == 12) { x q[2]; }
  if (syn == 6) { x q[3]; }
  if (syn == 3) { x q[4]; }
  if (syn == 10) { z q[0]; }
  if (syn == 5) { z q[1]; }
  if (syn == 2) { z q[2]; }
  if (syn == 9) { z q[3]; }
  if (syn == 4) { z q[4]; }
  if (syn == 11) { y q[0]; }
  if (syn == 13) { y q[1]; }
  if (syn == 14) { y q[2]; }
  if (syn == 15) { y q[3]; }
  if (syn == 7) { y q[4]; }
}

def apply_error(bit[5] x_error, bit[5] z_error, qubit[5] q) {
  for int i in [0:4] {
    if (x_error[i] == 1) { x q[i]; }
    if (z_error[i] == 1) { z q[i]; }
  }
}

@pre s ~> |0,0,0,0> , q ~> |0,0,0,0,r:bit>, popcount(xe) + popcount(ze) <= 1
@post q ~> |0, 0, 0, 0, r>
def err(qubit[5] q, qubit[4] s, bit[5] xe, bit[5] ze) {
  encode q[0], q[1], q[2], q[3], q[4];

  apply_error(xe, ze, q);

  h s;
  ctrl @ m1 s[3], q[0], q[1], q[2], q[3], q[4];
  ctrl @ m2 s[2], q[0], q[1], q[2], q[3], q[4];
  ctrl @ m3 s[1], q[0], q[1], q[2], q[3], q[4];
  ctrl @ m4 s[0], q[0], q[1], q[2], q[3], q[4];
  h s;
  uint[4] u = 0;
  u = measure s;

  correct(u, q);
  inv @ encode q[0], q[1], q[2], q[3], q[4];
}
