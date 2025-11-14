OPENQASM 3.0;

include "stdgates.inc";

// OpenQASM 3 standard gate library

// // Pauli gate: bit-flip or NOT gate
// @pre a ~>  |v:bit>
// @post a ~> |1+v>
// gate x_copy a { x a; }

// Pauli gate: bit and phase flip 
// @pre    a ~> |qa:bit>
// @post   a ~> exp(qa+1/2)|1+qa>
// gate y_copy a { y a;} 

// Pauli gate: phase flip
@pre    a ~> |qa:bit>
@post   a ~> exp(qa)|qa>
gate z_copy a { z a; }

// Clifford gate: Hadamard
@pre    a ~> |qa:bit>
@post   a ~> sum{j}. exp(qa*j) |j>
gate h_copy a { h a; }

// Clifford gate: sqrt(Z) or S gate 
@pre    a ~> |qa:bit>
@post   a ~> exp(qa/2)|qa>
gate s_copy a { s a; }

// // Clifford gate: inverse of sqrt(Z) 
// @pre    a ~> |qa>
// @post   a ~> exp(-qa/2)|qa>
// gate sdg_copy a { sdg a; }

// sqrt(S) or T gate
@pre    a ~> |qa:bit>
@post   a ~> exp(qa/4)|qa>
gate t_copy a { pow(1/2) @ s a; }

// // inverse of sqrt(S)
// @pre    a ~> |qa>
// @post   a ~> exp(-qa/4)|qa>
// gate tdg a { inv @ pow(1/2) @ s a; }

// // sqrt(NOT) gate
// @pre    a ~> |qa>
// @post   a ~> sum{j}.exp(qa*j)|j>
// gate sx a { pow(1/2) @ x a; }

// // controlled-NOT
// @pre    (c,t) ~> |qc,qt>
// @post   (c,t) ~> |qc,qc+qt>
// gate cx c, t { ctrl @ x c, t; } 

// // controlled-Y
// @pre    (a,b) ~> |qa,qb>
// @post   (a,b) ~> exp(qa*(qb+1/2))|qa,1+qb>
// gate cy a, b { ctrl @ y a, b; } 

// // controlled-Z
// @pre    (a,b) ~> |qa,qb>
// @post   (a,b) ~> exp(qa*qb)|qa,qb>
// gate cz a, b { ctrl @ z a, b; }

// // controlled-H
// @pre    (a,b) ~> |qa,q>
// @post   (a,b) ~> sum{j}. exp(qb*j) | qa,(1 + qa)*qb+ qa*j>
// gate ch a, b { ctrl @ h a, b; }

// // swap
// @pre    (a,b) ~> |qa,qb >
// @post   (a,b) ~> |qb,qb>
// gate swap a, b { cx a, b; cx b, a; cx a, b; }

// // Toffoli
// @pre    (a,b,c) ~> | qa,qb,qc>
// @post   (a,b,c) ~> | qa,qb,qc + qa*qb >
// gate ccx a, b, c { ctrl @ ctrl @ x a, b, c; } 

// // controlled-swap
// @pre    (a,b,c) ~> | qa,qb,qc >
// @post   (a,b,c) ~> | qa, qa*qc+(1+qa)*qb, qa*qb+(1+qa)*qb>
// gate cswap a, b, c { ctrl @ swap a, b, c; }

// // Gates for OpenQASM 2 backwards compatibility // CNOT
// @pre    (c,t) ~> |qc,qt>
// @post   (c,t) ~> |qc,qc+qt>
// gate CX c, t { ctrl @ U(π, 0, π) c, t; }

// // identity or idle gate
// @pre    a ~> |qa>
// @post   a ~> |qa>
// gate id a { U(0, 0, 0) a; }