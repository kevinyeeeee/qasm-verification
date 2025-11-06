// OpenQASM 3 standard gate library

// phase gate
@pre    a == |x>
@post   a == exp(π*x*λ)|x>
gate p(λ) a { ctrl @ gphase(λ) a; }

// Pauli gate: bit-flip or NOT gate
@pre    a == |x>
@post   a == |1+x>
gate x a { U(π, 0, π) a; }

// Pauli gate: bit and phase flip 
@pre    a == |x>
@post   a == exp(π*(x+1/2))|1+x>
gate y a { U(π, π/2, π/2) a; } 

// Pauli gate: phase flip
@pre    a == |x>
@post   a == exp(π*x)|x>
gate z a { p(π) a; }

// Clifford gate: Hadamard
@pre    a == |x>
@post   a == 1/sqrt(2)*sum{y}exp(π*x*y)|y>
gate h a { U(π/2, 0, π) a; }

// Clifford gate: sqrt(Z) or S gate 
@pre    a == |x>
@post   a == exp(π*x/2)|x>
gate s a { pow(1/2) @ z a; }

// Clifford gate: inverse of sqrt(Z) 
@pre    a == |x>
@post   a == exp(-π*x/2)|x>
gate sdg a { inv @ pow(1/2) @ z a; }

// sqrt(S) or T gate
@pre    a == |x>
@post   a == exp(π*x/4)|x>
gate t a { pow(1/2) @ s a; }

// inverse of sqrt(S)
@pre    a == |x>
@post   a == exp(-π*x/4)|x>
gate tdg a { inv @ pow(1/2) @ s a; }

// sqrt(NOT) gate
@pre    a == |x>
@post   a == 1/sqrt(2)*sum{y}exp(π*x*y)|y>
gate sx a { pow(1/2) @ x a; }

// controlled-NOT
@pre    (c,t) == |x,y>
@post   (c,t) == |x,x+y>
gate cx c, t { ctrl @ x c, t; } 

// controlled-Y
@pre    (a,b) == |x,y>
@post   (a,b) == exp(π*x*(y+1/2))|x,1+y>
gate cy a, b { ctrl @ y a, b; } 

// controlled-Z
@pre    (a,b) == |x,y>
@post   (a,b) == exp(π*x*y)|x,y>
gate cz a, b { ctrl @ z a, b; }

// controlled-H
@pre    (a,b) == | x, w >
@post   (a,b) == 1/sqrt(2) * sum{y}exp(π*w*y)| x, (1 + x)*w + x*y >
gate ch a, b { ctrl @ h a, b; }

// swap
@pre    (a,b) == | x, w >
@post   (a,b) == | w, x >
gate swap a, b { cx a, b; cx b, a; cx a, b; }

// Toffoli
@pre    (a,b,c) == | x, y, z >
@post   (a,b,c) == | x, y, z + x*y >
gate ccx a, b, c { ctrl @ ctrl @ x a, b, c; } 

// controlled-swap
@pre    (a,b,c) == | x, y, z >
@post   (a,b,c) == | x, x*z+(1+x)*y, x*y+(1+x)*y >
gate cswap a, b, c { ctrl @ swap a, b, c; }

// Gates for OpenQASM 2 backwards compatibility // CNOT
@pre    (c,t) == |x,y>
@post   (c,t) == |x,x+y>
gate CX c, t { ctrl @ U(π, 0, π) c, t; }

// identity or idle gate
@pre    a == |x>
@post   a == |x>
gate id a { U(0, 0, 0) a; }