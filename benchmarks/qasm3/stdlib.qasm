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

// Rotation around X-axis
@pre    a == |x>
@post   a == 1/2*sum{y}(exp(θ/2)+exp(θ/2+π*(x+y)))|y>
gate rx(θ) a { U(θ, -π/2, π/2) a; } 

// rotation around Y-axis
@pre    a == |x>
@post   a == 1/2*sum{y}exp(θ*(y-x)/2)*(exp(-θ/2)+exp(θ/2+π*(x+y)))|y>
gate ry(θ) a { U(θ, 0, 0) a; }

// rotation around Z axis
@pre    a == |x>
@post   a == 1/2*sum{y}exp(π*(x+y)/2)*(exp(-θ/2)+exp(θ/2+π*(x+y)))|y>
gate rz(λ) a { gphase(-λ/2); U(0, 0, λ) a; }

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

// controlled-phase
@pre    (a,b) == |x,y>
@post   (a,b) == exp(π*x*y*λ)|x,y>
gate cp(λ) a, b { ctrl @ p(λ) a, b; } 

// controlled-rx
gate crx(θ) a, b
// controlled-ry
gate cry(θ) a, b
// controlled-rz
gate crz(θ) a, b
// controlled-H
gate ch a, b { ctrl @ h a, b; }
// swap
gate swap a, b { cx a, b; cx b, a; cx a, b; }
// Toffoli
gate ccx a, b, c { ctrl @ ctrl @ x a, b, c; } // controlled-swap
gate cswap a, b, c { ctrl @ swap a, b, c; }
// four parameter controlled-U gate with relative phase γ gate cu(θ, φ, λ, γ) c, t { p(γ) c; ctrl @ U(θ, φ, λ) c, t; }
{ ctrl @ rx(θ) { ctrl @ ry(θ) { ctrl @ rz(θ)
a, b; }
a, b; }
a, b; }
14
// Gates for OpenQASM 2 backwards compatibility // CNOT
gate CX c, t { ctrl @ U(π, 0, π) c, t; }
// phase gate
gate phase(λ) q { U(0, 0, λ) q; }
// controlled-phase
gate cphase(λ) a, b { ctrl @ phase(λ) a, b; }
// identity or idle gate
gate id a { U(0, 0, 0) a; }
// IBM Quantum experience gates
gate u1(λ) q { U(0, 0, λ) q; }
gate u2(φ, λ) q { gphase(-(φ+λ)/2); U(π/2, φ, λ) q; } gate u3(θ, φ, λ) q { gphase(-(φ+λ)/2); U(θ, φ, λ) q; }