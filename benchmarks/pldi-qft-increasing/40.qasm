OPENQASM 3.0;
const uint n = 40;
@pre a ~> |q:uint[n]>
@post a ~> sum{r:uint[n]}.exp(2*q*r/(2^n))|r>
def qftn(qubit[n] a) {
    for int i in [0:(n/2)-1] {
      swap a[i], a[n-1-i];
    }
    for int i in [0:n-1] {
        h a[i];
        for int j in [i+1:n-1] {
            crz(2*pi/(2**(j-i+1))) a[i], a[j];
        }
    }
}