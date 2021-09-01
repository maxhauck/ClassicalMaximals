InstallGlobalFunction(SubfieldSL, 
function(n, p, e, f)
local A, B, C, D, c, k, matrixForCongruence, lambda, zeta, omega, z, X;
    Assert(1, e mod f = 0);
    Assert(1, IsPrimeInt(QuoInt(e, f)));

    # Construction as in Proposition 8.1 of [2] 
    A := SL(n, p ^ f).1;
    B := SL(n, p ^ f).2;
    zeta := PrimitiveElement(GF(p ^ e));
    k := Gcd(p ^ e - 1, n);
    c := QuoInt((k * Lcm(p ^ f - 1, QuoInt((p ^ e - 1), k))), (p ^ e - 1));
    C := zeta ^ (QuoInt(p ^ e - 1, k)) * IdentityMat(n, GF(p ^ e));

    if c = Gcd(p ^ f - 1, n) then
        # TODO
        # This is not quite optimal as A and B are matrics over GF(p ^ f)
        # whereas C is a matrix over GF(p ^ e); it does work and gives the
        # correct result, but the generators of the group are not displayed
        # properly - how to cast A and B as matrics over GF(p ^ e) instead?
        # --> ask Sergio!!
        return Group(A, B, C);
    fi;

    omega := zeta ^ QuoInt(p ^ e - 1, p ^ f - 1);
    D := DiagonalMat(Concatenation([omega], List ([2..n], i -> zeta^0))) ^ c;

    # solving the congruence lambda * n = z (mod p ^ e - 1) by solving the
    # matrix equation (n, p ^ e - 1) * (lambda, t) ^ T = z over the integers
    matrixForCongruence := MatrixByEntries(Integers, 2, 1, [n, p ^ e - 1]);
    z := c * QuoInt(p ^ e - 1, p ^ f - 1);
    lambda := SolutionMat(matrixForCongruence, [z])[1];

    X := zeta ^ (-lambda) * IdentityMat(n, GF(p ^ e));
    # TODO
    # Same thing as above 
    # --> ask Sergio!!
    return Group(A, B, C, X * D);
end);

