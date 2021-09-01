InstallGlobalFunction(SubfieldSL, 
function(n, p, e, f)
local A, B, C, D, c, k, matrixForCongruence, lambda, zeta, omega, z, X,
subgroup;
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
        subgroup := Group(A, B, C);
        SetSize(subgroup, Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f -
        1), n));
        return subgroup;
    fi;

    omega := zeta ^ QuoInt(p ^ e - 1, p ^ f - 1);
    D := DiagonalMat(Concatenation([omega], List ([2..n], i -> zeta^0))) ^ c;

    # solving the congruence lambda * n = z (mod p ^ e - 1) by solving the
    # matrix equation (n, p ^ e - 1) * (lambda, t) ^ T = z over the integers
    matrixForCongruence := MatrixByEntries(Integers, 2, 1, [n, p ^ e - 1]);
    z := c * QuoInt(p ^ e - 1, p ^ f - 1);
    lambda := SolutionMat(matrixForCongruence, [z])[1];

    X := zeta ^ (-lambda) * IdentityMat(n, GF(p ^ e));
    subgroup := Group(A, B, C, X * D);
    SetSize(subgroup, Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f - 1),
    n)); 
    return subgroup;
end);

