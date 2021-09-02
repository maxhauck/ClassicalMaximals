# Construction as in Lemma 6.1 of [2]
BindGlobal("CLASSICALMAXIMALS_GammaLDimension1",
function(s, q)
    local primitivePolynomial, A, x, xq, B, row, i;
    # Let w be a primitive element of GF(q ^ s) over GF(q).
    # A acts on the standard basis in the same way as w acts by multiplication
    # on the GF(q)-basis {1, w, w ^ 2, ...} of GF(q ^ s). (Note that A is a
    # Singer cycle, i.e. has order q ^ s - 1.)
    primitivePolynomial := MinimalPolynomial(GF(q), Z(q ^ s));
    A := TransposedMat(CompanionMat(primitivePolynomial));
    # B acts on the standard basis in the same way as the Frobenius acts on the
    # basis {1, w, w ^ 2, ...} of GF(q ^ s) over GF(q), where w is as above.
    x := IndeterminateOfUnivariateRationalFunction(primitivePolynomial);
    xq := PowerMod(x, q, primitivePolynomial);
    B := [];
    for i in [0 .. s - 1] do
        row := CoefficientsOfUnivariatePolynomial(PowerMod(xq,
                                                           i,
                                                           primitivePolynomial));
        row := Concatenation(row,
                             ListWithIdenticalEntries(s - Length(row),
                                                      Zero(GF(q))));
        Add(B, row);
    od;
    return rec(A := A, B := B);
end);

# Construction as in Proposition 6.3 of [2]
InstallGlobalFunction(GammaLMeetSL,
function(n, q, s)
    local As, rootAs, Bs, Cs, Fs, m, gammaL1, Y, A, B, C, D, DBlock, ZBlock, i,
    range, result;
    if n mod s <> 0 or not IsPrime(s) then
        ErrorNoReturn("<s> must be prime and a divisor of <n> but <s> = ", s,
                      "<n> = ", n);
    fi;
    gammaL1 := CLASSICALMAXIMALS_GammaLDimension1(s, q);
    # Let w be a primitive element of GF(q ^ s) over GF(q). Since As is the
    # companion matrix of the minimal polynomial of w over GF(q), its
    # determinant is (-1) ^ s times the constant term of said minimal
    # polynomial. By Vieta, this constant term is (-1) ^ s * the product of
    # all Galois conjugates of w. Hence, det(As) = w ^ ((q ^ s - 1) / (q - 1)).
    As := gammaL1.A;
    # By Lemma 6.2 det(Bs) = (-1) ^ (s - 1).
    Bs := gammaL1.B;
    # det(Cs) = det(As) ^ (q - 1) = w ^ (q ^ s - 1) = 1.
    Cs := As ^ (q - 1);
    m := QuoInt(n, s);
    if m = 1 then
        if n mod 2 = 1 then
            result := Group(Bs, Cs);
        elif q mod 2 = 1 then
            Fs := (As ^ QuoInt(q - 1, 2)) * Bs;
            result := Group(Cs, Fs);
        # n = s = 2 and q even
        else
            # In characteristic 2 we have det(Bs) = -1 = 1.
            result := Group(Bs, Cs);
        fi;
        SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
        return result;
    fi;

    A := IdentityMat(n, GF(q));
    A{[1..s]}{[1..s]} := As;
    A{[1..s]}{[1..s]} := As;
    A{[s + 1..2 * s]}{[s + 1..2 * s]} := As ^ -1;
    Y := SL(m, q ^ s).2;
    B := KroneckerProduct(Y, IdentityMat(s, GF(q)));
    C := IdentityMat(n, GF(q));
    C{[1..s]}{[1..s]} := Cs;
    D := IdentityMat(n, GF(q));
    # The determinant of D might be -1. In these cases, adjust D.
    if s = 2 and IsOddInt(m) and IsOddInt(q) then
        ZBlock := As ^ QuoInt(q - 1, 2);
        DBlock := ZBlock * Bs;
    else
        DBlock := Bs;
    fi;
    for i in [0..m - 1] do
        range := [i * s + 1..(i + 1) * s];
        D{range}{range} := DBlock;
    od;

    result := Group(A, B, C, D);
    SetSize(result, Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s);
    return result;
end);
