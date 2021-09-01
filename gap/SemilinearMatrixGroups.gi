InstallGlobalFunction(GammaLDimension1, 
function(s, q)
local A, B, primitivePolynomial, x, xq;
    # Construction as in Lemma 6.1 of [2]
    primitivePolynomial := MinimalPolynomial(GF(q), Z(q ^ s));
    x := IndeterminateOfUnivariateRationalFunction(primitivePolynomial);
    A := TransposedMat(CompanionMat(primitivePolynomial));
    xq := PowerMod(x, q, primitivePolynomial);
    # Adding x ^ s here is a bit of a "hack": this ensures that the polynomials
    # from which we extract the coefficients have all degree >= s - 1 so that
    # none of the entries of the matrix B will be empty; by only taking the first
    # s coefficients, the summand x ^ s we "tweaked in" will then be neglected
    B := List([0..s - 1], i -> CoefficientsOfUnivariatePolynomial(x ^ s +
          (PowerMod(xq, i, primitivePolynomial))){[1..s]});
    return Group(A, B);
end);

InstallGlobalFunction(GammaLMeetSL,
function(n, q, s)
local As, rootAs, Bs, Cs, Fs, m, gammaL1, Y, A, B, C, D, DBlock, ZBlock, i, range;
    Assert(1, n mod s = 0);
    Assert(1, IsPrime(s));

    # Construction as in Proposition 6.3 of [2]
    m := QuoInt(n, s);
    gammaL1 := GammaLDimension1(s, q);
    As := gammaL1.1;
    Bs := gammaL1.2;
    Cs := As ^ (q - 1);

    if m = 1 then
        if n mod 2 = 1 then
            return Group(Bs, Cs);
        elif q mod 2 = 1 then
            Fs := (As ^ QuoInt(q - 1, 2)) * Bs;
            return Group(Cs, Fs);
        else
            # TODO
            # This is kind of a hack and is intended to cover the case n=q=s=2
            # which is not treated in [2] at all (technically, this combination
            # of arguments will not be called by the ClassicalMaximals function
            # as SL(2, 2) is soluble - but still!); formerly, this case would
            # just land in the previous elif block, but the quotient (q-1)/2
            # would not be an integer so this is nonsense -- this is a
            # workaround using the fact that for n=q=s=2 we have
            # [[1, 1], [1, 0]]^2 = As so this matrix is some sort of "root" of
            # As; making this choice seems to give the correct results since it
            # produces a group of order 6, as expected
            # --> talk this over with Sergio!!
            rootAs := Z(2) * [[1, 1], [1, 0]];
            Fs := rootAs * Bs;
            return Group(Cs, Fs);
        fi;
    fi;

    A := IdentityMat(n, GF(q));
    A{[1..s]}{[1..s]} := As;
    A{[s + 1..2 * s]}{[s + 1..2 * s]} := As ^ -1;
    Y := SL(m, q ^ s).2;
    B := KroneckerProduct(Y, IdentityMat(s, GF(q)));
    C := IdentityMat(n, GF(q));
    C{[1..s]}{[1..s]} := Cs;
    D := IdentityMat(n, GF(q));
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

    return Group(A, B, C, D);
end);