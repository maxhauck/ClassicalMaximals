# Construction as in Proposition 11.1 of [2]
BindGlobal("SymplecticNormalizerInSL",
function(d, q)
    local zeta, gcd, A, B, C, D, i, E, result;
    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    zeta := PrimitiveElement(GF(q));
    A := Sp(d, q).1;
    B := Sp(d, q).2;
    gcd := Gcd(d, q - 1);
    # generates the center of SL(d, q)
    C := zeta ^ QuoInt(q - 1, gcd) * IdentityMat(d, GF(q));

    if IsEvenInt(q) or gcd / 2 = Gcd(q - 1, d / 2) then
        result := Group([A, B, C]);
        # Size according to Table in [1]
        SetSize(result, gcd * Size(PSp(d, q)));
    else
        D := DiagonalMat(Concatenation(List([1..d / 2], i -> zeta),
                                       List([1..d / 2], i -> zeta ^ 0)));
        # solving the congruence d * i = d / 2 mod q - 1 for i
        i := (d / 2) / gcd * (d / gcd) ^ (-1) mod ((q - 1) / gcd);
        E := zeta ^ (-i) * D;
        result := Group([A, B, C, E]);
        # Size according to Table 2.11 in [1]
        # Note that |PCSp(d, q)| = |CSp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)| * |CSp(d, q) : Sp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)|,
        # since |CSp(d, q) : Sp(d, q)| = q - 1 according to Table 1.3 of [1]
        SetSize(result, gcd * Size(Sp(d, q)));
    fi;

    return result;
end);

# Construction as in Proposition 11.3 of [2]
BindGlobal("UnitaryNormalizerInSL",
function(d, q)
    local qFactorization, e, p, q0, zeta, C, g, c, SUWithIdentityForm, SUGens, gens, D, zetaId, solution, result;
    qFactorization := PrimePowersInt(q);
    e := qFactorization[2];
    if IsOddInt(e) then
        ErrorNoReturn("No such subrgoups exist since <q> is not square.");
    fi;
    p := qFactorization[1];

    q0 := p^(QuoInt(e, 2));
    zeta := PrimitiveElement(GF(q));
    C := zeta^(QuoInt((q - 1), Gcd(q - 1, d))) * IdentityMat(d, GF(q)); # generates the center of SL(d, q)
    g := Gcd(q - 1, d);
    c := QuoInt(Gcd(q0 + 1, d) * (q - 1), Lcm(q0 + 1, QuoInt(q - 1, g)) * g);
    SUWithIdentityForm := ChangeFixedSesquilinearForm(SU(d, q0), IdentityMatrix(GF(q0), d));
    SUGens := GeneratorsOfGroup(SUWithIdentityForm);

    gens := Concatenation(SUGens, [C]);
    if not IsOne(c) then
        D := (GL(d, q).1) ^ (q0 - 1); # diagonal matrix [zeta^(q0 - 1), 1, ..., 1]
        zetaId := zeta * IdentityMat(d, GF(q));
        for solution in NullspaceIntMat([[q0 - 1], [d], [q - 1]]) do
            Add(gens, D ^ solution[1] * zetaId ^ solution[2]);
        od;
    fi;

    result := Group(gens);
    # Size according to Table 2.11 in [1]
    SetSize(result, Size(SUWithIdentityForm) * Gcd(q0 - 1, d));
    return result;
end);
