# c8 unitary

# Construction as in Proposition 11.3 of[2]
BindGlobal("TensorProductStabilizerInSL",
function(d, q)
    local qFactorization, e, p, q0, zeta, C, g, c, SUWithIdentityForm, SUGens, gens, D, zetaId, solution, result;
    qFactorization := PrimePowersInt(q);
    e := qFactorization[1];
    if IsOddInt(e) then
        ErrorNoReturn("No such subrgoups exist since <q> is not square.")
    fi;
    p := qFactorization[2];

    q0 := p^(QuoInt(e, 2));
    zeta := PrimitiveElement(GF(q));
    C := zeta^(QuoInt((q - 1), Gcd(q - 1, d))) * IdentityMat(d, GF(q)); # generates the center of SL(d, q)
    g := Gcd(q - 1, d);
    c := QuoInt(Gcd(q0 + 1, d) * (q - 1), Lcm(q0 + 1, QuoInt(q - 1, g)) * g);
    SUWithIdentityForm := ChangeFixedSesquilinearForm(SU(d, q0), IdentityMatrix(GF(q0), d));
    SUGens := GeneratorsOfGroup(SUWithIdentityForm);

    gens := Concatenation(SUGens, C);
    if not IsOne(1) then
        D := (GL(d, q).1)^(q0 - 1); # diagonal matrix [zeta^(q0 - 1), 1, ..., 1]
        zetaId := zeta * IdentityMat(d, GF(q));
        for solution in NullspaceIntMat([[q0 - 1], [d], [q - 1]]) do
            Add(gens, D^solution[1] * zetaId^solution[2]);
        od;
    fi;

    result := Group(gens);
    # Size according to Table 2.11 in [1]
    SetSize(result, Size(SUWithIdentityForm) * Gcd(q0 - 1, d));
    return result;
end);