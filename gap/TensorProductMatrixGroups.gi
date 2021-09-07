# Construction as in Proposition 7.1 of [2]
BindGlobal("TensorProductGroups",
function(d1, d2, q)
    local d, c, k, zeta, C, Id1, Id2, gens, SL_d1_gens, SL_d2_gens, g1, g2, n;
    d := d1 * d2;
    k := Gcd(d, q - 1);
    c := QuoInt(Gcd(d1, q - 1) * Gcd(d2, q - 1) * Gcd(d1, d2, q - 1), k);
    zeta := PrimitiveElement(GF(q));
    C := zeta^(QuoInt((q - 1), k)) * IdentityMat(d, GF(q)); # generates the center of SL(d, q)
    Id1 := One(SL(d1 ,q));
    Id2 := One(SL(d2 ,q));
    gens := [C];
    SL_d1_gens := GeneratorsOfGroup(SL(d1, q));
    SL_d2_gens := GeneratorsOfGroup(SL(d2, q));
    Add(gens,KroneckerProduct(SL_d1_gens[1], Id2)); # corresponds to S in [2]
    Add(gens,KroneckerProduct(SL_d1_gens[2], Id2)); # corresponds to T in [2]
    Add(gens,KroneckerProduct(SL_d2_gens[1], Id1)); # corresponds to U in [2]
    Add(gens,KroneckerProduct(SL_d2_gens[2], Id1)); # corresponds to V in [2]


    if not c = 1 then
        g1 := GL(d1, q).1;
        g2 := GL(d2, q).1;
        for n in NullspaceMat([[d2], [d1], [q - 1]]) do
            Add(gens, KroneckerProduct(g1^n[1], g2^n[2]));
        od;
    fi;

    return Group(gens);
end);
