# Construction as in Lemma 10.1 of [2]
# TensorWreathProduct := function(H, K)
#     local A, i, d, t, m, field, symt, gens, generator, tensorProductBasis,
#     permuteTensorProductBasisElements, permutation;
#     m := Length(One(H));
#     field := DefaultFieldOfMatrixGroup(H);
#     t := LargestMovedPoint(K);
#     symt := SymmetricGroup(t);
#     d := m ^ t;
#     gens := [];
#     for A in GeneratorsOfGroup(H) do
#         generator := A;
#         for i in [1..t - 1] do
#             generator := KroneckerProduct(generator, IdentityMat(m, field));
#         od;
#         Add(gens, generator);
#     od;
# 
#     # TODO
#     # Better check if the following really does what it claims to do
# 
#     # Reverse to be consistent with Magma
#     tensorProductBasis := List(Tuples([1..m], t), Reversed);
#     permuteTensorProductBasisElements := ActionHomomorphism(symt,
#                                                             tensorProductBasis, 
#                                                             Permuted, 
#                                                             "surjective");
#     for permutation in GeneratorsOfGroup(K) do
#         generator := PermutationMat(Image(permuteTensorProductBasisElements,
#                                           permutation), 
#                                     d, field);
#         Add(gens, generator);
#     od;
#     return Group(gens);
# end;

# Construction as in Proposition 10.2 of [2]
BindGlobal("TensorInducedDecompositionStabilizerInSL",
function(m, t, q)
local d, d42, D, C, diag4, generatorsOfHInSL, i, H, E, U, S, x, zeta, mu;
    if not t > 1 or not m > 2 then
        ErrorNoReturn("<t> must be greater than 1 and <m> must be greater than 2 but <t> = ", 
                    t, " and <m> = ", m);
    fi;

    d := m ^ t;
    zeta := PrimitiveElement(GF(q));
    D := DiagonalMat(Concatenation([zeta], List([1..m - 1], i -> zeta ^ 0)));
    C := zeta ^ ((q - 1) / Gcd(q - 1, d)) * IdentityMat(d, GF(q));

    # TODO TODO TODO
    if (m=2) and (t=2) and (q mod 4=1) then
        #  kludge, but not maximal for m=2 anyway
        return Intersection(TensorWreathProduct(GL(m,q),SymmetricGroup(t))
       ,SL(4,q));
    fi;
    if ((t=2) and (m mod 4=2) and (q mod 4=3)) then
        generatorsOfHInSL:=Concatenation(List([1,2],i->KroneckerProduct(SL(m,q).i,One(SL(m,q))))
       ,List([1,2],i->KroneckerProduct(One(SL(m,q)),SL(m,q).i)));
    # TODO TODO TODO
    else
        H := TensorWreathProduct(SL(m, q), SymmetricGroup(t));
        generatorsOfHInSL := [];
        for generator in GeneratorsOfGroup(H) do
            if DeterminantMat(generator) = zeta ^ 0 then
                Add(generatorsOfHInSL, generator);
            else
                #  det = -1 for odd permutation
                if IsOddInt(m) then
                    Add(generatorsOfH, -1 * generator);
                else
                    Assert(1,t=2 and m mod 4=2 and q mod 4=1);
                    diag4:=diag^(QuoInt((q-1),4));
                    #  has fourth root of 1
                    d42:=KroneckerProduct(diag4,One(SL(m,q)));
                    Add(generatorsOfH,(x*d42));
              fi;
            fi;
        od;
    fi;

    U := KroneckerProduct(D, D ^ (-1));
    for i in [3..t] do
        U := KroneckerProduct(U, IdentityMat(m, GF(q)));
    od;
    E := D ^ QuoInt(Gcd(q - 1, d), Gcd(q - 1, m ^ (t - 1)));
    for i in [2..t] do
        E := KroneckerProduct(E, IdentityMat(m, GF(q)));
    od;

    # Write mu = zeta ^ k for some k. We want 
    # zeta ^ Gcd(q - 1, d) = det(mu * I_d) = mu ^ d = zeta ^ (kd), thus 
    # kd = Gcd(q - 1, d) mod (q - 1). Dividing through by Gcd(q - 1, d) gives 
    # k * d / Gcd(q - 1, d) = 1 mod ((q - 1) / Gcd(q - 1, d)) and now 
    # d / Gcd(q - 1, d) is invertible leading to 
    # k = 1 / (d / Gcd(q - 1, d)) mod ((q - 1) / Gcd(q - 1, d)).
    mu := zeta ^ (1 / (d / Gcd(q - 1, d)) mod ((q - 1) / Gcd(q - 1, d)))
    S := mu ^ (- d / (Gcd(q - 1, d / m) * m)) * IdentityMat(d, GF(q));

    return SubgroupContaining(SL(d,q),gens, out,new_diag/s);
end);

