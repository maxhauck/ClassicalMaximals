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
#     # Reverse to be consistent with Magma
#     tensorProductBasis := List(Tuples([1..m], t), Reversed);
#     permuteTensorProductBasisElements := ActionHomomorphism(symt,
#                                                             tensorProductBasis, 
#                                                             Permuted, 
#                                                             "surjective");
#     
#     
#     for permutation in GeneratorsOfGroup(K) do
#         generator := PermutationMat(Image(permuteTensorProductBasisElements,
#                                           permutation), 
#                                     d, field);
#         Add(gens, generator);
#     od;
#     return Group(gens);
# end;


######################## WORKING OUT FOR LEFTOVER CASE BELOW ##################
#
#     Working with the construction of TensorWreathProduct(SL(m, q), Sym(t)) 
#     from the function above, we have:
#
#     psi : Sym(t) --> Sym(m ^ t)
#     PermutationMat : Sym(m ^ t) --> GL(m ^ t, q)
#     GeneratorsOfGroup(K) = {(1, 2), (1, 2, 3, ..., t)}
#
#     psi((1, 2)) is a product of m * (m - 1) / 2 * m ^ (t - 2) cycles of length 2 
#     (for any two different a1, a2 in [1..m] and any a3, ..., at in [1..m] the 
#     tuples [a1, a2, ..., at] and [a2, a1, ..., at] are swapped). Therefore 
#     det(PermutationMat(phi((1, 2)))) = sign(psi((1, 2))) 
#                                      = (-1) ^ ((m * (m - 1)) / 2 * m ^ (t - 2)) 
#     For m even, this is -1 if and only if m = 2 mod 4 and t = 2.
#
#     Let A_d be the number of t-tuples from [1..m] that can be divided into d
#     equal blocks. Then A_d = m ^ (t / d) if d | t and 0 otherwise. Now let B_e 
#     be the number of t-tuples from [1..m] that can be divided into e and not 
#     more equal blocks. We have A_d = sum_{d | e} B_e for d | t. Hence
#
#               m ^ (t / d) = sum_{d | e} B_e.
#
#     Swap d and t / d as well as e and t / e, obtain
#
#               m ^ d = sum_{t / d | t / e} B_{t / e} = sum_{e | d} B_{t / e}.
#
#     Applying the Mobius inversion formula
#
#               B_{t / d} = sum_{e | d} mu(d / e) * m ^ e = 0 mod 2
#
#     since m is even for all d. But decomposing psi((1, 2, ..., t)) into a
#     product of cycles gives exactly B_{t / d} cycles of length d. Therefore
#     det(PermutationMat(phi((1, 2, ..., t)))) = sign(psi((1, 2, ..., t)))
#                                              = 1.
#
#     Conclusion: If m is even and we have a generator of determinant -1, then
#     t = 2 and m = 2 mod 4. 
#
###############################################################################     


# Construction as in Proposition 10.2 of [2]
BindGlobal("TensorInducedDecompositionStabilizerInSL",
function(m, t, q)
    local gensOfSLm, I, D, C, generatorsOfHInSL, gens, i, H, E, U, S, zeta, mu,
    result, scalingMatrix, d, generator;
    if not t > 1 or not m > 2 then
        ErrorNoReturn("<t> must be greater than 1 and <m> must be greater than 2 but <t> = ", 
                      t, " and <m> = ", m);
    fi;

    d := m ^ t;
    zeta := PrimitiveElement(GF(q));
    D := DiagonalMat(Concatenation([zeta], List([1..m - 1], i -> zeta ^ 0)));
    C := zeta ^ ((q - 1) / Gcd(q - 1, d)) * IdentityMat(d, GF(q));

    if t = 2 and m mod 4 = 2 and q mod 4 = 3 then
        gensOfSLm := GeneratorsOfGroup(SL(m, q));
        I := IdentityMat(m, GF(q));
        # Let Z = Z(SL(d, q)). Then these generate the group 
        # Z.(SL(m, q) o SL(m, q)) (to see this, realize the first factor of the
        # central product as all Kronecker Products I * M with M in SL(m, q)
        # and, similarly, the second factor as the Kronecker Products M * I).
        generatorsOfHInSL := [KroneckerProduct(gensOfSLm[1], I),
                              KroneckerProduct(gensOfSLm[2], I),
                              KroneckerProduct(I, gensOfSLm[1]),
                              KroneckerProduct(I, gensOfSLm[2])];
    else
        H := TensorWreathProduct(SL(m, q), SymmetricGroup(t));
        generatorsOfHInSL := [];
        for generator in GeneratorsOfGroup(H) do
            if DeterminantMat(generator) = zeta ^ 0 then
                Add(generatorsOfHInSL, generator);
            else
                # det = -1 for odd permutation
                if IsOddInt(m) then
                    Add(generatorsOfHInSL, -1 * generator);
                else
                    # In this case, we have t = 2, m = 2 mod 4 and q = 1 mod 4
                    # (see working out above).
                    #
                    # TODO
                    # --> Ask Sergio in how much detail to explain this

                    # This has determinant ((det D) ^ ((q - 1) / 4)) ^ m 
                    # = (zeta ^ ((q - 1) / 4)) ^ m, which, using m even,
                    # becomes (zeta ^ ((q - 1) / 2)) ^ (m / 2) = (-1) ^ (m / 2)
                    # and this is -1 due to m = 2 mod 4.
                    scalingMatrix := KroneckerProduct(D ^ QuoInt(q - 1, 4), 
                                                      IdentityMat(m, GF(q)));
                    # det(generator * scalingMatrix) = -1 * (-1) = 1
                    Add(generatorsOfHInSL,(generator * scalingMatrix));
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
    mu := zeta ^ (1 / (d / Gcd(q - 1, d)) mod ((q - 1) / Gcd(q - 1, d)));
    S := mu ^ (- d / (Gcd(q - 1, d / m) * m)) * IdentityMat(d, GF(q));

    gens := Concatenation(generatorsOfHInSL, [C, U, S * E]);
    result := Group(gens);
    return result;
end);

