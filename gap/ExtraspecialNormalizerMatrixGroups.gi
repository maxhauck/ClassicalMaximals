OddExtraspecialGroup := function(r, m, q)
    local zeta, omega, X, Y, permutationMatrixEntries, listOfXi, listOfYi,
    generators, result;
    Assert(1, r mod 2 = 1);
    Assert(1, (q - 1) mod r = 0); 
    # Construction as in Lemma 9.1 of [2]
    zeta := PrimitiveElement(GF(q));
    omega := zeta ^ (QuoInt(q - 1, r));
    X := DiagonalMat(List([0..r - 1], i -> omega ^ i));
    permutationMatrixEntries := Concatenation(List([1..r - 1], i -> [i, i+1,
    zeta ^ 0]), [r, 1, zeta ^ 0]);
    Y := MatrixByEntries(GF(q), r, r, permutationMatrixEntries);

    listOfXi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), GF(q)), X),
    IdentityMat(r ^ (i - 1), GF(q))));
    listOfYi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), GF(q)), Y),
    IdentityMat(r ^ (i - 1), GF(q))));
    generators := Concatenation(listOfXi, listOfYi);

    result := GroupWithGenerators(generators);
    SetSize(result, r ^ (1 + 2 * m));
    return result;
end;

OddExtraspecialNormalizer := function(r, m, q)
    local zeta, omega, U, V, W, listOfUi, listOfVi, listOfWi, matrixIndices,
    entriesOfV, w, generatingScalar, generators, result;
    # Construction as in Lemma 9.2 of [2]
    zeta := PrimitiveElement(GF(q));
    omega := zeta ^ (QuoInt(q - 1, r));
    U := DiagonalMat(List([1..r], i -> omega ^ (i * (i - 1) / 2)));
    matrixIndices := Concatenation(List([1..r], i -> List([1..r], j -> [i,
    j])));
    entriesOfV := List(matrixIndices, index -> Concatenation(index, [omega ^
    ((index[1] - 1) * (index[2] - 1))]));
    V := MatrixByEntries(GF(q), r, r, entriesOfV);

    listOfUi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), GF(q)), U),
    IdentityMat(r ^ (i - 1), GF(q))));
    listOfVi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - i), GF(q)), V),
    IdentityMat(r ^ (i - 1), GF(q))));

    w := PermList(List([1..r ^ 2 - 1], a -> (a + ((a - 1) mod r) * r) mod r ^
    2));
    W := PermutationMat(w);
    listOfWi := List([1..m - 1], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - 1 - i), GF(q)), W),
    IdentityMat(r ^ (i - 1), GF(q))));

    generatingScalar := zeta * IdentityMat(r ^ m, GF(q));
    generators := Concatenation([generatingScalar],
    GeneratorsOfGroup(OddExtraspecialGroup), listOfUi, listOfVi, listOfWi);
    result := GroupWithGenerators(generators);
    # TODO
    # I would set the size of the group here, but to which value??
    return result;
end;

InstallGlobalFunction("ExtraspecialNormalizerMeetSL"
function(r, m, q)
    local listOfUi, listOfVi, listOfWi, generatorsOfNormalizerInGL,
    generatorsOfExtraspecialGroup, scalarMultiplierUi, scalarMultiplierVi,
    scalarMultiplierWi, generators, generatingScalar;
    # Construction as in Proposition 9.5 of [2]
    if r mod 2 = 1 then
        generatorsOfNormalizerInGL :=
        GeneratorsOfGroup(OddExtraspecialNormalizer(r, m, q));
        # These are the Xi and Yi
        generatorsOfExtraspecialGroup := generatorsOfNormalizerInGL[{2..2 * m +
        1}];
        listOfUi := generatorsOfNormalizerInGL[{2 * m + 2..3 * m + 1}];
        listOfVi := generatorsOfNormalizerInGL[{3 * m + 2..4 * m + 1}];
        listOfWi := generatorsOfNormalizerInGL[{4 * m + 2..5 * m}];

        if r ^ m <> 3 then
            # Let G denote the normalizer of the extraspecial group r ^ (1 + 2 * m)
            # in GL(d, q), where d = r ^ m. Then, according to the proof of
            # Proposition 9.5 of [2], we have G = (G intersect SL(d, q))Z(G) in
            # the present case of d <> 3, which means precisely that we can
            # multiply each element of G by a scalar matrix in such a way that
            # the result has determinant 1. In particular, all of the
            # determinants of the generators Ui, Vi, Wi of G have a dth root in
            # GF(q). Note that det(Xi) = det(Yi) = 1 already and that, by
            # construction, det(Ui), det(Vi) and det(Wi) are independent of i
            # so that, in fact, we only have to compute three dth roots in
            # GF(q) (that is, the dth roots of det(U1), det(V1) and det(W1)).
            scalarMultiplierUi := RootFFE(GF(q), Determinant(listOfUi[1]), d) ^
            -1; 
            scalarMultiplierVi := RootFFE(GF(q), Determinant(listOfVi[1]), d) ^
            -1;
            scalarMultiplierWi := RootFFE(GF(q), Determinant(listOfWi[1]), d) ^
            -1;
            listOfUi := List(listOfUi, Ui -> scalarMultiplierUi * Ui);
            listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);
            listOfWi := List(listOfWi, Wi -> scalarMultiplierWi * Wi);

            # Finally, we need a generating element of Z(SL(d, q))
            generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, r ^ m))) *
            IdentityMat(r ^ m, GF(q));

            generators := Concatenation
        fi;
    fi;
end);
