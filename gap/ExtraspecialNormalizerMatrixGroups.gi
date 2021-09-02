OddExtraSpecialGroup := function(r, q, m)
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

OddExtraSpecialNormalizer := function(r, q, m)
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
    GeneratorsOfGroup(OddExtraSpecialGroup), listOfUi, listOfVi, listOfWi);
    result := GroupWithGenerators(generators);
    # TODO
    # I would set the size of the group here, but to which value??
    return result;
end;
