OddExtraspecialGroup := function(r, m, q)
    local zeta, omega, X, Y, permutationMatrixEntries, listOfXi, listOfYi;
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

    return rec(listOfXi := listOfXi, listOfYi := listOfYi);
end;

OddExtraspecialNormalizer := function(r, m, q)
    local zeta, omega, U, V, W, listOfUi, listOfVi, listOfWi, matrixIndices,
    entriesOfV, w, generatingScalar, result;
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

    if m <> 1 then
        # If m = 1 then we cannot have the Wi as generators since W is in 
        # GL(r ^ 2, q) (i.e. too large)

        w := PermList(List([1..r ^ 2 - 1], 
                           a -> (a + ((a - 1) mod r) * r) mod r ^2));
        W := PermutationMat(w);
        listOfWi := List([1..m - 1], 
                         i -> KroneckerProduct(KroneckerProduct(IdentityMat(r ^ (m - 1 - i), 
                                                                            GF(q)), 
                                               W), IdentityMat(r ^ (i - 1), GF(q))));
    fi;

    generatingScalar := zeta * IdentityMat(r ^ m, GF(q));
    result := OddExtraspecialGroup;
    result.generatingScalar := generatingScalar;
    result.listOfUi := listOfUi;
    result.listOfVi := listOfVi;
    result.listOfWi := listOfWi;
    return result;
end;

ScalarToNormalizeDeterminant := function(matrix, sizeOfMatrix, field)
    local scalar;
    scalar := RootFFE(field, Determinant(matrix), sizeOfMatrix);
    if scalar = fail then
        return fail;
    else
        return scalar ^ -1;
    fi;
end;

InstallGlobalFunction(ExtraspecialNormalizerMeetSL,
function(r, m, q)
    local d, listOfUi, listOfVi, listOfWi, generatorsOfNormalizerInGL,
    generatorsOfExtraspecialGroup, scalarMultiplierUi, scalarMultiplierVi,
    scalarMultiplierWi, generators, generatingScalar;

    # Construction as in Proposition 9.5 of [2]
    d := r ^ m

    if r mod 2 = 1 then
        generatorsOfNormalizerInGL := OddExtraspecialNormalizer(r, m, q);
        # These are the Xi and Yi
        generatorsOfExtraspecialGroup := Concatenation(generatorsOfNormalizerInGL.listOfXi,
                                                       generatorsOfNormalizerInGL.listOfYi);
        listOfUi := generatorsOfNormalizerInGL.listOfUi;
        listOfVi := generatorsOfNormalizerInGL.listOfVi;
        listOfWi := generatorsOfNormalizerInGL.listOfWi;

        # We always need a generating element of Z(SL(d, q))
        generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, r ^ m))) *
        IdentityMat(r ^ m, GF(q));


        # Note that not only det(Xi) = det(Yi) = 1, but as d is odd we
        # also have det(Wi) = 1, so these do not have to be rescaled to
        # determinant 1. However, we do not necessarily have det(Vi) = 1, but
        # in the case d odd, we can always rescale Vi to determinant 1 by
        # finding a d-th root of det(Vi) in GF(q) (which exists!). We can save
        # computations by observing that det(Vi) is independent of i and thus
        # we only need to compute one d-th root.

        scalarMultiplierVi := ScalarToNormalizeDeterminant(listOfVi[1], 
                                                           d, GF(q));
        listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);

        if d = 3 then
            # In the case d <> 3 and d odd, we have det(Ui) = 1 and therefore
            # we do not need to rescale Ui to determinant 1.    
            # If d = 3, we can find a d-th root in GF(q) for det(Ui) if and
            # only if r ^ 2 | q - 1. If not, we append U1 ^ -1 * V1 * U1 
            # instead of U1 (note that m = 1) to the generating set (where V1 
            # is already normalized to determinant 1).

            if (q - 1) mod (r ^ 2) = 0 then
                # We can find a d-th root of det(Ui) = omega in GF(q)

                scalarMultiplierUi := ScalarToNormalizeDeterminant(listOfUi[1],
                                                                   d, GF(q));
                listOfUi := List(listOfUi, Ui -> scalarMultiplierUi * Ui);
            else
                # Note that Length(listOfUi) = m = 1 here and use 
                # U1 ^ -1 * V1 * U1 instead of U1

                listOfUi := [listOfUi[1] ^ -1 * listOfVi[1] * listOfUi[1]];
            fi;
        fi;

        generators := Concatenation([generatingScalar],
                                    generatorsOfExtraspecialGroup, 
                                    listOfUi, listOfVi, listOfWi);
    fi;
end);
