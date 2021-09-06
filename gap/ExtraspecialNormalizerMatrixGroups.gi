# Construction as in Lemma 9.1 of [2]
OddExtraspecialGroup := function(r, m, q)
    local zeta, omega, X, Y, permutationMatrixEntries, listOfXi, listOfYi;

    if (q - 1) mod r <> 0 or not IsPrime(r) then
        ErrorNoReturn("<r> must be prime and a divisor of <q> - 1 but <r> = ", r,
                      "<q> = ", q);
    fi; 
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

# Construction as in Lemma 9.2 of [2]
OddExtraspecialNormalizerInGL := function(r, m, q)
    local zeta, omega, U, V, W, listOfUi, listOfVi, listOfWi, matrixIndices,
    entriesOfV, w, generatingScalar, result;

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
    else
        listOfWi := [];
    fi;

    generatingScalar := zeta * IdentityMat(r ^ m, GF(q));
    result := OddExtraspecialGroup(r, m, q);
    result.generatingScalar := generatingScalar;
    result.listOfUi := listOfUi;
    result.listOfVi := listOfVi;
    result.listOfWi := listOfWi;
    return result;
end;

# Solving the congruence a ^ 2 + b ^ 2 = -1 mod p by trial and error.
# A solution always exists by a simple counting argument using the pidgeonhole
# principle and the fact that there are (p + 1) / 2 > p / 2 squares mod p.
SolveQuadraticCongruence := function(p)
    local a, b;
    for a in [0..p - 1] do
        b := RootFFE(GF(p), (-1 - a ^ 2) * Z(p) ^ 0, 2);
        if not b = fail then
            break;
        fi;
    od;
    return rec(a := a, b := b);
end;

# Construction as in Lemma 9.3 of [2]
SymplecticTypeNormalizerInGL := function(m, q)
    local listOfUi, U, result, zeta, psi; 

    if (q - 1) mod 4 <> 0 or m < 2 then
        ErrorNoReturn("<q> must be 1 mod 4 and <m> must be at least 2 but <q> = ",
                      q, "<m> = ", m);
    fi;

    result := OddExtraspecialNormalizer(2, m, q);
    
    # In fact, we do not need the matrix Z mentioned in Lemma 9.3: It is only
    # needed as a generator of the symplectic type subgroup of GL(d, q), but
    # not as a generator of its normalizer in GL(d, q) because for the
    # normalizer, we already need a generating scalar, i.e. a scalar matrix of
    # order q - 1 (whereas Z has only order (q - 1) / 4), making Z redundant.

    zeta := PrimitiveElement(GF(q));
    psi := zeta ^ (QuoInt(q - 1, 4));
    U := DiagonalMat([zeta ^ 0, psi]);
    # Determinant psi ^ (2 ^ (m - 1)) = (zeta ^ ((q - 1) / 2)) ^ (2 ^ (m - 2))
    # = (-1) ^ (2 ^ (m - 2)) = 1 if m >= 3 and = -1 if m = 2 (recall m >= 2)
    listOfUi := List([1..m], i ->
    KroneckerProduct(KroneckerProduct(IdentityMat(2 ^ (m - i), GF(q)), U),
    IdentityMat(2 ^ (i - 1), GF(q))));
    
    result.listOfUi := listOfUi;

    return result;
end;

# Construction as in Lemma 9.4 of [2]
Extraspecial2MinusTypeNormalizerInGL := function(m, q)
    local solutionQuadraticCongruence, a, b, kroneckerFactorX1, kroneckerFactorY1, 
    kroneckerFactorU1, kroneckerFactorV1, kroneckerFactorW1, result;

    if (q - 1) mod 2 <> 0 then
        ErrorNoReturn("<q> must be odd but <q> = ", q);
    fi;

    result := OddExtraspecialNormalizer(2, m, q);
   
    p := PrimeDivisors(q)[1];
    solutionQuadraticCongruence := SolveQuadraticCongruence(p);
    a := solutionQuadraticCongruence.a; 
    b := solutionQuadraticCongruence.b;

    # This has determinant 1 by construction of a and b
    kroneckerFactorX1 := Z(q) ^ 0 * [[a, b], [b, -a]];
    # Determinant 1
    kroneckerFactorY1 := Z(q) ^ 0 * [[0, -1], [1, 0]];
    # Determinant 2
    kroneckerFactorU1 := Z(q) ^ 0 * [[1, 1], [-1, 1]];
    # Determinant 4
    kroneckerFactorV1 := Z(q) ^ 0 * [[1 + a + b, 1 - a + b], 
                                     [-1 - a + b, 1 - a - b]];
    if m <> 1 then
        # Determinant 4
        kroneckerFactorW1 := Z(q) ^ 0 * [[1, 0, 1, 0], [0, 1, 0, 1], 
                                         [0, 1, 0, -1], [-1, 0, 1, 0]];
    fi;

    # TODO
    # It seems we don't need the Ui here, but just U1? 
    # --> Check this with the Magma code!
    result.listOfUi := [];
    # Determinant 1
    result.listOfXi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorX1);
    # Determinant 1
    result.listOfYi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorY1);
    # Determinant 2 ^ (2 ^ (m - 1))
    result.listOfUi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorU1);
    # Determinant 4 ^ (2 ^ (m - 1)) = 2 ^ (2 ^ m)
    result.listOfVi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 1), GF(q)),
                                           kroneckerFactorV1);
    if m <> 1 then
        # Determinant 4 ^ (2 ^ (m - 2)) = 2 ^ (2 ^ (m - 1))
        result.listOfWi[1] := KroneckerProduct(IdentityMat(2 ^ (m - 2), GF(q)),
                                               kroneckerFactorW1);
    fi;

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

# Construction as in Proposition 9.5 of [2]
OddExtraspecialNormalizerInSL := function(r, m, q)
    local d, listOfUi, listOfVi, generatorsOfNormalizerInGL, scalarMultiplierUi, 
    scalarMultiplierVi, generators, generatingScalar, result;

    d := r ^ m

    generatorsOfNormalizerInGL := OddExtraspecialNormalizerInGL(r, m, q);
    listOfUi := generatorsOfNormalizerInGL.listOfUi;
    listOfVi := generatorsOfNormalizerInGL.listOfVi;

    # We always need a generating element of Z(SL(d, q))
    generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, r ^ m))) *
    IdentityMat(d, GF(q));

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
                                generatorsOfNormalizerInGL.listOfXi,
                                generatorsOfNormalizerInGL.listOfYi,
                                listOfUi, listOfVi,
                                generatorsOfNormalizerInGL.listOfWi);
    result := Group(generators);
    return result;
    
    # TODO
    # Set size of result
end;

# Construction as in Proposition 9.5 of [2]
SymplecticTypeNormalizerInSL := function(m, q)
    local generatorsOfNormalizerInGL, d, listOfUi, listOfVi, listOfWi,
    generatingScalar, scalarMultiplierVi, scalarMultiplierUiAndWi, p, e, 
    factorization, generators, result;
    
    if (q - 1) mod 4 <> 0 or m < 2 then
        ErrorNoReturn("<q> must be 1 mod 4 and <m> must be at least 2 but <q> = ",
                      q, "<m> = ", m);
    fi;

    d := 2 ^ m;
    # q = p ^ e with p prime
    factorization := PrimePowersInt(q);
    p := factorization[1];
    e := factorization[2];

    generatorsOfNormalizerInGL := SymplecticTypeNormalizerInGL(m, q);
    listOfUi := generatorsOfNormalizerInGL.listOfUi;
    listOfVi := generatorsOfNormalizerInGL.listOfVi;
    listOfWi := generatorsOfNormalizerInGL.listOfWi;

    # We always need a generating element of Z(SL(d, q))
    generatingScalar := zeta ^ (QuoInt(q - 1, Gcd(q - 1, r ^ m))) *
    IdentityMat(d, GF(q));

    # Note that det(Xi) = det(Yi) = 1, so we do not need to rescale these to
    # determinant 1.

    if m >= 3 then
        # If m >= 3, we have det(Wi) = det(Ui) = 1 and we do not have to
        # rescale these matrices to determinant 1. Furthermore, we can always
        # find a d-th root of det(Vi) in the case m >= 3; note that, again
        # det(Vi) is independent of i.

        scalarMultiplierVi := ScalarToNormalizeDeterminant(listOfVi[1], 
                                                           d, GF(q));
        listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);
    
    else
    
        # We first deal with the Ui and Wi
    
        if (q - 1) mod 8 = 0 then
            # This is m = 2 and q = 1 mod 8. Here we have det(Ui) = det(Wi) = -1
            # and we can find d-th roots for det(Ui) and det(Wi).

            scalarMultiplierUiAndWi := ScalarToNormalizeDeterminant(listOfUi[1],
                                                                    d, GF(q));
            listOfUi := List(listOfUi, Ui -> scalarMultiplierUiAndWi * Ui);
            listOfWi := List(listOfWi, Wi -> scalarMultiplierUiAndWi * Wi);
        else
            # Still m = 2 but now q <> 1 mod 8. Now we cannot rescale Wi and Ui to
            # determinant 1 since det(Wi) = det(Ui) = -1 and there are no 8th roots
            # of unity in GF(q).

            # Note that Length(listOfUi) = m = 2, Length(listOfWi) = m - 1 = 1.
            # Taking these two elements instead of the Ui and Wi should work
            # according to the Magma code; in particular, they both have
            # determinant 1.
            listOfUi := [listOfUi[1] ^ (-1) * listOfUi[2]];
            listWi := [listOfUi[1] ^ (-1) * listOfWi[1]];
        fi;

        # Now we deal with the Vi

        # For completeness, we note that p = 3, 7 mod 8 and e odd can
        # technically not occur here: For e odd we have q = p ^ e = p mod 8 
        # (since p is odd and therefore p ^ 2 = 1 mod 8) and we require q = 1 mod 4;
        # hence, we can only have p = 1, 5 mod 8 for e odd.
        if IsEvenInt(e) or (p - 1) mod 8 = 0 or (p - 3) mod 8 = 0 
                                             or (p - 7) mod 8 = 0 then
            # We can still rescale the Vi to determinant 1.

            scalarMultiplierVi := ScalarToNormalizeDeterminant(listOfVi[1],
                                                           d, GF(q));
            listOfVi := List(listOfVi, Vi -> scalarMultiplierVi * Vi);
        else
            # Now we cannot rescale the Vi to determinant 1. 

            # Note that Length(listOfVi) = m = 2. Taking this one element
            # instead of the Vi should work according to the Magma code.
            listOfVi := [listOfVi[1] ^ (-1) * listOfVi[2]];
        fi;
    fi;    

    generators := Concatenation([generatingScalar],
                                generatorsOfNormalizerInGL.listOfXi,
                                generatorsOfNormalizerInGL.listOfYi,
                                listOfUi, listOfVi, listOfWi);
    result := Group(generators);
    return result;

    # TODO
    # Set size of result
end;

# TODO
# It seems really pointless here to do this for anything with m > 1 since the
# intersection of the normalizer with the SL is only relevant in case L for n = 2.
# --> Talk this over with Sergio!!
# --> Sergio approves (yay!) :D
#
# Construction as in Proposition 9.5 of [2]
Extraspecial2MinusTypeNormalizerInSL := function(m, q)
end;
