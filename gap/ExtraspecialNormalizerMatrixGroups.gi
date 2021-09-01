InstallGlobalFunction(OddExtraSpecialGroup,
function(r, q, m)
    local zeta, omega, X, Y, permutationMatrixEntries, listOfXi, listOfYi, generators;
    Assert(1, IsOdd(r));
    Assert(1, (q - 1) mod p = 0); 
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
    return Group(generators);
end);

InstallGlobalFunction(OddExtraSpecialNormaliser,
function(r, q, m)
end);
