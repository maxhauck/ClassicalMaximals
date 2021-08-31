InstallGlobalFunction("SLStabilizerOfSubspace",
function(n, q, k)
    local diag, dirProd, z, transvecDiag, transvec;
    z := PrimitiveElement(GF(q));
    diag := DiagonalMat(Concatenation(Concatenation([z], List([2..n-1], i->z^0))
     , [z^-1]));
    dirProd := MatDirectProduct(SL(n-k, q), SL(k, q));
    transvecDiag := List([1..n], i->[i, i, 1]);
    transvec := MatrixByEntries(GF(q), n, n, Concatenation([[1, n-k+1, 1]], transvecDiag));
    return Group(Concatenation([diag], GeneratorsOfGroup(dirProd), [transvec]));
end);
