InstallGlobalFunction("SLStabilizerOfSubspace",
function(n, q, k)
    local A5, dirProd, z, transvecDiag, T;
    # Construction as in Proposition 4.1 of [2]
    z := PrimitiveElement(GF(q));
    A5 := DiagonalMat(Concatenation(Concatenation([z], List([2..n - 1], i -> z ^ 0))
     , [z ^ -1]));
    dirProd := MatDirectProduct(SL(n - k, q), SL(k, q));
    transvecDiag := List([1..n], i -> [i, i, 1]);
    T := MatrixByEntries(GF(q), n, n, Concatenation([[1, n - k + 1, 1]], transvecDiag));
    return Group(Concatenation([A5], GeneratorsOfGroup(dirProd), [T]));
end);
