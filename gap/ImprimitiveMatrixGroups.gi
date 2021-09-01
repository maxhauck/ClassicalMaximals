InstallGlobalFunction(ImprimitivesMeetSL, 
function(n, q, t)
local det, E, gens, i, newGen, newGens, wreathProduct, z, m, subgroup;
    Assert(1, (n mod t) = 0);
    Assert(1, t > 1);
    m := QuoInt(n, t);
    # Construction as in Proposition 5.1 of [2]
    wreathProduct := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(wreathProduct);
    # newGens will be analogous to A, B, C, D in [2]
    newGens := [];
    for i in [1..Length(gens)] do
        det := Determinant(gens[i]);
        if IsOne(det) then
            Add(newGens, gens[i]);
        else
            # rescale first column by -1
            newGen := gens[i] * DiagonalMat(Z(q) ^ 0 * Concatenation([-1], List([2..n], i -> 1)));
            Add(newGens, newGen);
        fi;
    od;
    z := PrimitiveElement(GF(q));
    E := DiagonalMat(Concatenation([z], List([2..m], i -> z ^ 0), 
           [z ^ -1], List([m + 2..n], i -> z ^ 0)));
    Add(newGens, E);
    subgroup := Group(newGens);
    SetSize(subgroup, Size(SL(n/t, q))^t*(q-1)^(t-1)*Factorial(t));
    return subgroup;
end);
