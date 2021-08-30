InstallGlobalFunction(ImprimitivesMeetSL@, 
function(n, q, t)
local det, detMat, gens, i, newGen, newGens, subgroup, z, m;
    Assert(1, IsPrimePowerInt(q));
    Assert(1, (n mod t)=0);
    Assert(1, t > 1);
    m := QuoInt(n, t);
    subgroup := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(subgroup);
    newGens := [];
    for i in [1..Length(gens)] do
        det := Determinant(gens[i]);
        Assert(1, det=1 or det=-1);
        if det=1 then
          Add(newGens, gens[i]);
        else
          newGen := gens[i]*DiagonalMat(Z(q)^0*Concatenation([-1], List([2..n], i->1)));
          Add(newGens, newGen);
        fi;
    od;
    z := PrimitiveElement(GF(q));
    detMat := DiagonalMat(Concatenation([z], List([2..m], i->z^0), 
           [z^-1], List([m+2..d], i->z^0)));
    Add(newGens, detMat);
    return Group(newGens);
end);
