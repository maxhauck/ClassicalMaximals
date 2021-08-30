InstallGlobalFunction(ImprimitivesMeetSL, 
function(n, q, t)
local det, E, gens, i, newGen, newGens, subgroup, z, m;
    Assert(1, IsPrimePowerInt(q));
    Assert(1, (n mod t)=0);
    Assert(1, t > 1);
    m := QuoInt(n, t);
    subgroup := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(subgroup);
    newGens := [];
    for i in [1..Length(gens)] do
        det := Determinant(gens[i]);
        if det=1 then
            Add(newGens, gens[i]);
        else
            #rescale first column by -1
            newGen := gens[i]*DiagonalMat(Z(q)^0*Concatenation([-1], List([2..n], i->1)));
            Add(newGens, newGen);
        fi;
    od;
    z := PrimitiveElement(GF(q));
    E := DiagonalMat(Concatenation([z], List([2..m], i->z^0), 
           [z^-1], List([m+2..d], i->z^0)));
    Add(newGens, E);
    return Group(newGens);
end);
