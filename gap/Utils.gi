InstallGlobalFunction("MatrixByEntries",
function(field, nrRows, nrCols, entries)
    local i, m, o;
    o := One(field);
    if ForAll(entries, x -> IsList(x) and Length(x)=3) then
        m := NullMat(nrRows, nrCols, field);
        for i in entries do
            m[i[1]][i[2]] := i[3]*o;
        od;
    else
        if nrCols*nrRows<>Length(entries) then
            Error("the list <entries> should have length <nrRows> * <nrCols> = ", nrRows*nrCols, "but has length", Length(entries));
        fi;
        m := List([1..nrRows], x -> entries{[1+nrCols*(x-1)..nrCols*x]}*o);
    fi;

    if IsFFECollection(field) then
        m := ImmutableMatrix(field, m);
    fi;
    return m;
end);

InstallGlobalFunction("ChangeFixedSesquilinearForm",
function(group, gramMatrix)
    local gapForm, newForm, gapToCanonical, canonicalToNew, field;
    gapForm := PreservedSesquilinearForms(group)[1];
    field := BaseField(gapForm);
    if IsBilinearForm(gapForm) then
        newForm := BilinearFormByMatrix(gramMatrix);
    elif IsHermitianForm(gapForm) then
        newForm := HermitianFormByMatrix(gramMatrix);
    fi;
    # the following if condition can only ever be fulfilled if <group> is an
    # orthogonal group; there the case of even dimension is problematic since,
    # in that case, there are two similarity classes of bilinear forms
    if not IsometricCanonicalForm(gapForm) = IsometricCanonicalForm(newForm)
       and IsEvenInt(DimensionOfMatrixGroup(group)) then
       ErrorNoReturn("The form preserved by <group> must be similar to the form", 
                     "described by the Gram matrix <gramMatrix>.");
    fi;
    gapToCanonical := BaseChangeHomomorphism(BaseChangeToCanonical(gapForm), 
                                             field);
    canonicalToNew := BaseChangeHomomorphism(BaseChangeToCanonical(newForm) ^ (-1), 
                                             field);
    return Group(canonicalToNew(gapToCanonical(GeneratorsOfGroup(group))));
end);

InstallGlobalFunction("AntidiagonalMat",
function(entries, field)
    local dimension;
    dimension := Length(entries);
    return MatrixByEntries(field, dimension, dimension, 
                           List([1..dimension], i -> [i, dimension - i + 1, entries[i]]));
end);


