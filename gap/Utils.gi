BindGlobal("MatrixByEntries",
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
