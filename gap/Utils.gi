BindGlobal("MatrixByEntries",
	function(f,nr,nc,entries)
    local i, m, o;
	# TODO: proper argument checks
	if ForAll(entries,x->IsList(x) and Length(x)=3) then
		m:=NullMat(nr,nc,f);
		o:=One(f);
		for i in entries do
			m[i[1]][i[2]]:=i[3]*o;
		od;
	else
		if nr*nc<>Length(entries) then
			Error("format?");
		fi;
		m:=List([1..nr],x->entries{[1+nc*(x-1)..nc*x]}*o);
	fi;

	if IsFFECollection(f) then
		m:=ImmutableMatrix(f,m);
	fi;
	return m;
end);
