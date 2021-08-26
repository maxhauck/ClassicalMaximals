DeclareGlobalFunction("SLStabOfKSpace@");

DeclareGlobalFunction("SLStabOfKSpaceMissDual@");

#  
#  * We take the k-space to be (0, \ldots, 0, a_1, \ldots, a_k) and
#  * the (n-k)-space to be (a_1, \ldots, a_n-k, 0, \ldots, 0)

InstallGlobalFunction(SLStabOfKSpaceMissDual@,
function(n,q,k)
local diag1,diag2,dir_prod,z,general;
  general:=ValueOption("general");
  if general=fail then
    general:=false;
  fi;
  z:=PrimitiveElement(GF(q));
  diag1:=DiagonalMat(Concatenation(Concatenation([z],List([2..n-1],i->1))
   ,[z^-1]));
  diag2:=DiagonalMat(Concatenation([z],List([2..n],i->1)));

  dir_prod:=MatDirectProduct(SL(n-k,q),SL(k,q));
  if general then
    return Group(Concatenation([diag1,diag2],GeneratorsOfGroup(dir_prod)));
  fi;
  return Group(Concatenation([diag1],GeneratorsOfGroup(dir_prod)));
  
end);

#  
#  * We take the k-space to be (0, \ldots, 0, a_1, \ldots, a_k)

InstallGlobalFunction(SLStabOfKSpace@,
function(n,q,k)
local diag,grp,transvec;
  diag:=List([1..n],i->[i,i,1]);
  grp:=SLStabOfNSpaceMissDual@(n,q,k);
  transvec:=MatrixByEntries(GF(q),n,n,Concatenation([[1,n-k+1,1]],diag));
  return Group(Concatenation(GeneratorsOfGroup(grp),[transvec]));
  
end);
