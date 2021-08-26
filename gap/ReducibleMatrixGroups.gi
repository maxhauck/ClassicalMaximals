DeclareGlobalFunction("SLStabOfKSpace@");

#  
#  * We take the k-space to be (0, \ldots, 0, a_1, \ldots, a_k)

InstallGlobalFunction(SLStabOfKSpace@,
function(n,q,k)
local diag,dir_prod,z,transvec_diag,transvec;

  z:=PrimitiveElement(GF(q));
  diag:=DiagonalMat(Concatenation(Concatenation([z],List([2..n-1],i->1))
   ,[z^-1]));

  dir_prod:=MatDirectProduct(SL(n-k,q),SL(k,q));
  
  transvec_diag:=List([1..n],i->[i,i,1]);
  transvec:=MatrixByEntries(GF(q),n,n,Concatenation([[1,n-k+1,1]],diag));
  
  return Group(Concatenation([diag],GeneratorsOfGroup(dir_prod),[transvec]));
  
end);
