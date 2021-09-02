#! @Chapter Utility Functions
#! @Section Maximal Subgroups
#! @Arguments s, q
#! @Description
#! Return a subgroup of <M>GL(s, q)</M> isomorphic to the group <M>\Gamma L(1,
#! q ^ s)</M> of semilinear transformations of the vector space <M>F'^1</M>
#! over the field <C>F' := GF(q ^ s)</C>. See <Ref Func="GammaLMeetSL"/> for
#! further details.
DeclareGlobalFunction("GammaLDimension1");

#! @Chapter Utility Functions
#! @Section Maximal Subgroups
#! @Arguments n, q, s
#! @Description
#! Return the subgroup of <M>SL(n, q)</M> induced by the group of semilinear
#! transformations of the vector space <M>F'^m</M> over the field 
#! <C>F' := GF(q ^ s)</C>, where <M>m := n / s</M>. (More precisely, there is
#! an isomorphism of <M>F</M>-vector spaces, where <C>F := GF(q)</C>, between
#! <M>F'</M> and <M>F ^ s</M>, which in turn induces an <M>F</M>-vector space
#! isomorphism between <M>F'^m</M> and <M>F^n</M> and consequently an embedding
#! of <M>\Gamma L(m, q ^ s)</M> into <M>GL(n, q)</M>; the intersection of the
#! image of this embedding with <M>SL(n, q)</M> is a subgroup of <M>SL(n,
#! q)</M>.) Note that this means <A>s</A> must be a divisor of <A>n</A>. We
#! further demand that <A>s</A> be a prime number, i.e. <M>F'</M> is a prime
#! extension of <M>F</M>.
DeclareGlobalFunction("GammaLMeetSL");
