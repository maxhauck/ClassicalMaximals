#! @Chapter Utility Functions
#! @Section Maximal Subgroups
#! @Arguments n, q, t
#! @Description
#! Return the subgroup of <M>SL(n, q)</M> stabilising a
#! decomposition <M>F^n=V_1\oplus V_2\oplus\dots\oplus V_t</M> of <M>F^n</M>,
#! where <C>F := GF(q)</C>, as a direct sum of vector spaces of equal
#! dimensions. Note that this means that <A>t</A> must be a divisor of <A>n</A>.
#! We demand that <A>t</A> be greater than 1.
DeclareGlobalFunction("ImprimitivesMeetSL");
