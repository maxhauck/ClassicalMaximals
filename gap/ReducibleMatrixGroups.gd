#! @Chapter Utility Functions
#! @Section Maximal Subgroups
#! @Description
#! Return the subgroup of <M>SL(n, q)</M> stabilizing the
#! <A>k</A>-dimensional subspace of <M>\mathbb{F}_q^n</M> consisting of
#! all vectors whose first <C>n-k</C> entries are zero.
#! @Arguments n, q, k
DeclareGlobalFunction("SLStabilizerOfSubspace");
