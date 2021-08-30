#! @Chapter Utility Functions
#! @Section Maximal Subgroups
#! @Arguments n, q, t
#! @Description
#! Return the subgroup of $\mathrm{SL}(n, q)$ stabilising a
#! decomposition $\mathbb{F}_q^n=V_1\oplus V_2\oplus\dots\oplus V_t$ 
#! as a direct product where $\mathrm{dim}(V_1)=\mathrm{dim}(V_2)=\dots
#! =\mathrm{dim}(V_t)$. Note that $t$ must be a divisor of $n$.
DeclareGlobalFunction("ImprimitivesMeetSL");
