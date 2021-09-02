#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# Code along the lines of:
# [1]   J. M. Bray, D. F. Holt, C. M. Roney-Dougal. "The Maximal Subgroups of the
#       Low-Dimensional Finite Classical Groups". Cambridge UP, 2013.
# [2]   D. F. Holt, C. M. Roney-Dougal. "Constructing Maximal Subgroups of
#       Classical Groups." LMS Journal of Computation and Mathematics, vol. 8,
#       2005, pp. 46-79.
#
# Implementations
#

ConjugatesInGeneralGroup := function(S, C, r)
    return List([0..r - 1], i -> S ^ (C ^ i));
end;

InstallGlobalFunction(ClassicalMaximalsGeneric,
function(type, n, q)
    if type = "L" then
        return MaximalSubgroupClassRepsSpecialLinearGroup(n, q);
    fi;

    return 0;
end);

InstallGlobalFunction(MaximalSubgroupClassRepsSpecialLinearGroup,
function(n, q)
    local maximalSubgroups, k, divisors, t, primeDivisorsOfn, primeDivisorsOfe, s, factorisation, p,
    e, generatorGLMinusSL, degreeOfExtension, f, numberOfConjugates,
    subfieldGroup;
    maximalSubgroups := [];

    if (n = 2 and q <= 3) then
        Error("SL_2(2) and SL_2(3) are soluble");
    fi;

    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GL(n, q).1;

    # Class C1 subgroups
    for k in [1..n-1] do
        Add(maximalSubgroups, SLStabilizerOfSubspace(n, q, k));
    od;

    # Class C2 subgroups
    divisors := DivisorsInt(n);
    for t in divisors{[2..Length(divisors)]} do
        if (n > 2 and t = n and q <= 4) or (t = n/2 and q = 2) then
            continue;
            # not maximal or considered in class C_1 or C_8 by Proposition
            # 2.3.6 of [1]
        fi;
        if (n = 2 and q in [5, 7, 9]) or (n = 4 and t = 4 and q = 5) or (n = 4
        and t = 2 and q = 3) then
            continue;
            # more small exceptions

            # TODO
            # original Magma code also has an exception for n = 2 and q = 11,
            # but this is not in [1]
            # --> talk this over with Sergio!!
        fi;
        Add(maximalSubgroups, ImprimitivesMeetSL(n, q, t));
    od;

    # Class C3 subgroups
    primeDivisorsOfn := PrimeDivisors(n);
    for s in primeDivisorsOfn do
        if (n = 2 and q = 7) or (n = 3 and q = 4) then
            continue;
            # small exceptions

            # TODO
            # original Magma code also has an exception for n = 2 and q = 9,
            # but this is not in [1]
            # --> talk this over with Sergio!!
        fi;
        Add(maximalSubgroups, GammaLMeetSL(n, q, s));
    od;

    # Class C5 subgroups
    primeDivisorsOfe := PrimeDivisors(e);
    for degreeOfExtension in primeDivisorsOfe do
        f := QuoInt(e, degreeOfExtension);
        if n = 2 and p = 2 and f = 1 then
            continue;
            # small exceptions
        fi;
        subfieldGroup := SubfieldSL(n, p, e, f);
        numberOfConjugates := Gcd(n, QuoInt(q - 1, p ^ f - 1));
        maximalSubgroups := Concatenation(maximalSubgroups,
        ConjugatesInGeneralGroup(subfieldGroup, generatorGLMinusSL, numberOfConjugates));
    od;

    return maximalSubgroups;
end);
