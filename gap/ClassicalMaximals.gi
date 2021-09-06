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

C1SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local k, result;
    result := [];
    for k in [1..n-1] do
        Add(result, SLStabilizerOfSubspace(n, q, k));
    od;
    return result;
end;

C2SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local t, divisors, result;
    divisors := DivisorsInt(n);
    result := [];
    for t in divisors{[2..Length(divisors)]} do
        if (n > 2 and t = n and q <= 4) or (t = n / 2 and q = 2) then
            continue;
            # not maximal or considered in class C_1 or C_8 by Proposition
            # 2.3.6 of [1]
        fi;
        Add(result, ImprimitivesMeetSL(n, q, t));
    od;
    return result;
end;

C3SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local primeDivisorsOfn, s, result;
    primeDivisorsOfn := PrimeDivisors(n);
    result := [];
    for s in primeDivisorsOfn do
        Add(result, GammaLMeetSL(n, q, s));
    od;
    return result;
end;

C5SubgroupsSpecialLinearGroupGeneric := function(n, q)
    local factorisation, p, e, generatorGLMinusSL, primeDivisorsOfe,
    degreeOfExtension, f, subfieldGroup, numberOfConjugates, result;
    
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GL(n, q).1;
    primeDivisorsOfe := PrimeDivisors(e);

    result := [];
    for degreeOfExtension in primeDivisorsOfe do
        f := QuoInt(e, degreeOfExtension);
        subfieldGroup := SubfieldSL(n, p, e, f);
        numberOfConjugates := Gcd(n, QuoInt(q - 1, p ^ f - 1));
        result := Concatenation(result,
                                ConjugatesInGeneralGroup(subfieldGroup, 
                                                         generatorGLMinusSL, 
                                                         numberOfConjugates));
    od;

    return result;
end;

InstallGlobalFunction(MaximalSubgroupClassRepsSpecialLinearGroup,
function(n, q)
    local maximalSubgroups, primeDivisorsOfe, factorisation, p, e, generatorGLMinusSL, degreeOfExtension, f,
    numberOfConjugates, subfieldGroup;

    maximalSubgroups := [];

    if (n = 2 and q <= 3) then
        Error("SL(2, 2) and SL(2, 3) are soluble");
    fi;
 
    factorisation := PrimePowersInt(q);
    p := factorisation[1];
    e := factorisation[2];
    generatorGLMinusSL := GL(n, q).1;
    
    # Class C1 subgroups ######################################################
    # Cf. Propositions 3.1.2 (n = 2), 3.2.1 (n = 3), 3.3.1 (n = 4), 
    #                  3.4.1 (n = 5), 3.5.1 (n = 6), 3.6.1 (n = 7), 
    #                  3.7.1 (n = 8), 3.8.1 (n = 9), 3.9.1 (n = 10), 
    #                  3.10.1 (n = 11), 3.11.1 (n = 12) in [1]
    maximalSubgroups := Concatenation(maximalSubgroups,
                                      C1SubgroupsSpecialLinearGroupGeneric(n, q));

    # Class C2 subgroups ######################################################
    if not n in [2, 4] then
        # Cf. Propositions 3.2.2. (n = 3), 3.4.2 (n = 5), 
        #                  3.5.2, 3.5.3, 3.5.4 (all n = 6), 3.6.2 (n = 7),
        #                  3.7.2, 3.7.3, 3.7.4 (all n = 8), 3.8.2 (n = 9),
        #                  3.9.2, 3.9.3, 3.9.4 (all n = 10), 3.10.2 (n = 11),
        #                  3.11.2, 3.11.3, 3.11.4, 3.11.5, 3.11.6 (n = 12) in [1]
        # The exceptions mentioned in these propositions are all general
        # exceptions and are dealt with directly in the function
        # C2SubgroupsSpecialLinearGeneric
        maximalSubgroups := Concatenation(maximalSubgroups,
                                          C2SubgroupsSpecialLinearGroupGeneric(n, q));
    elif n = 2 then
        if not q in [5, 7, 9] then
            # Cf. Lemma 3.1.3 in [1]
            Add(maximalSubgroups, ImprimitivesMeetSL(2, q, 2));
            
            # TODO
            # original Magma code also has an exception for n = 2 and q = 11,
            # but this is not in [1]
            # --> talk this over with Sergio!!
        fi;
    else
        # n = 4
        if q >= 7 then
            # Cf. Proposition 3.3.2 in [1]
            Add(maximalSubgroups, ImprimitivesMeetSL(4, q, 4));
        fi;
        if q > 3 then
            # Cf. Proposition 3.3.3 in [1]
            Add(maximalSubgroups, ImprimitivesMeetSL(4, q, 2));
        fi;
    fi;

    # Class C3 subgroups ######################################################
    # Cf. Propositions 3.3.4 (n = 4), 3.4.3 (n = 5), 3.5.5 (n = 6), 
    #                  3.6.3 (n = 7), 3.7.5 (n = 8), 3.8.3 (n = 9),
    #                  3.9.5 (n = 10), 3.10.3 (n = 11), 3.11.7 (n = 12) in [1]
    if not n in [2, 3] then
        Add(maximalSubgroups, C3SubgroupsSpecialLinearGroupGeneric(n, q));
    elif n = 2 then
        if q <> 7 then
            # Cf. Lemma 3.1.4 in [1]
            Add(maximalSubgroups, C3SubgroupsSpecialLinearGroupGeneric(2, q));

            # TODO
            # original Magma code also has an exception for n = 2 and q = 9,
            # but this is not in [1]
            # --> talk this over with Sergio!!
        fi;
    else 
        # n = 3
        if q <> 4 then
            # Cf. Proposition 3.2.3 in [1]
            Add(maximalSubgroups, C3SubgroupsSpecialLinearGroupGeneric(3, q));
        fi;
    fi;

    # Class C5 subgroups ######################################################
    #
    # Cf. Propositions 3.2.4 (n = 3), 3.3.5 (n = 4), 3.4.3 (n = 5), 
    #                  3.5.7 (n = 6), 3.6.3 (n = 7), 3.7.8 (n = 8),
    #                  3.8.4 (n = 9), 3.9.7 (n = 10), 3.10.3 (n = 11),
    #                  3.11.9 (n = 12) in [1]
    if n <> 2 then
        maximalSubgroups := Concatenation(maximalSubgroups,
                                          C5SubgroupsSpecialLinearGroupGeneric(n, q));
    else
        # n = 2
        if  p <> 2 or not IsPrimeInt(e) then
            # Cf. Lemma 3.1.5 in [1]
            maximalSubgroups := Concatenation(maximalSubgroups,
                                              C5SubgroupsSpecialLinearGroupGeneric(2, q));
        fi;
    fi;

    return maximalSubgroups;
end);
