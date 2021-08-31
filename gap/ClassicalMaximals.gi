#
# ClassicalMaximals: Maximal subgroups of classical groups
#
# Implementations
#
InstallGlobalFunction(ClassicalMaximalsGeneric,
function(type, n, q)
    if type = "L" then
        return MaximalSubgroupClassRepsSpecialLinearGroup(n, q);
    fi;

    return 0;
end);

InstallGlobalFunction(MaximalSubgroupClassRepsSpecialLinearGroup,
function(n, q)
    local maximalSubgroups, k, divisors, t;
    maximalSubgroups := [];

    if (n = 2 and q <= 3) then
        Error("SL_2(2) and SL_2(3) are soluble")
    fi;

    # class C1 subgroups
    for k in [1..n-1] do
        Add(maximalSubgroups, SLStabilizerOfSubspace(n, q, k));
    od;

    # class C2 subgroups
    divisors := DivisorsInt(n);
    for t in divisors{[2..Length(divisors)]} do
        if (n > 2 and t = n and q <= 4) or (t = n/2 and q = 2) then
            continue;
            # not maximal or considered in class C_1 or C_8 by Proposition 2.3.6
        fi;
        if (n = 2 and q in [5, 7, 9]) or (n = 4 and t = 4 and q = 5) or (n = 4
        and t = 2 and q = 3) then
            continue;
            # more small exceptions
        fi;
        Add(maximalSubgroups, ImprimitivesMeetSL(n, q, t));
    od;

    return maximalSubgroups;
end);
