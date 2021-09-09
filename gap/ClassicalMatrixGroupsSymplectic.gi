# Construction as in Proposition 11.1 of [2]
BindGlobal("SymplecticNormalizerInSL",
function(d, q)
local zeta, gcd, A, B, C, D, i, E, result;
    if IsOddInt(d) then
        ErrorNoReturn("<d> must be even but <d> = ", d);
    fi;

    zeta := PrimitiveElement(GF(q));
    A := Sp(d, q).1;
    B := Sp(d, q).2;
    gcd := Gcd(d, q - 1);
    # generates the center of SL(d, q)
    C := zeta ^ QuoInt(q - 1, gcd) * IdentityMat(d, GF(q));

    if IsEvenInt(q) or gcd / 2 = Gcd(q - 1, d / 2) then
        result := Group([A, B, C]);
        # Size according to Table in [1]
        SetSize(result, gcd * Size(PSp(d, q)));
    else
        D := DiagonalMat(Concatenation(List([1..d / 2], i -> zeta),
                                       List([1..d / 2], i -> zeta ^ 0)));
        # solving the congruence d * i = d / 2 mod q - 1 for i
        i := (d / 2) / gcd * (d / gcd) ^ (-1) mod ((q - 1) / gcd);
        E := zeta ^ (-i) * D;
        result := Group([A, B, C, E]);
        # Size according to Table 2.11 in [1]
        # Note that |PCSp(d, q)| = |CSp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)| * |CSp(d, q) : Sp(d, q)| / (q - 1) 
        #                        = |Sp(d, q)|,
        # since |CSp(d, q) : Sp(d, q)| = q - 1 according to Table 1.3 of [1]
        SetSize(result, gcd * Size(Sp(d, q)));
    fi;

    return result;
end);
