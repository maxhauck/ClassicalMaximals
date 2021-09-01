gap> n := 4;; p := 2;; e := 4;; f := 2;;
gap> G := SubfieldSL(n, p, e, f);;
gap> Size(G) = Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f - 1), n);
true
gap> n := 2;; p := 3;; e := 6;; f := 2;;
gap> G := SubfieldSL(n, p, e, f);;
gap> Size(G) = Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f - 1), n);
true
gap> n := 3;; p := 7;; e := 3;; f := 1;;
gap> G := SubfieldSL(n, p, e, f);;
gap> Size(G) = Size(SL(n, p ^ f)) * Gcd(QuoInt(p ^ e - 1, p ^ f - 1), n);
true
