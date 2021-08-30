gap> n := 4;; q := 3;; k := 2;;
gap> G := SLStabilizerOfSubspace(n, q, k);;
gap> Size(G) = q ^ (k * (n-k)) * Size(SL(k, q)) * Size(SL(n-k, q)) * (q-1);
true
gap> n := 3;; q := 8;; k := 2;;
gap> G:=SLStabilizerOfSubspace(n, q, k);;
gap> Size(G) = q ^ (k * (n-k)) * Size(SL(k, q)) * Size(SL(n-k, q)) * (q-1);
true
gap> n := 2;; q := 7;; k := 1;;
gap> G:=SLStabilizerOfSubspace(n, q, k);;
gap> Size(G) = q ^ (k * (n-k)) * Size(SL(k, q)) * Size(SL(n-k, q)) * (q-1);
true
