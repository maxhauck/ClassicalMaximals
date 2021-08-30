gap> n := 2;; q := 3;; t := 2;;
gap> G := ImprimitivesMeetSL(n, q, t);;
gap> Size(G) = Size(SL(n/t, q))^t*(q-1)^(t-1)*Factorial(t);
true
gap> n := 4;; q := 8;; t := 2;;
gap> G := ImprimitivesMeetSL(n, q, t);;
gap> Size(G) = Size(SL(n/t, q))^t*(q-1)^(t-1)*Factorial(t);
true
gap> n := 6;; q := 5;; t := 3;;
gap> G := ImprimitivesMeetSL(n, q, t);;
gap> Size(G) = Size(SL(n/t, q))^t*(q-1)^(t-1)*Factorial(t);
true
