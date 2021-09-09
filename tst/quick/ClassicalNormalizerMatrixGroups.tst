gap> n := 4;; q := 3;;
gap> G := SymplecticNormalizerInSL(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 5;;
gap> G := SymplecticNormalizerInSL(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 6;; q := 4;;
gap> G := SymplecticNormalizerInSL(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 9;;
gap> G := UnitaryNormalizerInSL(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 3;; q := 9;;
gap> G := UnitaryNormalizerInSL(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> n := 4;; q := 4;;
gap> G := UnitaryNormalizerInSL(n, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true