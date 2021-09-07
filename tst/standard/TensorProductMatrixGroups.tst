gap> d1 := 1;; d2 := 2;; q := 2;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 2;; d2 := 3;; q := 2;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 2;; d2 := 3;; q := 3;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 2;; d2 := 3;; q := 4;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 2;; d2 := 3;; q := 5;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 2;; d2 := 3;; q := 7;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 2;; d2 := 4;; q := 3;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 3;; d2 := 4;; q := 2;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 3;; d2 := 4;; q := 3;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 3;; d2 := 4;; q := 4;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> d1 := 4;; d2 := 5;; q := 2;;
gap> G := TensorProductStabilizerInSL(d1, d2, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true