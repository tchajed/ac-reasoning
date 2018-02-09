Set Implicit Arguments.

Require Import List.

Section NEList.

  Variable A:Type.

  Definition nelist := (A * list A)%type.

  Definition single x : nelist := (x, nil).

  Definition append (l1 l2: nelist) : nelist :=
    let (x, xs) := l1 in
    let (y, ys) := l2 in
    (x, xs ++ cons y ys).

  Definition hd (l:nelist) : A :=
    let (x, _) := l in x.

  Definition tl (l:nelist) : list A :=
    let (_, xs) := l in xs.

End NEList.
