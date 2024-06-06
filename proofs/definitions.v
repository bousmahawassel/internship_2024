Require Export Arith.
Require Export Lia.
Require Export Coq.Sorting.Sorted.
Require Export stdpp.sorting.
From Equations Require Export Equations.
Global Open Scope bool_scope.

Definition A := nat.

Parameter rank_of : A -> nat.

Inductive Tree : Type := Leaf: Tree | Node: Tree -> A -> nat -> Tree -> Tree.

Equations elements (t: Tree) : list A :=
  elements Leaf := [];
  elements (Node t1 k r t2) := (elements t1) ++ [k] ++ (elements t2).

Definition occurs (x: A) (t: Tree) := x ∈ elements t.

Notation "x '∈' t" := (occurs x t).
Notation "x '∉' t" := (~(occurs x t)).

Definition all_smallers (t: Tree) (x: A) := forall y, y ∈ t -> y < x.

Definition all_greaters (t: Tree) (x: A) := forall y, y ∈ t -> x < y.

Notation sorted := (StronglySorted lt).

Definition abr (t: Tree) : Prop := sorted (elements t).

Open Scope stdpp_scope.

Definition list_pairwise (xs ys: list nat) :=
  ∀ x y, x ∈ xs → y ∈ ys → x < y.

Notation "xs '≺' ys" := (list_pairwise xs ys) (at level 80) : stdpp_scope.

Close Scope stdpp_scope.

Definition tree_pairwise t1 t2 := list_pairwise (elements t1) (elements t2).

