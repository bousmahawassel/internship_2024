Require Export Arith.
Require Export Lia.
Require Export Coq.Sorting.Sorted.
Require Export stdpp.sorting.
From Equations Require Export Equations.
From Coq.Program Require Export Equality.
Global Open Scope bool_scope.

Definition A := nat.

Parameter rank_of : A -> nat.

Inductive Tree : Type := Leaf: Tree | Node: Tree -> A -> nat -> Tree -> Tree.

Definition singleton_list (k: A) (r: nat) : Tree := Node Leaf k r Leaf.

Equations elements (t: Tree) : list A :=
  elements Leaf := [];
  elements (Node t1 k r t2) := (elements t1) ++ [k] ++ (elements t2).

Definition occurs (x: A) (t: Tree) := x ∈ elements t.

Notation "x '∈' t" := (occurs x t).
Notation "x '∉' t" := (~(occurs x t)).

Definition delta {X} (b: bool) (x: X) := if b then [x] else [].

Equations occursb_list (x: A) (l: list A) : bool :=
| x, [] => false;
| x, a::l0 with (x =? a), occursb_list x l0 => {
  | true, _ => true;
  | _, true => true;
  | false, false => false;
  }.

Definition occursb (x: A) (t: Tree) := occursb_list x (elements t).

Definition all_smallers (t: Tree) (x: A) := Forall (gt x) (elements t).

Definition all_greaters (t: Tree) (x: A) := Forall (lt x) (elements t).

Notation sorted := (StronglySorted lt).

Definition abr (t: Tree) : Prop := sorted (elements t).

Open Scope stdpp_scope.

Definition list_pairwise (xs ys: list nat) :=
  ∀ x y, x ∈ xs → y ∈ ys → x < y.

Notation "xs '≺' ys" := (list_pairwise xs ys) (at level 80) : stdpp_scope.

Close Scope stdpp_scope.

Definition tree_pairwise t1 t2 := list_pairwise (elements t1) (elements t2).

