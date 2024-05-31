Parameter A : Type.
Parameter lt : A -> A -> Prop.
Notation "x '<' y" := (lt x y).
Parameter lt_antirefl : forall x: A, ~(x < x).
Parameter lt_trans : forall x y z: A, x < y -> y < z -> x < z.

Inductive Tree : Type := Leaf: Tree | Node: Tree -> A -> Tree -> Tree.


Inductive occurs  : A -> Tree -> Prop :=
| is_root: forall r t1 t2, occurs r (Node t1 r t2)
| left_occurs: forall a r t1 t2, occurs a t1 -> occurs a (Node t1 r t2)
| right_occurs: forall a r t1 t2, occurs a t2 -> occurs a (Node t1 r t2)
.

Lemma empty_leaf: forall x: A, ~(occurs x Leaf).
  intros x H. inversion H.
Qed.
