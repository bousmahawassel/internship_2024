Require Export Arith.
Require Export Lia.
Open Scope bool_scope.

(*Parameter A : Type.
Parameter lt : A -> A -> Prop.
Parameter ltb : A -> A -> bool.
Parameter eqb: A -> A -> bool.
Parameter rank_of : A -> A.
Notation "x '<' y" := (lt x y).
Notation "x '<?' y" := (ltb x y) (at level 30, no associativity).
Notation "x '=?' y" := (eqb x y) (at level 30, no associativity).
Axiom lt_antirefl : forall x: A, ~(x < x).
Axiom lt_trans : forall x y z: A, x < y -> y < z -> x < z.
Axiom lt_ltb : forall x y: A, x < y <-> x <? y = true.
Axiom eq_eqb : forall x y: A, x = y <-> x =? y = true.*)

Definition A := nat.

Parameter rank_of : A -> nat.

Lemma couple_to_fst_snd : forall {A B} {a: A} {b: B} {p}, (a, b) = p -> a = fst p /\ b = snd p.
  intros. rewrite <- H. simpl. auto.
Qed.

Lemma opti_tricho : forall {a b}, false = (a =? b) -> false = (a <? b) -> b < a.
Proof.
  intros. apply eq_sym in H, H0. apply Nat.eqb_neq in H. apply Nat.ltb_nlt in H0.
  destruct (Nat.lt_trichotomy a b); try contradiction. destruct H1; try contradiction.
  auto.
Qed.

Inductive Tree : Type := Leaf: Tree | Node: Tree -> A -> nat -> Tree -> Tree.


Inductive occurs  : A -> Tree -> Prop :=
| is_root: forall k r t1 t2, occurs k (Node t1 k r t2)
| left_occurs: forall a k r t1 t2, occurs a t1 -> occurs a (Node t1 k r t2)
| right_occurs: forall a k r t1 t2, occurs a t2 -> occurs a (Node t1 k r t2)
.

Lemma empty_leaf: forall x: A, ~(occurs x Leaf).
  intros x H. inversion H.
Qed.

Definition is_higher_rank (r1: nat) (k1: A) (r2: nat) (k2 : A) : bool :=
  (r2 <? r1) || ((r1 =? r2) && (k1 <? k2)).

Fixpoint unzip (t: Tree) (k: A) {struct t} : Tree * Tree :=
  match t with
  | Leaf => (Leaf, Leaf)
  | Node t1 kt r t2 => if k =? kt then (t1, t2) else
                        if k <? kt then let (st1, gt1) := unzip t1 k in (st1, Node gt1 kt r t2) else
                          let (st2, gt2) := unzip t2 k in (Node t1 kt r st2, gt2)
  end.

Fixpoint down (t: Tree) (k: A) (r: nat) {struct t} : Tree :=
  match t with
  | Node t1 kt rt t2 =>
      if is_higher_rank rt kt r k then
        if kt <? k then Node t1 kt rt (down t2 k r) else Node (down t1 k r) kt rt t2
      else let (st, gt) := unzip t k in Node st k r gt
  | Leaf => let (st, gt) := unzip t k in Node st k r gt
  end.

Definition insert (t: Tree) (k: nat) : Tree := down t k (rank_of k).

Inductive all_smallers : Tree -> A -> Prop :=
| leaf_smallers : forall x: A, all_smallers Leaf x
| rec_smallers : forall t1 t2 k r x, k < x -> all_smallers t1 x -> all_smallers t2 x -> all_smallers (Node t1 k r t2) x.

Lemma occurs_smallers : forall t x, (forall y, occurs y t -> y < x) <-> all_smallers t x.
Proof.
  intros t x. split.
  - induction t; auto using occurs, all_smallers.
  - intro. induction H.
    + intros. exfalso. apply (empty_leaf y). auto.
    + intros. inversion H2; subst; eauto.
Qed.

Lemma smaller_trans : forall t x y, all_smallers t x -> x < y -> all_smallers t y.
Proof.
  intros t x y H H0. induction H; eauto using all_smallers, Nat.lt_trans.
Qed.


Inductive all_greaters  : Tree -> A -> Prop :=
| leaf_greaters : forall x: A, all_greaters Leaf x
| rec_greaters : forall t1 t2 k r x, x < k -> all_greaters t1 x -> all_greaters t2 x -> all_greaters (Node t1 k r t2) x.

Lemma occurs_greaters : forall t x, (forall y, occurs y t -> x < y) <-> all_greaters t x.
Proof.
  intros t x. split.
  - induction t; auto using occurs, all_greaters.
  - intro. induction H.
    + intros. exfalso. eapply empty_leaf. eauto.
    + intros. inversion H2; subst; eauto.
Qed.

Lemma greaters_trans : forall t x y, all_greaters t x -> y < x -> all_greaters t y.
Proof.
  intros t x y H H0. induction H; eauto using all_greaters, Nat.lt_trans.
Qed.

Inductive abr : Tree -> Prop :=
| leaf_abr : abr Leaf
| rec_abr : forall t1 r k t2, abr t1 -> abr t2 -> all_smallers t1 k -> all_greaters t2 k -> abr (Node t1 k r t2).

Definition is_higher_rank_than_root (t: Tree) (r: nat) (k: A) : bool :=
  match t with
  | Leaf => true
  | Node _ r1 k1 _ => is_higher_rank r k r1 k1
  end.

Inductive heap_higher_rank: Tree -> Prop :=
| leaf_heap : heap_higher_rank Leaf
| rec_heap : forall t1 r k t2,
    heap_higher_rank t1 -> heap_higher_rank t2 ->
    is_higher_rank_than_root t1 r k = true -> is_higher_rank_than_root t2 r k = true ->
    heap_higher_rank (Node t1 k r t2).

Definition zip_tree (t: Tree) : Prop := heap_higher_rank t /\ abr t.

#[export] Hint Constructors occurs abr all_smallers all_greaters: core.

Lemma occurs_unzip : forall t k x, occurs x t -> x = k \/ occurs x (fst (unzip t k)) \/ occurs x (snd (unzip t k)).
Proof.
  intros t k x H.
  induction H;
    simpl;
    try
      (
        destruct (k =? k0);
        destruct (k <? k0);
        destruct (unzip t1 k);
        destruct (unzip t2 k);
        destruct IHoccurs;
        destruct H0;
        eauto
      );
    destruct (k <? k0);
    destruct (unzip t1 k);
    destruct (unzip t2 k);
    remember (k =? k0);
    destruct b;
    eauto using occurs;
    left;
    apply eq_sym;
    apply Nat.eqb_eq;
    auto.
Qed.

Lemma occurs_fst_unzip : forall t k x, occurs x (fst (unzip t k)) -> occurs x t.
Proof.
  intros t k x. induction t.
  - simpl. auto.
  - simpl. destruct (k =? a); auto. destruct (k <? a).
    + destruct (unzip t1 k). auto using occurs.
    + destruct (unzip t2 k). simpl in IHt2. simpl. intro. inversion H; auto using occurs.
Qed.

Lemma occurs_snd_unzip : forall t k x, occurs x (snd (unzip t k)) -> occurs x t.
Proof.
  intros t k x. induction t; auto. simpl. destruct (k =? a); auto. destruct (k <? a).
  - destruct (unzip t1 k). simpl in IHt1. intro H; inversion H; auto using occurs.
  - destruct (unzip t2 k). auto using occurs.
Qed.


Lemma unzip_preserves_smaller_fst : forall t k x, all_smallers t x -> all_smallers (fst (unzip t k)) x.
  intros. apply occurs_smallers. intros. apply occurs_fst_unzip in H0.
  eapply occurs_smallers; eauto.
Qed.

Lemma unzip_preserves_smaller_snd : forall t k x, all_smallers t x -> all_smallers (snd (unzip t k)) x.
  intros. apply occurs_smallers. intros. apply occurs_snd_unzip in H0.
  eapply occurs_smallers; eauto.
Qed.

Lemma unzip_preserves_greater_fst : forall t k x, all_greaters t x -> all_greaters (fst (unzip t k)) x.
  intros. apply occurs_greaters. intros. apply occurs_fst_unzip in H0.
  eapply occurs_greaters; eauto.
Qed.

Lemma unzip_preserves_greater_snd : forall t k x, all_greaters t x -> all_greaters (snd (unzip t k)) x.
  intros. apply occurs_greaters. intros. apply occurs_snd_unzip in H0.
  eapply occurs_greaters; eauto.
Qed.

Lemma unzip_smaller_greater :
  forall t k, abr t -> all_smallers (fst (unzip t k)) k /\ all_greaters (snd (unzip t k)) k.
  intros t k H. induction H; simpl; auto. remember (k =? k0). destruct b.
  - apply eq_sym, Nat.eqb_eq in Heqb. subst. auto.
  - remember (k <? k0). destruct b.
    + apply eq_sym, Nat.ltb_lt in Heqb0. destruct (unzip t1 k). simpl. destruct IHabr1.
      eauto using greaters_trans.
    + apply opti_tricho in Heqb; auto. destruct (unzip t2 k). simpl. destruct IHabr2.
      split; eauto using smaller_trans.
Qed.

Lemma unzip_preserves_abr_small :
  forall t k, abr t -> abr (fst (unzip t k)).
Proof.
  intros t k H. induction H; simpl; auto. remember (k =? k0). destruct b; auto.
  remember (k <? k0). destruct b.
  - remember (unzip t1 k). destruct p. simpl in IHabr1. simpl. auto.
  - apply eq_sym in Heqb, Heqb0. remember (unzip t2 k). destruct p. simpl in IHabr2. simpl.
    constructor; auto. destruct (couple_to_fst_snd Heqp).
    subst. auto using unzip_preserves_greater_fst.
Qed.

Lemma unzip_preserves_abr_great : forall t k, abr t -> abr (snd (unzip t k)).
Proof.
  intros t k H. induction H; simpl; auto. remember (k =? k0). destruct b; auto.
  remember (k <? k0). destruct b.
  - remember (unzip t1 k). destruct p. simpl in IHabr1. simpl. constructor; auto.
    destruct (couple_to_fst_snd Heqp). subst.
    auto using unzip_preserves_smaller_snd.
  - remember (unzip t2 k). destruct p. simpl in IHabr2. simpl.
    auto.
Qed.


      
Lemma occurs_down : forall t k r x, occurs x (down t k r) -> occurs x t \/ x = k.
  intros t k r x. induction t.
  - simpl. intro H. inversion H; subst; auto.
  - simpl. destruct (is_higher_rank n a r k).
    + destruct (a <? k);
        intro;
        inversion H;
        subst;
        eauto using occurs;
        (destruct (IHt1 H2) || destruct (IHt2 H2)); eauto using occurs.
    + destruct (k =? a).
      * intro. inversion H; subst; auto using occurs.
      * destruct (k <? a).
        -- remember (unzip t1 k);
             destruct p;
             intro;
             inversion H;
             subst;
             auto.
           ++ left. apply left_occurs. eapply occurs_fst_unzip. rewrite <- Heqp. auto.
           ++ inversion H2; subst; auto. left. constructor 2. eapply occurs_snd_unzip.
              rewrite <- Heqp. auto.
        -- remember (unzip t2 k).
           destruct p.
           intro.
           inversion H; subst; auto.
           ++ inversion H2; subst; auto. left. constructor 3. eapply occurs_fst_unzip.
              rewrite <- Heqp. auto.
           ++ left. constructor 3. eapply occurs_snd_unzip. rewrite <- Heqp. auto.
Qed.

Lemma down_preserves_abr : forall t k r, ~(occurs k t) -> abr t -> abr (down t k r).
  intros t k r H. induction t.
  - intro. simpl. constructor; constructor.
  - intro. inversion H0. subst. simpl. remember (is_higher_rank n a r k). destruct b.
    + remember (a <? k). destruct b.
      * constructor; auto. apply occurs_greaters. intros.
        apply occurs_down in H1. apply eq_sym in Heqb0. apply Nat.ltb_lt in Heqb0.
        destruct H1; subst; auto. eapply occurs_greaters; eauto.
      * constructor; auto. apply occurs_smallers. intros. apply occurs_down in H1.
        destruct H1; subst; auto.
        -- eapply occurs_smallers; eauto.
        -- unfold is_higher_rank in Heqb. remember (k <? a). destruct b.
           ++ apply eq_sym in Heqb1. apply Nat.ltb_lt. auto.
           ++ simpl in Heqb. apply eq_sym in Heqb0, Heqb1. apply Nat.ltb_ge in Heqb0, Heqb1.
              exfalso. cut (a = k).
              ** intro. subst. auto using occurs.
              ** apply Nat.le_antisymm; auto.
    + remember (k =? a). destruct b.
      * apply eq_sym, Nat.eqb_eq in Heqb0. subst. constructor; auto.
      * remember (k <? a). destruct b.
        -- apply eq_sym, Nat.ltb_lt in Heqb1. remember (unzip t1 k). destruct p.
           constructor;
             destruct (couple_to_fst_snd Heqp);
             subst;
             eauto using unzip_preserves_abr_small,
             unzip_preserves_abr_great,
             unzip_preserves_smaller_snd,
             unzip_smaller_greater.
           ++ apply unzip_smaller_greater. auto.
           ++ constructor; eauto using greaters_trans. apply unzip_smaller_greater. auto.
        -- apply opti_tricho in Heqb0; auto. remember (unzip t2 k). destruct p.
           destruct (couple_to_fst_snd Heqp). subst.
           constructor; auto using unzip_preserves_greater_fst,
             unzip_preserves_abr_small,
             unzip_preserves_abr_great.
           ++ constructor; auto.
              ** eapply smaller_trans; eauto.
              ** apply unzip_smaller_greater. auto.
           ++ apply unzip_smaller_greater. auto.
Qed.
Theorem down_correct : forall t k r,
    zip_tree t ->
    zip_tree (down t k r) /\ (forall y, occurs y (down t k r) <-> occurs y t \/ y=k).
Abort.



