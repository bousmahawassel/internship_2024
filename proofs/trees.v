From BalancedTrees Require Import definitions utils.

Definition is_higher_rank (r1: nat) (k1: A) (r2: nat) (k2 : A) : bool :=
  (r2 <? r1) || ((r1 =? r2) && (k1 <? k2)).

(* coupe t en 2 sous-arbre : les éléments plus petits et les éléments plus grands *)
Equations unzip (t: Tree) (k: A) : Tree * Tree :=
  | Leaf, k => (Leaf, Leaf)
  | Node t1 kt r t2, k with (k =? kt, k <? kt) => {
    | (true, _) => (t1, t2)
    | (_, true) with unzip t1 k => {
        | (st1, gt1) => (st1, Node gt1 kt r t2)
      }
    | _ with unzip t2 k => {
        | (st2, gt2) => (Node t1 kt r st2, gt2)
      }
    }.

Fixpoint down (t: Tree) (k: A) (r: nat) {struct t} : Tree :=
  match t with
  | Node t1 kt rt t2 =>
      if is_higher_rank rt kt r k then
        if kt <? k then Node t1 kt rt (down t2 k r) else Node (down t1 k r) kt rt t2
      else let (st, gt) := unzip t k in Node st k r gt
  | Leaf => let (st, gt) := unzip t k in Node st k r gt
  end.

Definition insert (t: Tree) (k: nat) : Tree := down t k (rank_of k).

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

Lemma occurs_unzip : forall t k x, occurs x t -> x = k \/ occurs x (fst (unzip t k)) \/ occurs x (snd (unzip t k)).
Proof.
  intros t k x. funelim (unzip t k); eauto 10; apply couple_to_fst_snd in Heqcall;
    destruct Heqcall as [Hfst Hsnd];
    rewrite <- Hfst, <- Hsnd;
    try solve [apply Nat.eqb_eq in H; subst; eauto]; (* résout le cas où k = la racine *)
    (* résout les 2 cas récursifs *)
    intro Hocc;
    apply occurs_rec_direct in Hocc;
    repeat destruct Hocc as [Hocc | Hocc] using or_ind; eauto 10;
    apply Hind in Hocc; apply eq_sym, couple_to_fst_snd in Heq; destruct Heq; subst;
    repeat destruct Hocc as [Hocc | Hocc] using or_ind; eauto 10.
Qed.

Lemma occurs_fst_unzip : forall t k x, occurs x (fst (unzip t k)) -> occurs x t.
Proof.
  intros t k x. funelim (unzip t k);
    auto;
    apply couple_to_fst_snd in Heqcall;
    destruct Heqcall as [Hfst Hsnd]; rewrite <- Hfst; auto; apply eq_sym, couple_to_fst_snd in Heq;
    destruct Heq; subst; auto.
  intro Hocc. apply occurs_rec_direct in Hocc.
  repeat destruct Hocc as [Hocc | Hocc] using or_ind; subst; auto.
Qed.

Lemma occurs_snd_unzip : forall t k x, occurs x (snd (unzip t k)) -> occurs x t.
Proof.
  intros t k x. funelim (unzip t k);
    auto;
    apply couple_to_fst_snd in Heqcall;
    destruct Heqcall as [Hfst Hsnd]; rewrite <- Hsnd; auto; apply eq_sym, couple_to_fst_snd in Heq;
    destruct Heq; subst; auto.
  intro Hocc. apply occurs_rec_direct in Hocc.
  repeat destruct Hocc as [Hocc | Hocc] using or_ind; subst; auto.
Qed.


Lemma unzip_preserves_smaller_fst : forall t k x, all_smallers t x -> all_smallers (fst (unzip t k)) x.
  unfold all_smallers. intros. apply occurs_fst_unzip in H0. eauto.
Qed.

Lemma unzip_preserves_smaller_snd : forall t k x, all_smallers t x -> all_smallers (snd (unzip t k)) x.
  unfold all_smallers. intros. apply occurs_snd_unzip in H0. eauto.
Qed.

Lemma unzip_preserves_greater_fst : forall t k x, all_greaters t x -> all_greaters (fst (unzip t k)) x.
  unfold all_greaters. intros. apply occurs_fst_unzip in H0. eauto.
Qed.

Lemma unzip_preserves_greater_snd : forall t k x, all_greaters t x -> all_greaters (snd (unzip t k)) x.
  unfold all_greaters. intros. apply occurs_snd_unzip in H0. eauto.
Qed.

Lemma unzip_abr_small :
  forall t k, abr t -> abr ((unzip t k).1).
Proof.
  intros t k. unfold abr. funelim (unzip t k); eauto;
    apply couple_to_fst_snd in Heqcall; destruct Heqcall as [Hfst Hsnd];
    rewrite <- Hfst; unfold abr; simp elements.
  - eauto using StronglySorted_app_inv_l.
  - rewrite Heq in Hind. eauto using StronglySorted_app_inv_l.
  - Search (LocallySorted _ (_ ++ _)).
Abort.
(*Lemma unzip_smaller_greater :
  forall t k, abr t -> all_smallers (fst (unzip t k)) k /\ all_greaters (snd (unzip t k)) k.
  intros t k H. induction H. simp unzip; simpl; auto. remember (k =? k0). destruct b.
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
*)

