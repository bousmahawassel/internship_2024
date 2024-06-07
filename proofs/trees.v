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

(*Goal forall a b, unzip t k = (a, b) -> occurs k t -> elements t = elements a ++ [k] ++ elements b
 Goal forall a b, unzip t k = (a, b) ->  ~ (occurs k t) -> elements t = elements a ++ elements b
 Goal forall a b, unzip t k = (a, b) ->  elements t = elements a ++ delta (occursb t k) k ++ elements b.
 *)

Equations down (t: Tree) (k: A) (r: nat) : Tree :=
| Leaf, k, r => singleton_list k r
| Node t1 kt rt t2, k, r with is_higher_rank rt kt r k => {
  | false with unzip (Node t1 kt rt t2) k => {
      | (st, gt) => Node st k r gt
    }
  | true with kt <? k => {
    | false => Node (down t1 k r) kt rt t2
    | true => Node t1 kt rt (down t2 k r)
    }
  }.

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

#[local] Hint Rewrite app_assoc: app.

Lemma unzip_elts_occurs_k : forall t k a b, abr t ->
    unzip t k = (a, b) -> occurs k t ->
    elements t = elements a ++ [k] ++ elements b.
Proof.
  intros t k. funelim (unzip t k); try easy.
  - intros. subst. apply Nat.eqb_eq in H. subst. rewrite <- Heqcall in *. inversion H1. subst. auto.
  - intros. rewrite <- Heqcall in *. inversion H2. subst. simp elements. autorewrite with app. repeat f_equal.
    rewrite <- app_assoc.
    apply abr_node in H1 as Habr. intuition. apply Hind; auto. apply Nat.ltb_lt in H0.
    eapply abr_lt_occurs; eauto.
  - intros. rewrite <- Heqcall in *. inversion H2. subst. simp elements.
    replace ((elements t1 ++ [kt] ++ elements st2) ++ [k] ++ elements b)
      with (elements t1 ++ [kt] ++ elements st2 ++ [k] ++ elements b) by autorewrite with app using auto.
    repeat f_equal. apply abr_node in H1 as Habr. intuition. apply Hind; auto. apply opti_tricho in H; auto.
      eapply abr_gt_occurs; eauto.
Qed.

Lemma unzip_elts_not_occurs_k : forall t k a b,
    abr t -> unzip t k = (a, b) -> ~ occurs k t -> elements t = elements a ++ elements b.
Proof.
  intros t k. funelim (unzip t k).
  - simp unzip. intros. inversion H0. auto.
  - intros. rewrite Nat.eqb_eq in H. subst. absurd (kt ∈ Node t1 kt r t2); auto.
  - intros. rewrite <- Heqcall in *. inversion H2. subst. simp elements. autorewrite with app. repeat f_equal.
    apply abr_node in H1 as Habr. intuition. apply Hind; eauto.
  - intros. rewrite <- Heqcall in *. inversion H2. subst. simp elements. replace ((elements t1 ++ [kt] ++ elements st2) ++ elements b)
      with (elements t1 ++ [kt] ++ elements st2 ++ elements b) by autorewrite with app using auto.
    repeat f_equal. apply abr_node in H1 as Habr. intuition. apply Hind; eauto.
Qed.

Lemma unzip_elts_occursb : forall t k a b,
    abr t -> unzip t k = (a, b) -> elements t = elements a ++ delta (occursb k t) k ++ elements b.
  intros t k. remember (occursb k t). destruct b.
  - apply eq_sym, occursb_correct in Heqb. intros. simpl delta. apply unzip_elts_occurs_k; auto.
  - apply eq_sym in Heqb. intros. simpl. eapply unzip_elts_not_occurs_k; eauto. intro.
    apply occursb_correct in H1. rewrite Heqb in H1. discriminate.
Qed.

Lemma unzip_preserves_abr_fst : forall t k a b,
    abr t -> unzip t k = (a, b) -> abr a.
Proof.
  unfold abr.
  intros. rewrite (unzip_elts_occursb _ k a b) in H; auto.
  eauto using StronglySorted_app_inv_l.
Qed.

Lemma unzip_preserves_abr_snd : forall t k a b,
    abr t -> unzip t k = (a, b) -> abr b.
Proof.
  unfold abr. intros. rewrite (unzip_elts_occursb _ k a b) in H; auto.
  eauto using StronglySorted_app_inv_r.
Qed.

Lemma down_elts_occurs_k : forall t k r,
    abr t -> occurs k t -> elements t = elements (down t k r).
Proof.
  intros t k r. funelim (down t k r); try easy.
  - rewrite <- Heqcall. simp elements. intros. apply abr_node in H0 as H2. do 2 f_equal. intuition. apply H5.
    apply Nat.ltb_lt in Heq. eapply abr_gt_occurs; eauto.
  - rewrite <- Heqcall. simp elements. intros. apply abr_node in H0 as H2. f_equal. intuition. apply H5. unfold is_higher_rank in *. cut (k = kt \/ k < kt).
    + intuition.
      * subst.
Abort.


(*

      
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

