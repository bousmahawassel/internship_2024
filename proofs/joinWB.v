From Hammer Require Import Tactics.
From BalancedTrees Require Import definitions utils.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Lists.

Equations weight (t: Tree) : nat :=
| Leaf => 1
| Node t1 _ t2 => weight t1 + weight t2.

Lemma weight_ge_one : forall t, weight t >= 1. (* Un lemme simple dont j'ai besoin un peu plus tard *)
Proof.
  unfold ge. intro. funelim (weight t); auto. transitivity (1 + 1); auto.
  transitivity (weight t1 + 1); auto using add_le_mono_r_proj_l2r, add_le_mono_l_proj_l2r.
Qed.

Lemma weight_elements : forall t, weight t = length (elements t) + 1.
Proof.
  intro. induction t; auto. simp elements weight. rewrite IHt1, IHt2.
  repeat rewrite app_length. simpl. lia.
Qed.

Lemma equal_elts_equal_weight : forall t1 t2, elements t1 = elements t2 -> weight t1 = weight t2.
Proof.
intros. repeat rewrite weight_elements. rewrite H. auto.
Qed.

Definition alpha := 29.

Definition not_left_heavyb wl wr :=
  alpha * wl <=? (100 - alpha) * wr.

Definition not_left_heavy wl wr :=
  alpha * wl <= (100 - alpha) * wr.

Lemma not_left_heavy_equiv : forall wl wr, not_left_heavy wl wr <-> not_left_heavyb wl wr = true.
Proof.
  intros. unfold not_left_heavy, not_left_heavyb. rewrite Nat.leb_le. auto.
Qed.

Lemma not_left_heavy_equiv_false : forall wl wr, ~not_left_heavy wl wr <-> not_left_heavyb wl wr = false.
Proof.
  intros. unfold not_left_heavy, not_left_heavyb. rewrite Nat.leb_nle. auto.
Qed.

Definition not_right_heavy wl wr :=
  not_left_heavy wr wl.

Definition not_right_heavyb wl wr :=
  not_left_heavyb wr wl.

Lemma not_right_heavy_equiv : forall wl wr, not_right_heavy wl wr <-> not_right_heavyb wl wr = true.
Proof.
  intros. apply not_left_heavy_equiv.
Qed.

Lemma not_right_heavy_equiv_false : forall wl wr,
    ~not_right_heavy wl wr <-> not_right_heavyb wl wr = false.
Proof.
  intros. apply not_left_heavy_equiv_false.
Qed.

Lemma left_heavy_Leaf_false : forall r, not_left_heavy (weight Leaf) (weight r).
Proof.
  intro. unfold not_left_heavy. simp weight. remember (weight_ge_one r). unfold alpha. lia.
Qed.

Lemma left_heavy_not_leaf : forall l r, ~ (not_left_heavy (weight l) (weight r)) -> l <> Leaf.
Proof.
  intuition. subst. auto using left_heavy_Leaf_false.
Qed.

Definition like_weights wl wr :=
  not_left_heavy wl wr /\ not_right_heavy wl wr.

Definition like_weightsb wl wr :=
  not_left_heavyb wl wr && not_right_heavyb wl wr.

Lemma like_weights_equiv : forall wl wr, like_weights wl wr <-> like_weightsb wl wr = true.
Proof.
  intros. unfold like_weights, like_weightsb. rewrite not_left_heavy_equiv, not_right_heavy_equiv.
  split; auto using andb_true_intro, andb_prop.
Qed.

Lemma like_weightsb_false_iff : forall wl wr,
    like_weightsb wl wr = false <-> ~ not_left_heavy wl wr \/ ~ not_right_heavy wl wr.
Proof.
  intros. unfold like_weightsb. rewrite not_left_heavy_equiv_false, not_right_heavy_equiv_false.
  intuition.
  - apply andb_false_iff. auto.
  - rewrite H0. auto.
  - rewrite H0. apply andb_false_r.
Qed.

Inductive WB : Tree -> Prop :=
| WBLeaf : WB Leaf
| WBNode : forall l v r, WB l -> WB r -> like_weights (weight l) (weight r) -> WB (Node l v r).

(*Equations balance_maybe_right_heavy (l: Tree) (v: A) (r: Tree) : Tree :=
| l, v, r with not_right_heavy (weight l) (weight r) => {
  | true => Node l v r (* évacue le maybe *)
  | false with r => {
    | Leaf => Leaf (* Ce cas n'a pas de sens, cf lemme *)
    | Node rl rv rr
      with like_weights (weight l) (weight rl), like_weights (weight l + weight rl) (weight rr)
      => {
      | true, true => Node (Node l v rl) rv rr
      | _, _ with rl => {
        | Leaf => Leaf (* apparemment c'est absurde aussi, mais je sais pas encore pourquoi *)
        | Node rll rlv rlr => Node (Node l v rll) rlv (Node rlr rv rr)
        }
      }
    }
  }.

Lemma dead_rl_leaf : forall l r rl rv rr,
    not_right_heavy (weight l) (weight r) = false ->
    r = Node rl rv rr ->
    like_weights (weight l) (weight rl) && like_weights (weight l + weight rl) (weight rr) = false ->
    WB r ->
    rl = Leaf -> False.
Proof.
  intros. subst. inversion H2. subst. unfold like_weights, not_right_heavy in *.
  rewrite left_heavy_Leaf_false in *. apply andb_prop in H7. intuition. clear H0 H2 H5.
  remember (weight_ge_one rr).
  remember (not_left_heavy (weight l) (weight Leaf)) as b eqn: Heqb; destruct b;
    apply eq_sym in Heqb;
    remember (not_left_heavy (weight l + weight Leaf) (weight rr)) as b eqn: Heqb0; destruct b;
    apply eq_sym in Heqb0;
    remember (not_left_heavy (weight rr) (weight l + weight Leaf)) as b eqn: Heqb1; destruct b;
    apply eq_sym in Heqb1;
    try discriminate;
    simp weight in *;
    unfold not_left_heavy, alpha in *; rewrite Nat.leb_le, Nat.leb_gt in *; try lia.
Qed.

Equations balance_maybe_left_heavy (l: Tree) (v: A) (r: Tree) : Tree :=
| l, v, r with not_left_heavy (weight l) (weight r) => {
  | true => Node l v r (* évacue le maybe *)
  | false with l => {
    | Leaf => Leaf (* Ce cas n'a pas de sens, cf lemme *)
    | Node ll lv lr
      with like_weights (weight r) (weight lr), like_weights (weight r + weight lr) (weight ll)
      => {
      | true, true => Node ll lv (Node lr v r)
      | _, _ with lr => {
        | Leaf => Leaf (* apparemment c'est absurde aussi, mais je sais pas encore pourquoi *)
        | Node lrl lrv lrr => Node (Node ll lv lrl) lrv (Node lrr v r)
        }
      }
    }
  }.



Lemma dead_lr_leaf : forall l r ll lv lr,
    not_left_heavy (weight l) (weight r) = false ->
    l = Node ll lv lr ->
    like_weights (weight r) (weight lr) &&
      like_weights (weight r + weight lr) (weight ll) = false ->
    WB l ->
    lr = Leaf -> False.
Proof.
  intros. subst. inversion H2. subst. unfold like_weights, not_right_heavy in *.
  rewrite left_heavy_Leaf_false in *. apply andb_prop in H7. intuition. clear H3 H2 H5.
  remember (weight_ge_one ll).
  remember (not_left_heavy (weight r) (weight Leaf)) as b eqn: Heqb; destruct b;
    apply eq_sym in Heqb;
    remember (not_left_heavy (weight r + weight Leaf) (weight ll)) as b eqn: Heqb0; destruct b;
    apply eq_sym in Heqb0;
    remember (not_left_heavy (weight ll) (weight r + weight Leaf)) as b eqn: Heqb1; destruct b;
    apply eq_sym in Heqb1;
    try discriminate;
    simp weight in *;
    unfold not_left_heavy, alpha in *; rewrite Nat.leb_le, Nat.leb_gt in *; try lia.
Qed.

(* J'ai fusionné [join_left_heavy] dans [join_maybe_left_heavy]*)
Equations join_maybe_left_heavy (l: Tree) (v: A) (r: Tree) : Tree :=
| l, v, r with (not_left_heavy (weight l) (weight r)) => {
  | true => Node l v r (* évacue le maybe *)
  | false with l => {
    | Leaf => Leaf (* Ce cas n'a pas de sens, cf lemme *)
    | Node ll lv lr =>
        balance_maybe_right_heavy ll lv (join_maybe_left_heavy lr v r)
    }
  }
.

Equations join_maybe_right_heavy (l: Tree) (v: A) (r: Tree) : Tree :=
| l, v, r with not_right_heavy (weight l) (weight r) => {
  | true => Node l v r (* évacue le maybe *)
  | false with r => {
    | Leaf => Leaf (* Ce cas n'a pas de sens, cf lemme *)
    | Node rl rv rr =>
        balance_maybe_left_heavy (join_maybe_right_heavy l v rl) rv rr
    }
  }
.

Definition join l v r : Tree :=
  if not_left_heavy (weight l) (weight r) then
    if not_right_heavy (weight l) (weight r) then
      Node l v r
    else
      join_maybe_right_heavy l v r
  else
    join_maybe_left_heavy l v r.*)

Equations rotate_left (l: Tree) (v: A) (r: Tree) : Tree :=
| l, v, Leaf => Leaf (* should not be called *)
| l, v, Node rl rv rr => Node (Node l v rl) rv rr
.

Equations rotate_right (l: Tree) (v: A) (r: Tree) : Tree :=
| Leaf, v, r => Leaf
| Node ll lv lr, v, r => Node ll lv (Node lr v r)
.

Equations join_maybe_left_heavy (T__L: Tree) (k: A) (T__R: Tree) : Tree :=
| T__L, k, T__R with not_left_heavyb (weight T__L) (weight T__R) => {
  | true => Node T__L k T__R
  | false with T__L => {
    | Leaf => Leaf (* absurde *)
    | Node l k' c with join_maybe_left_heavy c k T__R  => {
      | T' with T' => {
        | Leaf => Leaf (* absurde *)
        | Node l1 k1 r1 with not_right_heavyb (weight l) (weight T') => {
          | true => Node l k' T'
          | false with like_weightsb (weight l) (weight l1),
              like_weightsb (weight l + weight l1) (weight r1) => {
            | true, true => rotate_left l k' T'
            | _, _ => rotate_left l k' (rotate_right l1 k1 r1)
            }
          }
        }
      }
    }
  }.

Equations join_maybe_right_heavy (T__L: Tree) (k: A) (T__R: Tree) : Tree :=
| T__L, k, T__R with not_right_heavyb (weight T__L) (weight T__R) => {
  | true => Node T__L k T__R
  | false with T__R => {
    | Leaf => Leaf (* absurde *)
    | Node c k' r with join_maybe_right_heavy T__L k c  => {
      | T' with T' => {
        | Leaf => Leaf (* absurde *)
        | Node l1 k1 r1 with not_left_heavyb (weight T') (weight r) => {
          | true => Node T' k' r
          | false with like_weightsb (weight r1) (weight r),
              like_weightsb (weight l1) (weight r1 + weight r) => {
            | true, true => rotate_right T' k' r
            | _, _ => rotate_right (rotate_left l1 k1 r1) k' r
            }
          }
        }
      }
    }
  }.

Ltac elim_join_left :=
  match goal with
  | |- context[join_maybe_left_heavy ?a ?b ?c] =>
      funelim (join_maybe_left_heavy a b c);
      rewrite <- ?not_left_heavy_equiv, <- ?not_left_heavy_equiv_false,
        <- ?not_right_heavy_equiv, <- ?not_right_heavy_equiv_false,
        <- ?like_weights_equiv, ?like_weightsb_false_iff in *;
      match goal with
      | H : _ = join_maybe_left_heavy _ _ _ |- _ => rewrite <- H; clear H
      end;
      eauto
  end.

Ltac elim_join_right :=
  match goal with
  | |- context[join_maybe_right_heavy ?a ?b ?c] =>
      funelim (join_maybe_right_heavy a b c);
      rewrite <- ?not_left_heavy_equiv, <- ?not_left_heavy_equiv_false,
        <- ?not_right_heavy_equiv, <- ?not_right_heavy_equiv_false,
        <- ?like_weights_equiv, ?like_weightsb_false_iff in *;
      match goal with
      | H : _ = join_maybe_right_heavy _ _ _ |- _ => rewrite <- H; clear H
      end;
      eauto
  end.
(*
Lemma join_maybe_left_heavy_no_leaf : forall T__L k T__R,
    WB T__L -> WB T__R -> not_right_heavy (weight T__L) (weight T__R) ->
    join_maybe_left_heavy T__L k T__R <> Leaf.
  intros. elim_join_left.
  - eauto using left_heavy_not_leaf.
  - inversion H. intuition. apply H10; auto. simp weight in *.
    unfold like_weights, not_right_heavy, not_left_heavy, alpha in *. lia.
  - inversion H. subst. destruct l1; simp rotate_right; simp rotate_left; auto.
    exfalso. simp weight in *.
    unfold like_weights, not_right_heavy, not_left_heavy, alpha in *. clear Hind H.
    destruct Heq; try lia. intuition. assert (weight l < 3) by lia.
    assert (weight c < 5) by lia. assert (weight T__R < 3) by lia. assert (weight r1 > 4) by lia.
    remember (weight_ge_one T__R). assert (weight l = 1 \/ weight l = 2) by lia.
    assert (weight T__R = 1 \/ weight T__R = 2) by lia.
    assert (weight c = 1 \/ weight c = 2 \/ weight c = 3 \/ weight c = 4) by lia. intuition try lia.
    + subst. rewrite H15, H12, H14 in *. clear H2 H3 H7 H9 H10 H4 H8 H1 Heq3.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - 
 *)
(*
Lemma join_maybe_left_heavy_keeps_weight : forall T__L k T__R,
    WB T__L -> not_right_heavy (weight T__L) (weight T__R) ->
    weight T__L + weight T__R = weight (join_maybe_left_heavy T__L k T__R).
Proof.
  intros. elim_join_left.
  - apply left_heavy_not_leaf in Heq. congruence.
  - inversion H. subst. rewrite Heq in *. simp weight in *.
    unfold like_weights, not_right_heavy, not_left_heavy, alpha in *. remember (weight_ge_one c).
    remember (weight_ge_one T__R). intuition. lia.
  - rewrite Heq0 in *. simp weight in *. inversion H. rewrite <- Hind; try hauto.
    unfold like_weights, not_right_heavy, not_left_heavy, alpha in *. lia.
  - rewrite Heq2 in *. simp rotate_left. simp weight in *. 
    enough (weight c + weight T__R = weight l1 + weight r1) by hauto. inversion H.
    apply Hind; auto. unfold like_weights, not_right_heavy, not_left_heavy, alpha in *. lia.
  - inversion H. subst. rewrite Heq2 in *.
    assert (not_right_heavy (weight c) (weight T__R)).
    + simp weight in *. unfold like_weights, not_right_heavy, not_left_heavy, alpha in *.
      intuition try lia.
    + specialize (Hind H5 H1). destruct l1.
      * simp weight in *. unfold like_weights, not_right_heavy, not_left_heavy, alpha in *.
        lia.
      * simp rotate_right. simp rotate_left. simp weight in *. lia.
  - inversion H. subst. rewrite Heq1 in *.
    assert (not_right_heavy (weight c) (weight T__R)).
    + simp weight in *. unfold like_weights, not_right_heavy, not_left_heavy, alpha in *.
      intuition try lia.
    + specialize (Hind H5 H1). destruct l1.
      * simp weight in *. unfold like_weights, not_right_heavy, not_left_heavy, alpha in *.
        intuition try lia. exfalso. clear Heq1 H H4 H5 H0. admit.
      * simp rotate_right. simp rotate_left. simp weight in *. lia.
Qed.
 *)

Ltac lia_autosolve :=
  match goal with
  | H: elements _ = elements _ |- _ => apply equal_elts_equal_weight in H
  | |- _ => idtac
  end;
  unfold like_weights, not_right_heavy, not_left_heavy, alpha in *; simp weight in *;
  try lia.

#[export] Hint Rewrite app_assoc: app.

Lemma join_maybe_left_heavyWB : forall T__L k T__R,
    WB T__L -> WB T__R -> not_right_heavy (weight T__L) (weight T__R) ->
    WB (join_maybe_left_heavy T__L k T__R) /\
      elements (join_maybe_left_heavy T__L k T__R) = elements (Node T__L k T__R).
Proof.
  intros. elim_join_left; split.
  - constructor; auto. unfold like_weights. intuition.
  - auto.
  - constructor.
  - apply left_heavy_not_leaf in Heq. congruence.
  - constructor.
  - inversion H. rewrite Heq in *. intuition. exfalso.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve. remember (weight_ge_one c).
    remember (weight_ge_one T__R). intuition. lia_autosolve.
  - rewrite Heq0 in *. inversion H. subst.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    intuition. constructor; auto; lia_autosolve.
  - inversion H. subst. assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    intuition. rewrite Heq0 in *. simp elements in *. aac_rewrite H8.
    aac_reflexivity.
  - simp rotate_left. rewrite Heq2 in *. inversion H. subst.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve. intuition. inversion H4.
    subst. constructor; auto. constructor; auto.
  - simp rotate_left. intuition. rewrite Heq2 in *. inversion H; subst.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    intuition. simp elements in *. aac_rewrite H8. aac_reflexivity.
  - inversion H. subst. assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    destruct l1; simp rotate_right; simp rotate_left; auto using WB.
    simp weight in *. specialize (Hind H6 H0 H2). destruct Hind. rewrite Heq2 in *.
    inversion_clear H3. inversion_clear H8.
    repeat constructor; auto; lia_autosolve.
  - rewrite Heq2 in *. inversion H. subst.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    destruct l1.
    + intuition. lia_autosolve. lia_autosolve.
    + simp rotate_right. simp rotate_left. simp elements in *.
      intuition aac_rewrite H9; aac_reflexivity.
  - inversion H. subst. assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    destruct l1; simp rotate_right; simp rotate_left; auto using WB.
    simp weight in *. specialize (Hind H6 H0 H2). rewrite Heq1 in *.
    destruct Hind. inversion_clear H3. inversion_clear H8.
    repeat constructor; auto; lia_autosolve.
  - rewrite Heq1 in *. inversion H. subst.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    destruct l1.
    + intuition lia_autosolve. inversion H8. subst. lia_autosolve.
    + simp rotate_right. simp rotate_left. simp elements in *.
      intuition aac_rewrite H9; aac_reflexivity.
Qed.

Lemma join_maybe_right_heavyWB : forall T__L k T__R,
    WB T__L -> WB T__R -> not_left_heavy (weight T__L) (weight T__R) ->
    WB (join_maybe_right_heavy T__L k T__R) /\
      elements (join_maybe_right_heavy T__L k T__R) = elements (Node T__L k T__R).
Proof.
  intros. elim_join_right; split.
  - constructor; auto. unfold like_weights. intuition.
  - auto.
  - constructor.
  - apply left_heavy_not_leaf in Heq. congruence.
  - constructor.
  - inversion H0. subst. rewrite Heq in *. intuition. exfalso.
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve. remember (weight_ge_one c).
    remember (weight_ge_one T__L). intuition. lia_autosolve.
  - rewrite Heq0 in *. inversion H0. subst.
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    intuition. constructor; auto; lia_autosolve.
  - inversion H0. subst. assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    intuition. rewrite Heq0 in *. simp elements in *. aac_rewrite H8. aac_reflexivity.
  - simp rotate_right. rewrite Heq2 in *. inversion H0. subst.
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve. intuition. inversion H4.
    subst. constructor; auto. constructor; auto.
  - simp rotate_right. intuition. rewrite Heq2 in *. inversion H0; subst.
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    intuition. simp elements in *. aac_rewrite H5. aac_reflexivity.
  - inversion H0. subst. assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    destruct r1; simp rotate_left; simp rotate_right; auto using WB.
    simp weight in *. specialize (Hind H H5 H2). destruct Hind. rewrite Heq2 in *.
    inversion_clear H3. inversion_clear H9.
    repeat constructor; auto; lia_autosolve.
  - rewrite Heq2 in *. inversion H0. subst.
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    destruct r1.
    + intuition lia_autosolve. inversion H8. lia_autosolve.
    + simp rotate_left rotate_right. simp elements in *.
      intuition aac_rewrite H9; aac_reflexivity.
  - inversion H0. subst. assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    destruct r1; simp rotate_left; simp rotate_right; auto using WB.
    simp weight in *. specialize (Hind H H5 H2). rewrite Heq1 in *.
    destruct Hind. inversion_clear H3. inversion_clear H9.
    repeat constructor; auto; lia_autosolve.
  - rewrite Heq1 in *. inversion H0. subst.
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve.
    destruct r1.
    + intuition lia_autosolve. inversion H8. subst. lia_autosolve.
    + simp rotate_left rotate_right. simp elements in *.
      intuition aac_rewrite H9; aac_reflexivity.
Qed.
(*
Lemma balance_maybe_left_elements : forall l v r, WB l ->
    elements (balance_maybe_left_heavy l v r) = elements l ++ [v] ++ elements r.
  intros. funelim (balance_maybe_left_heavy l v r); rewrite <- Heqcall; auto.
  - apply left_heavy_not_leaf in Heq. congruence.
  - simp elements. autorewrite with app using auto.
  - exfalso. eapply dead_lr_leaf; eauto. rewrite Heq0. auto.
  - simp elements. autorewrite with app using auto.
  - exfalso. eapply dead_lr_leaf; eauto. rewrite Heq.
    destruct (like_weights (weight r) (weight Leaf)); auto.
  - simp elements. autorewrite with app using auto.
Qed.

Lemma balance_maybe_right_elements : forall l v r, WB r ->
    elements (balance_maybe_right_heavy l v r) = elements l ++ [v] ++ elements r.
  intros. funelim (balance_maybe_right_heavy l v r); rewrite <- Heqcall; auto.
  - apply left_heavy_not_leaf in Heq. congruence.
  - simp elements. autorewrite with app using auto.
  - exfalso. eapply dead_rl_leaf; eauto. rewrite Heq0. auto.
  - simp elements. autorewrite with app using auto.
  - exfalso. eapply dead_rl_leaf; eauto. rewrite Heq. auto.
  - simp elements. autorewrite with app using auto.
Qed.

Lemma join_WB : forall l v r, WB l -> WB r -> WB (join l v r).

Lemma join_elements : forall l v r,
    WB l -> WB r -> elements (join l v r) = elements l ++ [v] ++ elements r.
Proof.
  intros. unfold join. destruct (not_left_heavy (weight l) (weight r)).
  - destruct (not_right_heavy (weight l) (weight r)); auto.
    funelim (join_maybe_right_heavy l v r); try congruence.
    + rewrite <- Heqcall. auto.
    + apply left_heavy_not_leaf in Heq. congruence.
    + rewrite <- Heqcall. rewrite balance_maybe_left_elements.
      * inversion H1. subst. rewrite H; auto. simp elements. autorewrite with app using auto.
      * admit.
  - funelim (join_maybe_left_heavy l v r); try congruence.
    + rewrite <- Heqcall; auto.
    + apply left_heavy_not_leaf in Heq. congruence.
    + rewrite <- Heqcall. rewrite balance_maybe_right_elements.
      * inversion H0. subst. rewrite H; auto. simp elements. autorewrite with app using auto.
      * admit.
Admitted.
*)
