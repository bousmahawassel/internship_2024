From Hammer Require Import Tactics.
From BalancedTrees Require Import definitions utils trees.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Lists.
Import Z.

Open Scope Z_scope.

Equations weight (t: Tree) : Z :=
| Leaf => 1
| Node t1 _ t2 => weight t1 + weight t2.

Lemma weight_ge_one : forall t, 1 <= weight t. (* Un lemme simple dont j'ai besoin un peu plus tard *)
Proof.
  intro. funelim (weight t); lia.
Qed.

Lemma weight_elements : forall t, weight t = Z.of_nat (length (elements t)) + 1.
Proof.
  intro. induction t; auto. simp elements weight. rewrite IHt1, IHt2.
  repeat rewrite app_length. simpl. lia.
Qed.

Lemma equal_elts_equal_weight : forall t1 t2, elements t1 = elements t2 -> weight t1 = weight t2.
Proof.
intros. repeat rewrite weight_elements. rewrite H. auto.
Qed.

Definition alpha := 292893218813452.

Definition not_left_heavyb wl wr :=
  alpha * wl <=? (1_000_000_000_000_000 - alpha) * wr.

Definition not_left_heavy wl wr :=
  alpha * wl <= (1_000_000_000_000_000 - alpha) * wr.

Lemma not_left_heavy_equiv : forall wl wr, not_left_heavy wl wr <-> not_left_heavyb wl wr = true.
Proof.
  intros. unfold not_left_heavy, not_left_heavyb. rewrite Z.leb_le. auto.
Qed.

Lemma not_left_heavy_equiv_false : forall wl wr, ~not_left_heavy wl wr <-> not_left_heavyb wl wr = false.
Proof.
  intros. unfold not_left_heavy, not_left_heavyb. rewrite Z.leb_nle. auto.
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

Definition join T__L k T__R :=
  if not_left_heavyb (weight T__L) (weight T__R)
  then join_maybe_right_heavy T__L k T__R
  else join_maybe_left_heavy T__L k T__R.

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
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve.
    remember (weight_ge_one T__R). intuition. lia_autosolve.
  - rewrite Heq0 in *. inversion H. subst.
    assert (not_right_heavy (weight c) (weight T__R)) by lia_autosolve. remember (weight_ge_one T__R).
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
    + intuition; lia_autosolve.
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
    assert (not_left_heavy (weight T__L) (weight c)) by lia_autosolve. remember (weight_ge_one T__L).
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

Theorem join_correct : forall T__L k T__R, WB T__L -> WB T__R -> WB (join T__L k T__R) /\ elements (join T__L k T__R) =  elements (Node T__L k T__R).
Proof.
  intros. unfold join. remember (not_left_heavyb (weight T__L) (weight T__R)) as b; destruct b.
  - apply join_maybe_right_heavyWB; auto. rewrite not_left_heavy_equiv. auto.
  - apply join_maybe_left_heavyWB; auto. apply eq_sym in Heqb. rewrite  <- not_left_heavy_equiv_false in Heqb.
    unfold not_right_heavy, not_left_heavy, alpha in *. remember (weight_ge_one T__R). lia.
Qed.

Lemma joinWB : forall T__L k T__R, WB T__L -> WB T__R -> WB (join T__L k T__R).
Proof.
  apply join_correct.
Qed.

Lemma join_elts : forall T__L k T__R, WB T__L -> WB T__R -> elements (join T__L k T__R) = elements (Node T__L k T__R).
Proof.
  apply join_correct.
Qed.

Lemma join_occurs : forall T__L k T__R x, WB T__L -> WB T__R -> x ∈ join T__L k T__R <-> x ∈ T__L \/ x = k \/ x ∈ T__R.
Proof.
  unfold occurs. intros. rewrite join_elts; auto.
  change ((x ∈ elements ?a)%stdpp) with (occurs x a). intuition. apply occurs_rec in H1.
  intuition auto.
Qed.

Lemma join_abr : forall T__L k T__R, WB T__L -> WB T__R -> abr T__L -> abr T__R -> all_smallers T__L k ->
                            all_greaters T__R k -> abr (join T__L k T__R).
Proof.
  intros. unfold abr. rewrite join_elts; auto. apply abr_node. tauto.
Qed.

Close Scope Z_scope.

Equations split (T: Tree) (k: A) : Tree * bool * Tree :=
| Leaf, _ => (Leaf, false, Leaf)
| Node l k' r, k with k ?= k' => {
  | Eq => (l, true, r)
  | Lt with split l k => {
    | (ll, b, lr) => (ll, b, join lr k' r)
    }
  | Gt with split r k => {
    | (rl, b, rr) => (join l k' rl, b, rr)
    }
  }.

Lemma splitWB : forall T k a b c, WB T -> split T k = (a, b, c) -> WB a /\ WB c.
Proof.
  intros T k. funelim (split T k).
  - simp split. auto.
  - rewrite <- Heqcall. intros. inversion H0. subst. inversion H. auto.
  - rewrite <- Heqcall. intros. inversion H0. subst. specialize (Hind a b0 lr). inversion H.
    subst. intuition auto. apply joinWB; auto.
  - rewrite <- Heqcall. intros. inversion H0. subst. specialize (Hind rl b0 c). inversion H.
    subst. intuition auto. apply joinWB; auto.
Qed.

Lemma split_b : forall T k a b c, WB T -> abr T -> split T k = (a, b, c) -> b = occursb k T.
Proof.
  intros T k. funelim (split T k).
  - simp split. auto.
  - rewrite <- Heqcall. apply Nat.compare_eq in Heq. subst. intros. inversion H1. subst.
    apply eq_sym. rewrite occursb_correct. auto.
  - rewrite <- Heqcall. intros. inversion H1. subst. inversion H. subst.
    apply abr_node in H0 as Habrs. intuition.
    specialize (Hind _ _ _ H5 H2 Heq). subst.
    enough (occursb k l = true <-> occursb k (Node l k' r) = true).
    + destruct (occursb k l); destruct (occursb k (Node l k' r)); intuition congruence.
    + repeat rewrite occursb_correct. intuition auto. eapply abr_lt_occurs; eauto.
      apply Nat.compare_lt_iff. auto.
  - rewrite <- Heqcall. intros. inversion H1. subst. inversion H. subst.
    apply abr_node in H0 as Habrs. intuition.
    specialize (Hind _ _ _ H6 H4 Heq). subst.
    enough (occursb k r = true <-> occursb k (Node l k' r) = true).
    + destruct (occursb k r); destruct (occursb k (Node l k' r)); intuition congruence.
    + repeat rewrite occursb_correct. intuition auto. eapply abr_gt_occurs; eauto.
      apply Nat.compare_gt_iff. auto.
Qed.

Lemma split_elts_occursb : forall T k a b c,
    WB T -> abr T -> split T k = (a, b, c) ->
    elements T = elements a ++ delta (occursb k T) k ++ elements c.
Proof.
  intros T k. funelim (split T k).
  - simp split. auto.
  - rewrite <- Heqcall. apply Nat.compare_eq in Heq. subst. intros. inversion H1. subst.
    simp elements. repeat f_equal. assert (occursb k' (Node a k' c) = true).
    + apply occursb_correct. auto.
    + rewrite H2. auto.
  - rewrite <- Heqcall. intros. apply abr_node in H0 as Habr. inversion H. subst. intuition.
    specialize (Hind _ _ _ H5 H2 Heq).
    apply split_b in Heq as Heq'; auto. apply eq_sym in Heq'. rewrite Heq' in *. destruct b.
    + assert (occursb k (Node l k' r) = true).
      * rewrite occursb_correct in *. apply occurs_rec. auto.
      * rewrite H8. inversion H1. subst.
        apply splitWB in Heq as Heq2; auto. intuition. rewrite join_elts; auto. simp elements.
        rewrite Hind. aac_reflexivity.
    + assert (~ occurs k (Node l k' r)).
      * intro. apply Nat.compare_lt_iff in Heq0. apply abr_lt_occurs in H8; auto.
        apply occursb_correct in H8. congruence.
      * rewrite <- occursb_correct in H8. apply not_true_is_false in H8. rewrite H8.
        simp elements. rewrite Hind. inversion H1. subst. apply splitWB in Heq; auto. intuition.
        rewrite join_elts; auto. simp elements. aac_reflexivity.
  - rewrite <- Heqcall. intros. apply abr_node in H0 as Habr. inversion H. subst. intuition.
    specialize (Hind _ _ _ H6 H4 Heq).
    apply split_b in Heq as Heq'; auto. apply eq_sym in Heq'. rewrite Heq' in *. destruct b.
    + assert (occursb k (Node l k' r) = true).
      * rewrite occursb_correct in *. apply occurs_rec. auto.
      * rewrite H8. inversion H1. subst.
        apply splitWB in Heq as Heq2; auto. intuition. rewrite join_elts; auto. simp elements.
        rewrite Hind. aac_reflexivity.
    + assert (~ occurs k (Node l k' r)).
      * intro. apply Nat.compare_gt_iff in Heq0. apply abr_gt_occurs in H8; auto.
        apply occursb_correct in H8. congruence.
      * rewrite <- occursb_correct in H8. apply not_true_is_false in H8. rewrite H8.
        simp elements. rewrite Hind. inversion H1. subst. apply splitWB in Heq; auto. intuition.
        rewrite join_elts; auto. simp elements. aac_reflexivity.
Qed.

Lemma split_occurs : forall T k a b c,
    WB T -> abr T -> split T k = (a, b, c) -> forall x, x ∈ a \/ x ∈ c -> x ∈ T.
Proof.
  unfold occurs. intros. rewrite (split_elts_occursb _ _ _ _ _ H H0 H1).
  repeat rewrite elem_of_app. intuition auto.
Qed.

Lemma split_occurs_recipr : forall T k a b c,
    WB T -> abr T -> split T k = (a, b, c) -> forall x, x ∈ T -> x ∈ a \/ x ∈ c \/ (x = k /\ b = true).
Proof.
  unfold occurs. intros.
  rewrite (split_elts_occursb _ _ _ _ _ H H0 H1), elem_of_app, elem_of_app in H2.
  intuition auto. apply split_b, eq_sym in H1; auto.  destruct b.
  - rewrite H1 in *. simpl delta in *. apply elem_of_list_singleton in H2.
    subst. auto.
  - rewrite H1 in *. simpl delta in *. inversion H2.
Qed.

Lemma split_abr : forall T k a b c,
    WB T -> abr T -> split T k = (a, b, c) -> abr a /\ abr c.
Proof.
  intros. apply split_elts_occursb in H1; auto. unfold abr in *. rewrite H1 in *.
  eauto using StronglySorted_app_inv_l, StronglySorted_app_inv_r.
Qed.

Lemma split_smallers_greaters : forall T k a b c,
    WB T -> abr T -> split T k = (a, b, c) -> all_smallers a k /\ all_greaters c k.
Proof.
  intros T k. funelim (split T k).
  - simp split. intros. unfold all_smallers, all_greaters. inversion H1. subst. simp elements.
    auto.
  - apply Nat.compare_eq in Heq. subst. rewrite <- Heqcall. intros. apply abr_node in H0.
    inversion H1. subst. tauto.
  - rewrite <- Heqcall. intros. inversion H. subst. apply abr_node in H0 as Habr. inversion H1.
    subst. destruct Habr. specialize (Hind _ _ _ H5 H2 Heq). intuition.
    unfold all_greaters. apply splitWB in Heq as Heq'; auto. rewrite join_elts; try tauto.
    simp elements. apply List.Forall_app. intuition. apply List.Forall_app.
    apply Nat.compare_lt_iff in Heq0. intuition. eapply greater_trans; eauto.
  - rewrite <- Heqcall. intros. inversion H. subst. apply abr_node in H0 as Habr. inversion H1.
    subst. destruct Habr. destruct H3. specialize (Hind _ _ _ H6 H3 Heq). intuition.
    unfold all_smallers. apply splitWB in Heq as Heq'; auto. rewrite join_elts; try tauto.
    simp elements. apply List.Forall_app. apply Nat.compare_gt_iff in Heq0. intuition.
    { eapply smaller_trans; eauto. }
    apply List.Forall_app. auto.
Qed.

Equations union (T1 T2: Tree) : Tree :=
| Leaf, T2 => T2
| T1, Leaf => T1
| T1, Node L2 k R2 with split T1 k => {
  | (L1, _, R1) => join (union L1 L2) k (union R1 R2)
  }.

Lemma unionWB : forall T1 T2, WB T1 -> WB T2 -> WB (union T1 T2).
Proof.
  intros. funelim (union T1 T2).
  - rewrite <- Heqcall. auto.
  - simp union.
  - rewrite <- Heqcall. inversion H2. subst. apply splitWB in Heq; auto. destruct Heq.
    intuition. apply joinWB; auto.
Qed.

Lemma union_keeps_elts : forall T1 T2 x,
    WB T1 -> WB T2 -> abr T1 -> abr T2 -> x ∈ union T1 T2 <-> x ∈ T1 \/ x ∈ T2.
Proof.
  intros. funelim (union T1 T2).
  - rewrite <- Heqcall. intuition auto. inversion H4.
  - simp union. intuition auto. inversion H4.
  - rewrite <- Heqcall. clear Heqcall. apply splitWB in Heq as Heq'; auto. destruct Heq'.
    inversion H2. subst. remember unionWB. rewrite join_occurs; auto.
    apply abr_node in H3 as Habr1. apply abr_node in H4 as Habr2.
    apply split_abr in Heq as Heq'; auto.
    rewrite H; try tauto. rewrite H0; try tauto. intuition eauto using split_occurs.
    + apply occurs_rec in H21.
      intuition apply split_occurs_recipr with (x := x) in Heq; intuition auto.
    + apply occurs_rec in H21. intuition auto. 
Qed.

Lemma union_keeps_abr : forall T1 T2, WB T1 -> WB T2 -> abr T1 -> abr T2 -> abr (union T1 T2).
Proof.
  intros. funelim (union T1 T2).
  - rewrite <- Heqcall. auto.
  - simp union.
  - rewrite <- Heqcall. inversion H1. inversion H2. apply splitWB in Heq as Heq'; intuition.
    subst. apply split_abr in Heq as Heq'; intuition auto. apply abr_node in H4. intuition.
    apply join_abr; auto using unionWB.
    + unfold all_smallers. rewrite Forall_forall. intro. pose union_keeps_elts.
      unfold occurs in i. rewrite i; auto. intro Hocc.
      destruct Hocc as [ Hocc | Hocc ]; revert Hocc; generalize x; apply Forall_forall; auto.
      eapply split_smallers_greaters; try eexact Heq; eauto.
    + unfold all_greaters. rewrite Forall_forall. intro. pose union_keeps_elts.
      unfold occurs in i. rewrite i; auto. intro Hocc.
      destruct Hocc as [ Hocc | Hocc ]; revert Hocc; generalize x; apply Forall_forall; auto.
      eapply split_smallers_greaters; try eexact Heq; eauto.
Qed.

Theorem union_works : forall T1 T2,
    abr T1 -> abr T2 -> WB T1 -> WB T2 ->
    WB (union T1 T2) /\ abr (union T1 T2) /\ (forall x, x ∈ union T1 T2 <-> x ∈ T1 \/ x ∈ T2).
Proof.
  intuition auto using unionWB, union_keeps_abr; apply union_keeps_elts; auto.
Qed.

(*Inductive WTree : Z -> Set :=
| WLeaf : WTree 1
| WNode : forall n m, WTree n -> A -> WTree m -> WTree (n + m).

Equations translate {n: Z} (wt: WTree n) : Tree :=
| WLeaf => Leaf
| WNode _ _ l k r => Node (translate l) k (translate r).

Equations test (n: Z) (t: WTree n) : WTree n :=
| n, WLeaf => WLeaf
| n, WNode wl wr l k r with test wl l, test wr r => {
  | a, b => WNode wl wr a k b
  }.

Recursive Extraction translate.

Lemma weight_WTree : forall n (wt: WTree n), weight (translate wt) = n.
Proof.
  intros. funelim (translate wt).
  - simp translate weight. auto.
  - simp translate weight. rewrite H, H0. auto.
Qed.

Definition WTreeCast {n: Z} {m: Z} (H: n = m) (t: WTree n) : WTree m.
  rewrite <- H. exact t. Show Proof.
Qed.

Lemma wtree_assoc : forall a b c, WTree (a + b + c) = WTree (a + (b + c)).
Proof.
  intros. rewrite Z.add_assoc. auto. Show Proof.
Qed.

Equations Wrotate_left (n: Z) (l: WTree n) (v: A) (m: Z) (r: WTree m) : WTree (n + m) :=
| n, l, v, m, WLeaf => WNode n 1 l v WLeaf (* should not be called *)
| n, l, v, m, WNode wrl wrr rl rv rr =>
    WTreeCast (eq_sym (Z.add_assoc n wrl wrr)) (WNode (n + wrl) wrr (WNode n wrl l v rl) rv rr)
.

Equations Wrotate_right (n: Z) (l: WTree n) (v: A) (m: Z) (r: WTree m) : WTree (n + m) :=
| n, WLeaf, v, m, r => WNode 1 m WLeaf v r (* should not be called *)
| n, WNode wll wlr ll lv lr, v, m, r =>
    WTreeCast (Z.add_assoc wll wlr m) (WNode wll (wlr + m) ll lv (WNode wlr m lr v r))
.

(*Set Equations Debug.*)

Equations Wjoin_maybe_left_heavy (n: Z) (T__L: WTree n) (k: A) (m: Z) (T__R: WTree m) :
  WTree (n + m) :=
| n, T__L, k, m, T__R with not_left_heavyb n m => {
  | true => WNode n m T__L k T__R
  | false with T__L => {
    | WLeaf => WNode 1 m T__L k T__R (* absurde *)
    | WNode wl wc l k' c => WTreeCast (Z.add_assoc _ _ _) (
       match Wjoin_maybe_left_heavy wc c k m T__R in WTree x return WTree (wl + x) with
       | WLeaf => WNode wl 1 l k WLeaf (* absurde *)
       | WNode wl1 wr1 l1 k1 r1 =>
           match not_right_heavyb wl (wc + m) with
           | true => WNode wl (wl1 + wr1) l k' (WNode wl1 wr1 l1 k1 r1)
           | false =>
               match (like_weightsb wl wl1, like_weightsb (wl + wl1) wr1) with
               | (true, true) => Wrotate_left wl l k' (wl1 + wr1) (WNode wl1 wr1 l1 k1 r1)
               | (true, false) =>
                   Wrotate_left wl l k' (wl1 + wr1) (Wrotate_right wl1 l1 k1 wr1 r1)
               | (false, _) => Wrotate_left wl l k' (wl1 + wr1) (Wrotate_right wl1 l1 k1 wr1 r1)
               end
           end
       end)
    }
  }.

(*Equations Wjoin_maybe_left_heavy (n: Z) (T__L: WTree n) (k: A) (m: Z) (T__R: WTree m) :
  WTree (n + m) :=
| n, T__L, k, m, T__R with not_left_heavyb n m => {
  | true => WNode n m T__L k T__R
  | false with T__L => {
    | WLeaf => WNode 1 m T__L k T__R (* absurde *)
    | WNode wl wc l k' c with Wjoin_maybe_left_heavy wc c k m T__R => {
(*      | T' with T' => {
        | WLeaf => WNode (wl + wc) m T__L k T__R (* absurde *)
        | WNode wl1 wr1 l1 k1 r1 with not_right_heavyb wl (wc + m) => {
          | true => WNode wl (wc + m) l k' T'
          | false with like_weightsb wl wl1, like_weightsb (wl + wl1) wr1 => {
            | true, true => Wrotate_left wl l k' (wc + m) T'
            | true, false => Wrotate_left wl l k' (wl1 + wr1) (Wrotate_right wl1 l1 k1 wr1 r1)
            | false, _ => Wrotate_left wl l k' (wl1 + wr1) (Wrotate_right wl1 l1 k1 wr1 r1)
            }
          }
        }*)
      | WLeaf => _
      | WNode _ _ _ _ _ => WNode (wl + wc) m T__L k T__R
      }
    }
  }.*)

Lemma Wjoin_left_correct: forall {n} (T__L: WTree n) (k: A) {m} (T__R: WTree m),
    translate (Wjoin_maybe_left_heavy n T__L k m T__R) =
      join_maybe_left_heavy (translate T__L) k (translate T__R).
Proof.
  intros. funelim (Wjoin_maybe_left_heavy n T__L k m T__R).
  - rewrite <- Heqcall. simp join_maybe_left_heavy. repeat rewrite weight_WTree. rewrite Heq.
    simpl. simp translate. auto.
  - Search (not_left_heavy _ _). exfalso. rewrite <- not_left_heavy_equiv_false in Heq.
    contradict Heq. rewrite <- (weight_WTree _ T__R). apply left_heavy_Leaf_false.
  - rewrite <- Heqcall. clear Heqcall. remember (Wjoin_maybe_left_heavy wc c k m T__R).
    dependent destruction w.
    + rewrite <- (weight_WTree _ T__R) in *. rewrite <- (weight_WTree _ c) in *.
      remember (weight_ge_one (translate c)). remember (weight_ge_one (translate T__R)). lia.
    + inversion x. Print existT.
Qed.

(*
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

Definition join T__L k T__R :=
  if not_left_heavyb (weight T__L) (weight T__R)
  then join_maybe_right_heavy T__L k T__R
  else join_maybe_left_heavy T__L k T__R.*)
 *)

Open Scope Z_scope.

Inductive WTree : Set :=
| WLeaf : WTree
| WNode : WTree -> A -> Z -> WTree -> WTree.

Equations translate (t: WTree) : Tree :=
| WLeaf => Leaf
| WNode l k _ r => Node (translate l) k (translate r).

Equations weightW (t: WTree) : Z :=
| WLeaf => 1
| WNode l _ _ r => weightW l + weightW r.

Equations constant_weight (t: WTree) : Z :=
| WLeaf => 1
| WNode __ (* c'est absurde mais sinon ça marche pas... *) _ w _ => w.

Inductive WTreeCorrectWeights : WTree -> Prop :=
| CorrectLeaf : WTreeCorrectWeights WLeaf
| CorrectRec : forall l k (w: Z) r,
    WTreeCorrectWeights l -> WTreeCorrectWeights r -> w = weightW l + weightW r ->
    WTreeCorrectWeights (WNode l k w r).

Lemma WTreeCorrect_weight : forall t, WTreeCorrectWeights t -> constant_weight t = weightW t.
Proof.
  intros t H. induction H; auto.
Qed.

Lemma weightW_translate : forall t, weightW t = weight (translate t).
Proof.
  intros. funelim (translate t); auto.
  simp weightW weight. rewrite H, H0. auto.
Qed.

Lemma constant_weight_translate : forall t,
    WTreeCorrectWeights t -> constant_weight t = weight (translate t).
Proof.
  intros. rewrite WTreeCorrect_weight; auto using weightW_translate.
Qed.

Equations Wrotate_left (l: WTree) (v: A) (r: WTree) : WTree :=
| l, v, WLeaf => WLeaf (* should not be called *)
| l, v, WNode rl rv wr rr =>
    WNode (WNode l v (constant_weight l + constant_weight rl) rl) rv (constant_weight l + wr) rr
.

Equations Wrotate_right (l: WTree) (v: A) (r: WTree) : WTree :=
| WLeaf, v, r => WLeaf
| WNode ll lv wl lr, v, r =>
    WNode ll lv (wl + constant_weight r) (WNode lr v (constant_weight lr + constant_weight r) r)
.

Equations Wjoin_maybe_left_heavy (T__L: WTree) (k: A) (T__R: WTree) : WTree :=
| T__L, k, T__R with not_left_heavyb (constant_weight T__L) (constant_weight T__R) => {
  | true => WNode T__L k (constant_weight T__L + constant_weight T__R) T__R
  | false with T__L => {
    | WLeaf => WLeaf (* absurde *)
    | WNode l k' _ c with Wjoin_maybe_left_heavy c k T__R  => {
      | T' with T' => {
        | WLeaf => WLeaf (* absurde *)
        | WNode l1 k1 wT' r1 with not_right_heavyb (constant_weight l) wT' => {
          | true => WNode l k' (constant_weight l + wT') T'
          | false with like_weightsb (constant_weight l) (constant_weight l1),
              like_weightsb (constant_weight l + constant_weight l1) (constant_weight r1) => {
            | true, true => Wrotate_left l k' T'
            | _, _ => Wrotate_left l k' (Wrotate_right l1 k1 r1)
            }
          }
        }
      }
    }
  }.

Equations Wjoin_maybe_right_heavy (T__L: WTree) (k: A) (T__R: WTree) : WTree :=
| T__L, k, T__R with not_right_heavyb (constant_weight T__L) (constant_weight T__R) => {
  | true => WNode T__L k (constant_weight T__L + constant_weight T__R) T__R
  | false with T__R => {
    | WLeaf => WLeaf (* absurde *)
    | WNode c k' _ r with Wjoin_maybe_right_heavy T__L k c  => {
      | T' with T' => {
        | WLeaf => WLeaf (* absurde *)
        | WNode l1 k1 wT' r1 with not_left_heavyb (wT') (constant_weight r) => {
          | true => WNode T' k' (wT' + constant_weight r) r
          | false with like_weightsb (constant_weight r1) (constant_weight r),
              like_weightsb (constant_weight l1) (constant_weight r1 + constant_weight r) => {
            | true, true => Wrotate_right T' k' r
            | _, _ => Wrotate_right (Wrotate_left l1 k1 r1) k' r
            }
          }
        }
      }
    }
  }.

Definition Wjoin T__L k T__R :=
  if not_left_heavyb (constant_weight T__L) (constant_weight T__R)
  then Wjoin_maybe_right_heavy T__L k T__R
  else Wjoin_maybe_left_heavy T__L k T__R.

Lemma WTreeCorrect_join_left : forall T__L k T__R,
    WTreeCorrectWeights T__L -> WTreeCorrectWeights T__R ->
    WTreeCorrectWeights (Wjoin_maybe_left_heavy T__L k T__R).
Proof.
  intros. funelim (Wjoin_maybe_left_heavy T__L k T__R); rewrite <- Heqcall;
    auto using WTreeCorrectWeights.
  - constructor; auto. repeat rewrite -> WTreeCorrect_weight; auto.
  - inversion H. subst. intuition. rewrite Heq0 in *. inversion H2. subst. constructor; auto.
    rewrite WTreeCorrect_weight; auto.
  - inversion_clear H. subst. rewrite Heq2 in *. simp Wrotate_left. intuition.
    inversion_clear H3. subst. repeat rewrite WTreeCorrect_weight; auto.
    repeat constructor; simp weightW; auto using Z.add_assoc.
  - inversion_clear H. subst. rewrite Heq2 in *. intuition. inversion_clear H3. subst.
    destruct l1; simp Wrotate_right Wrotate_left; auto using WTreeCorrectWeights.
    inversion_clear H.
    repeat rewrite WTreeCorrect_weight; auto. subst. repeat constructor; simp weightW; auto.
    aac_reflexivity.
  - inversion_clear H. subst. rewrite Heq1 in *. intuition. inversion_clear H3. subst. destruct l1; simp Wrotate_right Wrotate_left; auto. inversion_clear H. subst.
    repeat rewrite WTreeCorrect_weight; auto. repeat constructor; auto. simp weightW.
    aac_reflexivity.
Qed.

Lemma Wjoin_left_translate : forall T__L k T__R,
    WTreeCorrectWeights T__L -> WTreeCorrectWeights T__R ->
    translate (Wjoin_maybe_left_heavy T__L k T__R) =
      join_maybe_left_heavy (translate T__L) k (translate T__R).
Proof.
  intros. funelim (Wjoin_maybe_left_heavy T__L k T__R); rewrite <- Heqcall.
  - do 2 rewrite constant_weight_translate in *; auto.
    simp translate join_maybe_left_heavy. rewrite Heq. auto.
  - do 2 rewrite constant_weight_translate in *; auto.
    simp translate join_maybe_left_heavy in *. rewrite Heq. auto.
  - do 2 rewrite constant_weight_translate in *; auto.
    simp translate in *. simp join_maybe_left_heavy. rewrite Heq0. simpl. inversion_clear H.
    intuition. rewrite <- H4. rewrite Heq. simp translate. simpl. auto.
  -  inversion H. subst. intuition. do 2 rewrite constant_weight_translate in *; auto.
    simp translate in *. simp join_maybe_left_heavy. rewrite Heq1. simpl.
    rewrite <- H2. rewrite Heq0. simp translate. simpl.
    replace (weight (Node (translate l1) k1 (translate r1))) with wT'.
    + rewrite Heq. simpl. auto.
    + apply eq_sym. change wT' with (constant_weight (WNode l1 k1 wT' r1)).
      rewrite constant_weight_translate; auto. rewrite <- Heq0. apply WTreeCorrect_join_left; auto.
  - inversion H. subst. pose (WTreeCorrect_join_left c k T__R). intuition. rewrite Heq2 in *.
    inversion H3. subst. do 3 rewrite constant_weight_translate in *; auto.
    simp join_maybe_left_heavy. rewrite Heq3. simpl. simp translate in *. simpl. rewrite <- H2.
    simpl. repeat rewrite weightW_translate in *. simp weight.
    rewrite Heq1. simpl. rewrite Heq0. simpl. rewrite Heq.
    simp Wrotate_left rotate_left translate. auto.
  - inversion H. subst. pose (WTreeCorrect_join_left c k T__R). intuition. rewrite Heq2 in *.
    inversion H3. subst. do 3 rewrite constant_weight_translate in *; auto.
    simp join_maybe_left_heavy. rewrite Heq3. simpl. simp translate in *. simpl. rewrite <- H2.
    simpl. repeat rewrite weightW_translate in *. simp weight.
    rewrite Heq1. simpl. rewrite Heq0. simpl. rewrite Heq. destruct l1; auto.
  - inversion H. subst. pose (WTreeCorrect_join_left c k T__R). intuition. rewrite Heq1 in *.
    inversion H3. subst. do 2 rewrite constant_weight_translate in *; auto.
    simp join_maybe_left_heavy. rewrite Heq2. simpl. simp translate in *. simpl. rewrite <- H2.
    simpl. repeat rewrite weightW_translate in *. simp weight.
    rewrite Heq0. simpl. rewrite Heq. simpl. destruct l1; auto.
Qed.

Lemma WTreeCorrect_join_right : forall T__L k T__R,
    WTreeCorrectWeights T__L -> WTreeCorrectWeights T__R ->
    WTreeCorrectWeights (Wjoin_maybe_right_heavy T__L k T__R).
Proof.
  intros. funelim (Wjoin_maybe_right_heavy T__L k T__R); rewrite <- Heqcall;
    auto using WTreeCorrectWeights.
  - constructor; auto. repeat rewrite -> WTreeCorrect_weight; auto.
  - inversion H0. subst. intuition. rewrite Heq0 in *. inversion H2. subst. constructor; auto.
    rewrite WTreeCorrect_weight; auto.
  - inversion_clear H0. subst. rewrite Heq2 in *. simp Wrotate_right. intuition.
    inversion_clear H3. subst. repeat rewrite WTreeCorrect_weight; auto.
    repeat constructor; simp weightW; auto using Z.add_assoc.
  - inversion_clear H0. subst. rewrite Heq2 in *. intuition. inversion_clear H3. subst.
    destruct r1; simp Wrotate_right Wrotate_left; auto using WTreeCorrectWeights.
    inversion_clear H4.
    repeat rewrite WTreeCorrect_weight; auto. subst. repeat constructor; simp weightW; auto.
    aac_reflexivity.
  - inversion_clear H0. subst. rewrite Heq1 in *. intuition. inversion_clear H3. subst.
    destruct r1; simp Wrotate_right Wrotate_left; auto. inversion_clear H4. subst.
    repeat rewrite WTreeCorrect_weight; auto. repeat constructor; auto. simp weightW.
    aac_reflexivity.
Qed.

Lemma Wjoin_right_translate : forall T__L k T__R,
    WTreeCorrectWeights T__L -> WTreeCorrectWeights T__R ->
    translate (Wjoin_maybe_right_heavy T__L k T__R) =
      join_maybe_right_heavy (translate T__L) k (translate T__R).
Proof.
  intros. funelim (Wjoin_maybe_right_heavy T__L k T__R); rewrite <- Heqcall.
  - do 2 rewrite constant_weight_translate in *; auto.
    simp translate join_maybe_right_heavy. rewrite Heq. auto.
  - do 2 rewrite constant_weight_translate in *; auto.
    simp translate join_maybe_right_heavy in *. rewrite Heq. auto.
  - do 2 rewrite constant_weight_translate in *; auto.
    simp translate in *. simp join_maybe_right_heavy. rewrite Heq0. simpl. inversion_clear H0.
    intuition. rewrite <- H4. rewrite Heq. simp translate. simpl. auto.
  -  inversion H0. subst. intuition. do 2 rewrite constant_weight_translate in *; auto.
    simp translate in *. simp join_maybe_right_heavy. rewrite Heq1. simpl.
    rewrite <- H2. rewrite Heq0. simp translate. simpl.
    replace (weight (Node (translate l1) k1 (translate r1))) with wT'.
    + rewrite Heq. simpl. auto.
    + apply eq_sym. change wT' with (constant_weight (WNode l1 k1 wT' r1)).
      rewrite constant_weight_translate; auto. rewrite <- Heq0. apply WTreeCorrect_join_right; auto.
  - inversion H0. subst. pose (WTreeCorrect_join_right T__L k c). intuition. rewrite Heq2 in *.
    inversion H1. subst. do 3 rewrite constant_weight_translate in *; auto.
    simp join_maybe_right_heavy. rewrite Heq3. simpl. simp translate in *. simpl. rewrite <- H3.
    simpl. repeat rewrite weightW_translate in *. simp weight.
    rewrite Heq1. simpl. rewrite Heq0.
    unfold join_maybe_right_heavy_clause_1_clause_2_clause_2_clause_1_clause_2_clause_2.
    rewrite Heq. simpl. simp Wrotate_left rotate_left translate. auto.
  - inversion H0. subst. pose (WTreeCorrect_join_right T__L k c). intuition. rewrite Heq2 in *.
    inversion H1. subst. do 3 rewrite constant_weight_translate in *; auto.
    simp join_maybe_right_heavy. rewrite Heq3. simpl. simp translate in *. simpl. rewrite <- H3.
    simpl. repeat rewrite weightW_translate in *. simp weight.
    rewrite Heq1. simpl. rewrite Heq0.
    unfold join_maybe_right_heavy_clause_1_clause_2_clause_2_clause_1_clause_2_clause_2.
    rewrite Heq. simpl. destruct r1; auto.
  - inversion H0. subst. pose (WTreeCorrect_join_right T__L k c). intuition. rewrite Heq1 in *.
    inversion H1. subst. do 3 rewrite constant_weight_translate in *; auto.
    simp join_maybe_right_heavy. rewrite Heq2. simpl. simp translate in *. simpl. rewrite <- H3.
    simpl. repeat rewrite weightW_translate in *. simp weight. rewrite Heq0. simpl.
    unfold join_maybe_right_heavy_clause_1_clause_2_clause_2_clause_1_clause_2_clause_2.
    rewrite Heq. simpl. destruct r1; auto.
Qed.

Theorem Wjoin_translate : forall T__L k T__R,
    WTreeCorrectWeights T__L -> WTreeCorrectWeights T__R ->
    translate (Wjoin T__L k T__R) = join (translate T__L) k (translate T__R).
Proof.
  intros. unfold Wjoin, join. repeat rewrite constant_weight_translate; auto.
  destruct (not_left_heavyb (weight (translate T__L)) (weight (translate T__R)));
    auto using Wjoin_left_translate, Wjoin_right_translate.
Qed.
