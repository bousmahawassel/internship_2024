From Equations Require Import Equations.
From AAC_tactics Require Import AAC Instances.
From BalancedTrees Require Import definitions utils joinWB log.
Import Instances.All.

Equations join_maybe_left_heavy_cost (T__L: Tree) (k: A) (T__R: Tree) : nat :=
| T__L, k, T__R with not_left_heavyb (weight T__L) (weight T__R) => {
  | true => 0
  | false with T__L => {
    | Leaf => 0 (* absurde si WB *)
    | Node l k' c => S (join_maybe_left_heavy_cost c k T__R)
    }
  }.

Equations join_maybe_right_heavy_cost (T__L: Tree) (k: A) (T__R: Tree) : nat :=
| T__L, k, T__R with not_right_heavyb (weight T__L) (weight T__R) => {
  | true => 0
  | false with T__R => {
    | Leaf => 0 (* absurde si WB *)
    | Node c k' r => S (join_maybe_right_heavy_cost T__L k c)
    }
  }.

Definition join_cost T__L k T__R :=
  if not_left_heavyb (weight T__L) (weight T__R)
  then join_maybe_right_heavy_cost T__L k T__R
  else join_maybe_left_heavy_cost T__L k T__R.

Open Scope nat_scope.

Equations split_cost (T: Tree) (k: A) : nat :=
| Leaf, _ => 0
| Node l k' r, k with (k ?= k') => {
  | Eq => 0
  | Lt with split l k => {
    | (_, _, lr) => split_cost l k + join_cost lr k' r
    }
  | Gt with split r k => {
    | (rl, _, _) => split_cost r k + join_cost l k' rl
    }
  }.

Equations height (T: Tree) : nat :=
| Leaf => 0
| Node l _ r => S (max (height l) (height r)).

Open Scope positive_scope.

Open Scope log_scope.

Definition rank (t: Tree) := log (weight t).

Lemma rank_sumlog : forall l k r, rank (Node l k r) = log_sum (weight l) (weight r).
Proof.
  intros. unfold rank, log_sum. simp weight. auto.
Qed.

Lemma rank_weight_le : forall a b, rank a <= rank b <-> (weight a <= weight b)%positive.
Proof.
  unfold rank, le_log. simpl in *. tauto.
Qed.

Lemma rank_joinWB : forall A k B, WB A -> WB B -> rank (join A k B) = rank (Node A k B).
Proof.
  intros. unfold rank. repeat rewrite weight_elements. rewrite join_elts; auto.
Qed.

Lemma empty_rule : rank Leaf = as_log 0.
  auto.
Qed.

Lemma monotonicity : forall A k B, WB A -> WB B -> max_log (rank A) (rank B) <= rank (join A k B).
Proof.
  intros. rewrite rank_joinWB; auto. apply max_log_lub_iff_le. rewrite rank_sumlog.
  intuition.
  - apply log_sum_le_l.
  - apply log_sum_le_r.
Qed.

(* je réinterprète la règle de submodularity : les conditions 0 ≤ a - b sont transformées en
b ≤ a, pour ne pas avoir de problèmes dans nat *)

Lemma submodularity_decr : forall A e B A' B',
    WB A' -> WB B' -> rank A' <= rank A -> rank B' <= rank B -> rank (join A' e B') <= rank (Node A e B).
Proof.
  intros. rewrite rank_joinWB; auto. repeat rewrite rank_sumlog. rewrite rank_weight_le in H1, H2.
  rewrite H1, H2. easy.
Qed.

Lemma submodularity_incr : forall A e B A' B' x,
    WB A' -> WB B' -> rank A <= rank A' -> rank A' <= rank A + x ->
    rank B <= rank B' -> rank B' <= rank B + x -> rank (join A' e B') <= x + rank (Node A e B).
Proof.
  intros. rewrite rank_joinWB; auto. repeat rewrite rank_sumlog. destruct x.
  rewrite rank_weight_le in *. unfold rank in *. unfold add_log, le_log in H1, H2, H3, H4.
  simpl in *. rewrite H2. rewrite H4. rewrite log_sum_add_log. rewrite (Pos.mul_comm (weight B)).
  rewrite Pos.mul_comm. easy.
Qed.

Lemma balancing_rule : forall l k r,
    WB (Node l k r) -> 
    max_log (rank l) (rank r) + log 1 <= rank (Node l k r) /\
      rank (Node l k r) <= min_log (rank l) (rank r) + log 4.
Proof.
  intros. inversion H. subst. split.
  - aac_normalise. rewrite rank_sumlog. apply max_log_lub_iff_le.
    split; try apply log_sum_le_l; try apply log_sum_le_r.
  - rewrite <- add_min_log_distr_r. apply min_log_glb_iff_le. rewrite rank_sumlog.
    unfold rank, le_log. simpl. lia_autosolve.
Qed.

Lemma join_cost_rank_right_heavy : forall A k B,
    WB A -> WB B -> rank A <= rank B ->
    as_log (join_cost A k B) + 3 * rank A <= 3 * rank B.
Proof.
  unfold join_cost. intros. simpl in H1.
  assert (not_left_heavy (weight A) (weight B)) by (rewrite rank_weight_le in H1; lia_autosolve).
  rewrite not_left_heavy_equiv in H2. rewrite H2. clear H2.
  funelim (join_maybe_right_heavy_cost A k B); inversion_clear Heqcall; simp as_log in *; simpl;
    try solve [rewrite H1; aac_reflexivity].
  rewrite rank_sumlog in *. inversion_clear H1. intuition.
  destruct (le_log_dicho (rank T__L) (rank c)).
  - intuition. aac_rewrite H6. simp mul_log. aac_normalise. unfold log_sum, le_log, add_log.
    simpl. lia_autosolve. nia.
  - clear H. simp join_maybe_right_heavy_cost.
    assert (not_right_heavy (weight T__L) (weight c))
      by (rewrite rank_weight_le in H1; lia_autosolve).
    rewrite not_right_heavy_equiv in H. rewrite H. simpl. simp as_log. aac_normalise.
    rewrite <- not_right_heavy_equiv_false in *. simp mul_log. aac_normalise.
    unfold log_sum, rank, add_log, le_log. simpl. lia_autosolve.
    assert (2 * weight T__L <= weight c + weight r)%positive by lia. aac_rewrite H6.
    assert (weight T__L <= weight c + weight r)%positive by lia. aac_rewrite H7. aac_reflexivity.
Qed.

Lemma join_cost_rank_left_heavy : forall A k B,
    WB A -> WB B -> rank B <= rank A ->
    as_log (join_cost A k B) + 3 * rank B <= 3 * rank A.
Proof.
  unfold join_cost. intros. destruct (not_left_heavyb (weight A) (weight B)).
  {
    assert (not_right_heavy (weight A) (weight B))
      by (rewrite rank_weight_le in H1; lia_autosolve).
    simp join_maybe_right_heavy_cost. apply not_right_heavy_equiv in H2. rewrite H2. simpl.
    simp as_log. rewrite H1. aac_reflexivity.
  }
  funelim (join_maybe_left_heavy_cost A k B); rewrite <- Heqcall; simp as_log in *; simpl;
    try solve [rewrite H1; aac_reflexivity].
  rewrite rank_sumlog in *. inversion_clear H0. intuition.
  destruct (le_log_dicho (rank T__R) (rank c)).
  - intuition. aac_rewrite H6. simp mul_log. aac_normalise. unfold log_sum, le_log, add_log.
    simpl. lia_autosolve. nia.
  - clear H. simp join_maybe_left_heavy_cost.
    assert (not_left_heavy (weight c) (weight T__R))
      by (rewrite rank_weight_le in H0; lia_autosolve).
    rewrite not_left_heavy_equiv in *. rewrite H. simpl. simp as_log. aac_normalise.
    rewrite <- not_left_heavy_equiv_false in *. simp mul_log. lia_autosolve. aac_normalise.
    unfold log_sum, rank, add_log, le_log. simpl. 
    assert (2 * weight T__R <= weight l + weight c)%positive by lia. aac_rewrite H6.
    assert (weight T__R <= weight l + weight c)%positive by lia. aac_rewrite H7. aac_reflexivity.
Qed.

Lemma join_cost_rank : forall A k B,
    WB A -> WB B ->
    as_log (join_cost A k B) + 3 * min_log (rank A) (rank B) <= 3 * max_log (rank A) (rank B).
Proof.
  intros. destruct (le_log_dicho (rank A) (rank B)).
  - rewrite min_log_l; auto. rewrite max_log_r; auto. apply join_cost_rank_right_heavy; auto.
  - rewrite min_log_r; auto. rewrite max_log_l; auto. apply join_cost_rank_left_heavy; auto.
Qed.

Lemma height_rank : forall T, WB T -> as_log (height T) <= 3 * rank T.
Proof.
  intros. funelim (height T).
  - rewrite empty_rule. simp as_log. simp mul_log. apply add_log_le_l.
  - inversion_clear H1. intuition. rewrite rank_sumlog. simp as_log.
    rewrite as_log_max. rewrite <- add_max_log_distr_l. apply max_log_lub_iff_le. split.
    + rewrite H1. simp mul_log. aac_normalise. unfold rank, le_log, add_log. simpl.
      lia_autosolve. nia.
    + rewrite H. simp mul_log. aac_normalise. unfold rank, le_log, add_log. simpl.
      lia_autosolve. nia.
Qed.

Lemma rank_height : forall T, WB T -> rank T <= as_log (height T).
Proof.
  intros. funelim (height T).
  - rewrite empty_rule. easy.
  - inversion_clear H1. intuition. simp as_log. rewrite rank_sumlog. rewrite as_log_max.
    unfold log_sum, rank, add_log, le_log in *. simpl in *. lia.
Qed.

Lemma split_rank : forall T k a b c, WB T -> split T k = (a, b, c) -> rank a <= rank T /\ rank c <= rank T.
Proof.
  intros T k a b c H. funelim (split T k).
  - simp split. intros. inversion_clear H0. intuition reflexivity.
  - inversion_clear Heqcall. intros. inversion H0. subst. rewrite rank_sumlog.
    split; try apply log_sum_le_l; apply log_sum_le_r.
  - inversion_clear Heqcall. rewrite Heq in Hind. intros. inversion H0. subst. inversion_clear H.
    apply splitWB in Heq; auto. rewrite rank_joinWB; try tauto. specialize (Hind a b0 lr).
    repeat rewrite rank_sumlog. intuition.
    + rewrite H5. apply log_sum_le_l.
    + rewrite rank_weight_le in H7. rewrite H7. easy.
  - inversion_clear Heqcall. rewrite Heq in Hind. intros. inversion H0. subst. inversion_clear H.
    apply splitWB in Heq; auto. rewrite rank_joinWB; try tauto. specialize (Hind rl b0 c).
    repeat rewrite rank_sumlog. intuition.
    + rewrite rank_weight_le in H5. rewrite H5. easy.
    + rewrite H7. apply log_sum_le_r.
Qed.

Lemma join_weight : forall T__L k T__R, WB T__L -> WB T__R -> weight (join T__L k T__R) = weight (Node T__L k T__R).
Proof.
  intros. rewrite weight_elements. rewrite join_elts; auto. rewrite <- weight_elements.
  auto.
Qed.

Lemma split_weight : forall T k a b c,
    WB T -> split T k = (a, b, c) ->
    ((if b then id else Pos.succ) (weight T) = (weight a + weight c))%positive.
Proof.
  intros T k. funelim (split T k).
  - simp split. intros. inversion_clear H0. simp weight. simpl. auto.
  - inversion_clear Heqcall. intros. inversion_clear H0. simp weight. auto.
  - inversion_clear Heqcall. intros. inversion H0. subst. inversion_clear H.
    apply Hind in Heq as Hrec; auto. clear Hind.  destruct b0.
    + apply splitWB in Heq as HWB; auto. rewrite join_weight; intuition.
      simp weight. simpl in *. rewrite Hrec. aac_reflexivity.
    + apply splitWB in Heq as HWB; auto. rewrite join_weight; intuition. simp weight.
      rewrite <- Pos.add_succ_l. rewrite Hrec. aac_reflexivity.
  - inversion_clear Heqcall. intros. inversion H0. subst. inversion_clear H.
    apply Hind in Heq as Hrec; auto. clear Hind. apply splitWB in Heq as HWB; auto.
    rewrite join_weight; intuition. simp weight. destruct b0.
    + simpl in *. rewrite Hrec. aac_reflexivity.
    + rewrite <- Pos.add_succ_r. rewrite Hrec. aac_reflexivity.
Qed.

Lemma split_cost_split : forall T k a b c,
    WB T -> split T k = (a, b, c) -> as_log (split_cost T k) <= 3 * (rank a + rank c).
Proof.
  intros T k. funelim (split_cost T k).
  - simp split_cost as_log. unfold le_log. simpl. lia.
  - rewrite <- Heqcall. simp as_log. unfold le_log. simpl. lia.
  - inversion_clear Heqcall. simp split. rewrite Heq0. simpl. rewrite Heq. simpl. intros.
    inversion H1. subst. clear H1. inversion_clear H0. specialize (H a b0 lr). intuition.
    rewrite as_log_add. apply splitWB in Heq as HWB; intuition. rewrite rank_joinWB; auto.
    rewrite rank_sumlog. rewrite H. pose (join_cost_rank lr k' r). intuition.
    repeat rewrite mul_add_log_distrib_r. repeat rewrite <- add_log_assoc. apply add_le_log_mono_l.
    destruct (le_pos_dicho (weight lr) (weight r)).
    + rewrite min_log_l in *; auto. rewrite max_log_r in *; auto. aac_rewrite H6.
      apply mul_le_log_mono_l, log_sum_le_r.
    + assert (join_cost lr k' r = 0)%nat.
      * unfold join_cost. apply split_weight in Heq as Hw; auto.
        assert (weight lr <= weight l)%positive by (destruct b0; simpl in *; lia_autosolve).
        assert (not_left_heavy (weight lr) (weight r)) by lia_autosolve.
        rewrite not_left_heavy_equiv in H8. rewrite H8. clear H8.
        simp join_maybe_right_heavy_cost.
        assert (not_right_heavy (weight lr) (weight r)) by lia_autosolve.
        rewrite not_right_heavy_equiv in H8. rewrite H8. clear H8. simpl. easy.
      * rewrite H7. simp as_log. aac_normalise. apply mul_le_log_mono_l, log_sum_le_l.
  - inversion_clear Heqcall. simp split. rewrite Heq0. simpl. rewrite Heq. simpl. intros.
    inversion H1. subst. clear H1. inversion_clear H0. specialize (H rl b0 c). intuition.
    rewrite as_log_add. apply splitWB in Heq as HWB; intuition. rewrite rank_joinWB; auto.
    rewrite rank_sumlog. rewrite H. pose (join_cost_rank l k' rl). intuition.
    rewrite add_log_comm. repeat rewrite mul_add_log_distrib_r. rewrite add_log_assoc.
    apply add_le_log_mono_r. destruct (le_pos_dicho (weight l) (weight rl)).
    + assert (join_cost l k' rl = 0)%nat.
      * unfold join_cost. apply split_weight in Heq as Hw; auto.
        assert (weight rl <= weight r)%positive by (destruct b0; simpl in *; lia_autosolve).
        assert (not_left_heavy (weight l) (weight rl)) by lia_autosolve.
        rewrite not_left_heavy_equiv in H8. rewrite H8. clear H8.
        simp join_maybe_right_heavy_cost.
        assert (not_right_heavy (weight l) (weight rl)) by lia_autosolve.
        rewrite not_right_heavy_equiv in H8. rewrite H8. clear H8. simpl. easy.
      * rewrite H7. simp as_log. aac_normalise. apply mul_le_log_mono_l, log_sum_le_r.
    + rewrite min_log_r in *; auto. rewrite max_log_l in *; auto. aac_rewrite H6.
      apply mul_le_log_mono_l, log_sum_le_l.
Qed.

Lemma split_cost_rank : forall T k, WB T -> as_log (split_cost T k) <= 6 * rank T.
Proof.
  intros. remember (split T k). destruct p as [[a b] c]. apply eq_sym in Heqp.
  apply split_cost_split in Heqp as Hcost; auto. apply split_rank in Heqp; intuition.
  rewrite Hcost, H0, H1. rewrite mul_add_log_distrib_r, <- mul_add_log_distrib_l. easy.
Qed.

Definition le_pos_sumbool : forall a b, ({a <= b} + {b <= a})%positive.
  intros. remember (a ?= b). destruct c.
  - apply eq_sym, Pos.compare_eq in Heqc. left. lia.
  - apply eq_sym in Heqc. rewrite Pos.compare_lt_iff in Heqc. left. lia.
  - apply eq_sym in Heqc. rewrite Pos.compare_gt_iff in Heqc. right. lia.
Qed.

Equations size (T: Tree) : nat :=
| Leaf => 0
| Node l _ r => S (size l + size r).

Lemma size_weight : forall T, Pos.to_nat (weight T) = S (size T).
Proof.
  intro. funelim (size T); simp weight; auto.
  rewrite Pos2Nat.inj_add. rewrite H. rewrite H0. lia.
Qed.

Lemma join_size : forall A k B, WB A -> WB B -> size (join A k B) = size (Node A k B).
Proof.
  intros. simp size. apply Nat.succ_inj. rewrite <- size_weight. rewrite join_weight; auto.
  simp weight. rewrite Pos2Nat.inj_add. repeat rewrite size_weight. lia.
Qed.

Lemma split_size : forall T k a b c,
    WB T -> split T k = (a, b, c) -> size T = (if b then S else id) (size a + size c)%nat.
Proof.
  intros T k. funelim (split T k).
  - simp split. intros. inversion H0. simp size. auto.
  - inversion_clear Heqcall. intros. inversion H0. simp size. lia.
  - inversion_clear Heqcall. intros. inversion H0. inversion_clear H.
    apply Hind in Heq as Hrec; auto. inversion H0. subst. apply splitWB in Heq as HWB; intuition.
    rewrite join_size; auto. simp size. rewrite Hrec. destruct b0; simpl; lia.
  - inversion_clear Heqcall. intros. inversion H0. inversion_clear H.
    apply Hind in Heq as Hrec; auto. inversion H0. subst. apply splitWB in Heq as HWB; intuition.
    rewrite join_size; auto. simp size. rewrite Hrec. destruct b0; simpl; lia.
Qed.

Definition sum_size T1 T2 := (size T1 + size T2)%nat.

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

(*Lemma join_size_inf_noWB : forall A k B, (size (join A k B) <= size A + size B)%nat.
Proof.
  intros. unfold join. destruct (not_left_heavyb (weight A) (weight B)).
  - funelim (join_maybe_right_heavy A k B); try inversion_clear Heqcall; simp size.
Qed.*)

Lemma join_size_noWB : forall A k B, (size (join A k B) <= S (size A) + (size B))%nat.
Proof.
  intros. unfold join. destruct (not_left_heavyb (weight A) (weight B)).
  - elim_join_right; simp size; try lia.
    + rewrite Heq0 in *. simp size in *. lia.
    + rewrite Heq2 in *. simp rotate_right. simp size in *. lia.
    + rewrite Heq2 in *. destruct r1; simp rotate_left rotate_right size in *; try lia.
    + rewrite Heq1 in *. destruct r1; simp rotate_left rotate_right size in *; try lia.
  - elim_join_left; simp size; try lia.
    + rewrite Heq0 in *. simp size in *. lia.
    + rewrite Heq2 in *. simp rotate_left. simp size in *. lia.
    + rewrite Heq2 in *. destruct l1; simp rotate_right rotate_left size in *; try lia.
    + rewrite Heq1 in *. destruct l1; simp rotate_left rotate_right size in *; try lia.
Qed.

#[export] Instance add_nat_le_mono : Proper (le ==> le ==> le) Nat.add.
Proof.
  unfold Proper, "==>". intros. apply Nat.add_le_mono; auto.
Qed.

Lemma split_size_noWB : forall T k a b c, split T k = (a, b, c) -> (size a + size c <= size T)%nat.
Proof.
  intros T k. funelim (split T k); try inversion_clear Heqcall.
  - simp split. intros. inversion_clear H. simp size. auto.
  - intros. inversion_clear H. simp size. auto.
  - intros. inversion H. subst. clear H. apply Hind in Heq. simp size. rewrite join_size_noWB.
    lia.
  - intros. inversion H. subst. clear H. apply Hind in Heq. rewrite join_size_noWB. simp size.
    lia.
Qed.

Lemma split_weight_noWB : forall T k a b c,
    split T k = (a, b, c) -> (weight a + weight c <= 1 + weight T)%positive.
Proof.
  intros. rewrite Pos.add_1_l. rewrite Pos2Nat.inj_le, Pos2Nat.inj_succ, Pos2Nat.inj_add.
  repeat rewrite size_weight. apply split_size_noWB in H. lia.
Qed.

Equations? union_switch (T1 T2: Tree) : Tree by wf (sum_size T1 T2) lt :=
| Leaf, T2 => T2
| T1, Leaf => T1
| T1, Node L2 k R2 with inspect (split T1 k) => {
  | (L1, b, R1) eqn: Heq with le_pos_sumbool (weight L2) (weight L1),
      le_pos_sumbool (weight R2) (weight R1) => {
    | left _, left _ => join (union_switch L1 L2) k (union_switch R1 R2)
    | left _, right _ => join (union_switch L1 L2) k (union_switch R2 R1)
    | right _, left _ => join (union_switch L2 L1) k (union_switch R1 R2)
    | right _, right _ => join (union_switch L2 L1) k (union_switch R2 R1)
    }
  }.
Proof.
  all: apply split_size_noWB in Heq; unfold sum_size; simp size in *; lia.
Qed.

Lemma union_switch_WB : forall T1 T2, WB T1 -> WB T2 -> WB (union_switch T1 T2).
Proof.
  intros.
  funelim (union_switch T1 T2); try solve [simp union_switch]; try inversion_clear Heqcall;
    clear H1; inversion_clear H3; apply joinWB; apply splitWB in Heq; intuition.
Qed.

Equations? union_switch_cost (T1 T2: Tree) : nat by wf (sum_size T1 T2) lt :=
| Leaf, T2 => 0
| T1, Leaf => 0
| T1, Node L2 k R2 with inspect (split T1 k) => {
  | (L1, _, R1) eqn: Heq with le_pos_sumbool (weight L2) (weight L1),
      le_pos_sumbool (weight R2) (weight R1) => {
    | left _, left _ => split_cost T1 k
                       + join_cost (union_switch L1 L2) k (union_switch R1 R2)
                       + union_switch_cost L1 L2 + union_switch_cost R1 R2
    | left _, right _ => split_cost T1 k
                        + join_cost (union_switch L1 L2) k (union_switch R2 R1)
                        + union_switch_cost L1 L2 + union_switch_cost R2 R1
    | right _, left _ => split_cost T1 k
                        + join_cost (union_switch L2 L1) k (union_switch R1 R2)
                        + union_switch_cost L2 L1 + union_switch_cost R1 R2
    | right _, right _ => split_cost T1 k
                         + join_cost (union_switch L2 L1) k (union_switch R2 R1)
                         + union_switch_cost L2 L1 + union_switch_cost R2 R1
    }
  }.
Proof.
  all: apply split_size_noWB in Heq; unfold sum_size; simp size in *; lia.
Qed.

Equations? union_switch_bound (T1 T2: Tree) : logtype by wf (rank T1 + rank T2) lt_log :=
| Leaf, T2 => log 1
| T1, Leaf => log 1
| T1, Node L2 k R2 with inspect (split T1 k) => {
  | (L1, _, R1) eqn: Heq with le_pos_sumbool (weight L2) (weight L1),
      le_pos_sumbool (weight R2) (weight R1) => {
    | left _, left _ => 12 * log (weight T1)
                       + union_switch_bound L1 L2
                       + union_switch_bound R1 R2
    | left _, right _ => 12 * log (weight T1)
                        + union_switch_bound L1 L2
                        + union_switch_bound R2 R1
    | right _, left _ => 12 * log (weight T1)
                        + union_switch_bound L2 L1
                        + union_switch_bound R1 R2
    | right _, right _ => 12 * log (weight T1)
                         + union_switch_bound L2 L1
                         + union_switch_bound R2 R1
    }
  }.
Proof.
  all: apply split_weight_noWB in Heq; simp weight in *; repeat rewrite rank_sumlog.
  all: unfold rank, log_sum, lt_log; simpl; nia.
Qed.

Lemma union_switch_weight_le : forall T1 T2,
    WB T1 -> WB T2 -> (Pos.succ (weight (union_switch T1 T2)) <= weight T1 + weight T2)%positive.
Proof.
  intros.
  funelim (union_switch T1 T2);
    try solve [simp union_switch weight; lia];
    inversion_clear Heqcall; clear H1.
  all: inversion_clear H3; apply splitWB in Heq as HWB; intuition.
  all: rewrite join_weight; auto using union_switch_WB; simp weight.
  all: apply split_weight in Heq as Hw; auto; destruct b; simp weight in *; simpl in *; lia.
Qed.

Lemma union_switch_weight_ge : forall T1 T2,
    WB T1 -> WB T2 ->
    (weight T1 <= weight (union_switch T1 T2) /\ weight T2 <= weight (union_switch T1 T2))%positive.
Proof.
  intros. funelim (union_switch T1 T2);
    try solve [simp union_switch weight; lia];
    try inversion_clear Heqcall; clear H1; simp weight.
  all: inversion_clear H3; apply splitWB in Heq as HWB; intuition.
  all: rewrite join_weight; auto using union_switch_WB; simp weight.
  all: apply split_weight in Heq as Hw; auto; simp weight in *; destruct b; simpl in *; try lia.
Qed.

Lemma weight_size_le : forall T1 T2, (weight T1 <= weight T2)%positive -> (size T1 <= size T2)%nat.
Proof.
  intros. apply le_S_n. repeat rewrite <- size_weight. lia.
Qed.

Lemma recursive_union_switch_cost_bound : forall t a t0 k L1 L2 R1 R2,
    WB L2 -> WB R2 -> WB L1 -> WB R1 -> (weight L1 <= weight t + weight t0)%positive ->
    (weight R1 <= weight t + weight t0)%positive -> (weight L2 <= weight L1)%positive ->
    (weight R2 <= weight R1)%positive ->
    as_log (join_cost (union_switch L1 L2) k (union_switch R1 R2)) <= 6 * rank (Node t a t0).
Proof.
  intros. pose (join_cost_rank (union_switch L1 L2) k (union_switch R1 R2)).
    destruct (le_log_dicho (rank (union_switch L1 L2)) (rank (union_switch R1 R2))).
  - clear H3 H5. rewrite max_log_r in *; auto. rewrite min_log_l in *; auto. clear H7.
    rewrite add_log_le_r, l; auto using union_switch_WB. clear l.
    pose (union_switch_weight_le R1 R2). intuition. clear H H0 H1 H2. unfold rank. simp weight.
    assert (weight (union_switch R1 R2) <= weight R1 + weight R2)%positive by lia. clear H5.
    rewrite H. clear H.
    assert (weight R1 + weight R2 <= (weight t + weight t0) * (weight t + weight t0))%positive
      by nia. rewrite H. clear H4 H6 H.
    rewrite <- add_log_mul, mul_add_log_distrib_r, <- mul_add_log_distrib_l.
    reflexivity.
  - clear H4 H6. rewrite min_log_r in *; auto. rewrite max_log_l in *; auto. clear H7.
    pose (union_switch_weight_le L1 L2). intuition. unfold rank in *. simp weight.
    rewrite add_log_le_r, l; auto using union_switch_WB. clear H H0 H1 H2 l.
    assert (weight (union_switch L1 L2) <= weight L1 + weight L2)%positive by lia. clear H6.
    rewrite H. clear H.
    assert (weight L1 + weight L2 <= (weight t + weight t0) * (weight t + weight t0))%positive
      by nia. rewrite H. clear H H3 H5.
    rewrite <- add_log_mul, mul_add_log_distrib_r, <- mul_add_log_distrib_l. easy.
Qed.

Lemma union_switch_cost_bound : forall T1 T2,
    WB T1 -> WB T2 -> rank T2 <= rank T1 ->
    as_log (union_switch_cost T1 T2) <= union_switch_bound T1 T2.
Proof.
  intros. funelim (union_switch_cost T1 T2);
    try solve [simp union_switch_bound union_switch_cost as_log; easy]; inversion_clear Heqcall;
    clear H1; inversion_clear H3; apply splitWB in Heq as HWB; intuition;
    repeat rewrite as_log_add; rewrite split_cost_rank; auto; simp union_switch_bound;
    remember (inspect (split (Node t a t0) k)); destruct s; destruct x; destruct p; simpl;
    rewrite e in Heq; clear Heqs; inversion Heq; subst; rewrite Heq1; simpl; rewrite Heq0;
    change 12%nat with (6 + 6)%nat; rewrite mul_add_log_distrib_l; repeat rewrite <- add_log_assoc;
    apply add_le_log_mono_l; apply split_weight in e; intuition; simp weight in e.
  - rewrite H, H8. apply add_le_log_mono_r.
    destruct b; simpl in *; eapply recursive_union_switch_cost_bound; eauto; lia.
  - rewrite H0, H8. apply add_le_log_mono_r. unfold rank, le_log in H4. simpl in H4.
    simp weight in H4. destruct b; simpl in *; eapply recursive_union_switch_cost_bound; eauto;
      lia.
  - rewrite H, H8. apply add_le_log_mono_r. unfold rank, "<=" in H4. simpl in H4.
    simp weight in H4. destruct b; simpl in *; eapply recursive_union_switch_cost_bound; eauto;
      lia.
  - rewrite H, H8. apply add_le_log_mono_r. unfold rank, "<=" in H4. simpl in H4.
    simp weight in H4. destruct b; simpl in *; eapply recursive_union_switch_cost_bound; eauto;
      lia.
Qed.

Lemma union_cost_rank : forall T1 T2,
    WB T1 -> WB T2 -> rank T2 <= rank T1 ->
    as_log (union_switch_cost T1 T2) + 12 * (size T2 * rank T2) <= 12 * (size T2 * rank T1).
Proof.
  intros. rewrite union_switch_cost_bound; auto. funelim (union_switch_bound T1 T2).
  - simp union_switch_bound. rewrite H1. aac_reflexivity.
  - inversion_clear Heqcall. rewrite H1. aac_reflexivity.
  - inversion_clear Heqcall. clear H1. inversion_clear H3. apply splitWB in Heq as HWB; intuition.
    unfold rank in *. simp weight in *. simp size in *. remember 12%nat. simp mul_log.
    repeat rewrite ?mul_add_log_distrib_r, ?mul_add_log_distrib_l.
    assert (weight L2 + weight R2 <= 4 * weight L2)%positive by lia_autosolve. rewrite H0 at 1.
    assert (weight L2 + weight R2 <= 4 * weight R2)%positive by lia_autosolve. rewrite H9 at 1.
    apply split_weight in Heq as Hw; intuition. simp weight in Hw.
Abort.

Close Scope log_scope.
