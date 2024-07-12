From Equations Require Import Equations.
From AAC_tactics Require Import AAC.
From BalancedTrees Require Import definitions utils joinWB.
Import Instances.P.

Inductive WTree : Set :=
| WLeaf : WTree
| WNode : WTree -> A -> positive -> WTree -> WTree.

Equations translate (t: WTree) : Tree :=
| WLeaf => Leaf
| WNode l k _ r => Node (translate l) k (translate r).

Equations weightW (t: WTree) : positive :=
| WLeaf => 1
| WNode l _ _ r => weightW l + weightW r.

Equations constant_weight (t: WTree) : positive :=
| WLeaf => 1
| WNode __ (* c'est absurde mais sinon ça marche pas... *) _ w _ => w.

Open Scope positive_scope.

Inductive WTreeCorrectWeights : WTree -> Prop :=
| CorrectLeaf : WTreeCorrectWeights WLeaf
| CorrectRec : forall l k w r,
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
    repeat constructor; simp weightW; aac_reflexivity.
  - inversion_clear H. subst. rewrite Heq2 in *. intuition. inversion_clear H3. subst.
    destruct l1; simp Wrotate_right Wrotate_left; auto using WTreeCorrectWeights.
    inversion_clear H.
    repeat rewrite WTreeCorrect_weight; auto. subst. repeat constructor; simp weightW; auto.
    aac_reflexivity.
  - inversion_clear H. subst. rewrite Heq1 in *. intuition. inversion_clear H3. subst. destruct l1; simp Wrotate_right Wrotate_left; auto. inversion_clear H. subst.
    repeat rewrite WTreeCorrect_weight; auto. repeat constructor; eauto. simp weightW.
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
    repeat constructor; simp weightW; aac_reflexivity.
  - inversion_clear H0. subst. rewrite Heq2 in *. intuition. inversion_clear H3. subst.
    destruct r1; simp Wrotate_right Wrotate_left; auto using WTreeCorrectWeights.
    inversion_clear H4.
    repeat rewrite WTreeCorrect_weight; auto. subst. repeat constructor; auto. simp weightW.
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
    rewrite Heq1. simpl. rewrite Heq0. simpl.
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
