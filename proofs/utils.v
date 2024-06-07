From BalancedTrees Require Import definitions.


(* Un lemme très simple, visant à simplifier impliquant des couples, notamment en ce qui
 concerne unzip *)

Lemma couple_to_fst_snd : forall {A B} {a: A} {b: B} {p}, (a, b) = p -> a = fst p /\ b = snd p.
  intros. rewrite <- H. simpl. auto.
Qed.

(* Une trichotomy un peu plus optimisée, pour aller plus vite dans les preuves avec les
fonction d'égalité et d'infériorité booléennes *)
Lemma opti_tricho : forall {a b}, (a =? b) = false -> (a <? b) = false -> b < a.
Proof.
  intros. apply Nat.eqb_neq in H. apply Nat.ltb_nlt in H0.
  destruct (Nat.lt_trichotomy a b); try contradiction. destruct H1; try contradiction.
  auto.
Qed.

Lemma ltb_neqb : forall {a b}, a <? b = true -> a =? b = false.
Proof.
  intros. apply Nat.eqb_neq, Nat.lt_neq, Nat.ltb_lt. auto.
Qed.

Lemma ltb_antisymm : forall {a b}, a <? b = true -> b <? a = false.
  intros. apply Nat.ltb_nlt, Nat.lt_asymm, Nat.ltb_lt. auto.
Qed.

Lemma occursb_list_correct : forall l x, occursb_list x l = true <-> (x ∈ l)%stdpp.
  intros. funelim (occursb_list x l).
  - easy.
  - intuition auto. apply Nat.eqb_eq in Heq. subst. constructor.
  - intuition auto. constructor. auto.
  - rewrite <- Heqcall. intuition try discriminate. apply Nat.eqb_neq in Heq0 as H2.
    inversion H1; auto. subst. rewrite Heqcall. simp occursb_list. rewrite Heq0. simpl.
    rewrite H0; auto.
Qed.

Lemma occursb_correct : forall t x, occursb x t = true <-> x ∈ t.
  intros. unfold occursb, occurs. remember (elements t). apply occursb_list_correct.
Qed.

(* Prouve une forme de récurrence sur occurs*)
Lemma occurs_rec : forall x t1 k t2, x ∈ (Node t1 k t2) <-> x = k \/ x ∈ t1 \/ x ∈ t2.
Proof.
  intros x t1 k t2. unfold occurs. funelim (elements (Node t1 k t2)); inversion eqargs.  subst. split.
  - intro.
    repeat (apply elem_of_app in H1; destruct H1);
      try apply elem_of_list_singleton in H1;
      auto. 
  - intro.
    repeat destruct H1 using or_ind;
      repeat rewrite elem_of_app;
      try apply elem_of_list_singleton in H1;
      auto.
Qed.

(* Si on met seulement l'équivalence dans [core], pour une raison que j'ignore, eauto ne
l'utilise pas. Je crée donc 2 versions implicatives*)
Lemma occurs_rec_direct : forall x t1 k t2, x ∈ Node t1 k t2 -> x = k \/ x ∈ t1 \/ x ∈ t2.
  apply occurs_rec.
Qed.

Lemma occurs_rec_recipr : forall x t1 k t2, x = k \/ x ∈ t1 \/ x ∈ t2 -> x ∈ Node t1 k t2.
  apply occurs_rec.
Qed.

#[export] Hint Resolve occurs_rec_direct occurs_rec_recipr: core.

Lemma smaller_trans : forall t x y, all_smallers t x -> x < y -> all_smallers t y.
Proof.
  unfold all_smallers. unfold gt.
  intuition. induction H; auto. constructor; auto. transitivity x; auto.
Qed.

Lemma greater_trans : forall t x y, all_greaters t x -> y < x -> all_greaters t y.
Proof.
  unfold all_greaters.
  intuition. induction H; auto. constructor; auto. transitivity x; auto.
Qed.

Open Scope stdpp_scope.

Lemma pairwise_transitive_singleton xs y zs :
  xs ≺ [y] → [y] ≺ zs → xs ≺ zs.
Proof.
  unfold "≺". intros Hl Hr x z.
  specialize (Hl x y).
  specialize (Hr y z).
  rewrite elem_of_list_singleton in *.
  eauto using Nat.lt_trans.
Qed.


Lemma pairwise_app_left_iff xs ys zs :
  xs ++ ys ≺ zs ↔ xs ≺ zs ∧ ys ≺ zs.
Proof.
  unfold list_pairwise. split; intros H.
  { split; intros x y ? ?; specialize (H x y);
    rewrite elem_of_app in H; tauto. }
  { intros x y. rewrite elem_of_app. firstorder. }
Qed.

Lemma pairwise_app_right_iff xs ys zs :
  xs ≺ ys ++ zs ↔ xs ≺ ys ∧ xs ≺ zs.
Proof.
  unfold list_pairwise. split; intros H.
  { split; intros x y ? ?; specialize (H x y);
    rewrite elem_of_app in H; tauto. }
  { intros x y. rewrite elem_of_app. firstorder. }
Qed.

Lemma pairwise_app_right_direct xs ys zs :
  xs ≺ ys ++ zs -> xs ≺ ys ∧ xs ≺ zs.
Proof.
  apply pairwise_app_right_iff.
Qed.

Lemma pairwise_app_right_recipr xs ys zs :
  xs ≺ ys /\ xs ≺ zs -> xs ≺ ys ++ zs.
Proof.
  apply pairwise_app_right_iff.
Qed.

Lemma Forall_lt_iff x ys :
  Forall (lt x) ys ↔ [x] ≺ ys.
Proof.
  rewrite Forall_forall. unfold list_pairwise. split; intros H.
  { intros x' y. rewrite elem_of_list_singleton. intros ->. eauto. }
  { intros y ?. specialize (H x y). rewrite elem_of_list_singleton in H.
    eauto. }
Qed.

Lemma Forall_lt_direct x ys :
  Forall (lt x) ys -> [x] ≺ ys.
Proof.
  apply Forall_lt_iff.
Qed.

Lemma Forall_lt_recipr x ys :
  [x] ≺ ys -> Forall (lt x) ys.
Proof.
  apply Forall_lt_iff.
Qed.

Lemma Forall_gt_iff x ys :
  Forall (gt x) ys <-> ys ≺ [x].
Proof. unfold gt.
  rewrite Forall_forall. unfold list_pairwise. split; intros H.
       - intros x0 y H'. rewrite elem_of_list_singleton. intros ->. auto.
       - intros y ?. specialize (H y x). rewrite elem_of_list_singleton in H. eauto.
Qed.

Lemma Forall_gt_direct x ys :
  Forall (gt x) ys -> ys ≺ [x].
Proof. apply Forall_gt_iff.
Qed.

Lemma sorted_app : forall xs ys, sorted xs -> sorted ys -> xs ≺ ys -> sorted (xs ++ ys).
Proof. intro xs. induction xs as [| x xs]; auto. intros ys Hxs Hys Hlt. simpl.
       dependent destruction Hxs. change (x :: xs) with ([x] ++ xs) in Hlt.
       rewrite Forall_lt_iff in *. apply pairwise_app_left_iff in Hlt. destruct Hlt.
       constructor; rewrite ?Forall_lt_iff, ?pairwise_app_right_iff; eauto.
Qed.

Lemma sorted_app_pw : forall xs ys, sorted (xs ++ ys) -> xs ≺ ys.
Proof.
  unfold "≺". intros. eapply elem_of_StronglySorted_app; eauto.
Qed.

Close Scope stdpp_scope.


Theorem abr_node : forall t1 k t2, abr (Node t1 k t2) <->
                                  abr t1 /\ abr t2 /\ all_smallers t1 k /\ all_greaters t2 k.
  intros. unfold abr. simp elements. split.
  - intuition eauto using StronglySorted_app_inv_l, StronglySorted_app_inv_r.
    + rewrite app_assoc in H. apply StronglySorted_app_inv_l, sorted_app_pw, Forall_gt_iff in H.
      auto.
    + apply StronglySorted_app_inv_r, sorted_app_pw, Forall_lt_recipr in H. auto.
  - intuition eauto 10 using sorted_app, StronglySorted, Forall_lt_direct, pairwise_app_right_recipr, pairwise_transitive_singleton, Forall_lt_direct, Forall_gt_direct.
Qed.

Lemma abr_lt_occurs : forall t1 k t2 x, abr (Node t1 k t2) -> x ∈ Node t1 k t2 -> x < k -> x ∈ t1.
Proof.
  intros. apply abr_node in H. intuition. apply occurs_rec in H0.
  intuition; absurd (x < k); subst; eauto using Nat.lt_irrefl.
  apply Nat.lt_asymm. eapply Forall_forall; eauto.
Qed.

Lemma abr_gt_occurs : forall t1 k t2 x, abr (Node t1 k t2) -> x ∈ Node t1 k t2 -> k < x -> x ∈ t2.
Proof.
  intros. apply abr_node in H. apply occurs_rec in H0.
  intuition; absurd (k < x); subst; eauto using Nat.lt_irrefl.
  apply Nat.lt_asymm. change (x < k) with (k > x). eapply Forall_forall; eauto.
Qed.

