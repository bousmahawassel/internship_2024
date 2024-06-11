From BalancedTrees Require Import definitions utils.

Ltac get_couples :=
  match goal with
    | H: (_, _) = (_, _) |- _ => inversion H; subst end.

Definition is_higher_rank (k1 : option A) (k2 : option A) : Prop :=
  match k1, k2 with
  | Some k1, Some k2 => (rank_of k2 < rank_of k1) \/ (rank_of k1 = rank_of k2 /\ k1 < k2)
  | None, Some _ => True
  | _, None => False
  end.

Notation "k1 '≻' k2" := (is_higher_rank k1 k2) (at level 70).
Notation "k1 '!≻' k2" := (is_higher_rank (Some k1) (Some k2)) (at level 70).

Definition is_higher_rankb (k1: option A) (k2 : option A) : bool :=
  match k1, k2 with
  | Some k1, Some k2 => (rank_of k2 <? rank_of k1) || ((rank_of k1 =? rank_of k2) && (k1 <? k2))
  | None, Some _ => true
  | _, None => false
  end.

Notation "k1 '≻?' k2" := (is_higher_rankb k1 k2) (at level 70).
Notation "k1 '!≻?' k2" := (is_higher_rankb (Some k1) (Some k2)) (at level 70).

Lemma is_higher_rank_dec : forall k1 k2, k1 ≻ k2 <-> k1 ≻? k2 = true.
  intros k1 k2. destruct k1, k2; simpl; intuition try lia.
  - apply Nat.ltb_lt in H0. rewrite H0. apply orb_true_l.
  - apply Nat.ltb_lt in H1. apply Nat.eqb_eq in H. rewrite H, H1. simpl. apply orb_true_r.
  - apply orb_prop in H. intuition.
    + apply Nat.ltb_lt in H0. auto.
    + apply andb_prop in H0. intuition. apply Nat.eqb_eq in H. apply Nat.ltb_lt in H1. auto.
Qed.

Lemma is_higher_rank_tricho : forall k k0,
    is_higher_rank k k0 \/ k = k0 \/ is_higher_rank k0 k.
  intros. destruct k, k0; unfold is_higher_rank; auto.
  destruct (Nat.lt_trichotomy (rank_of a0) (rank_of a)) as [H | [H | H]]; auto.
    destruct (Nat.lt_trichotomy a a0) as [H0 | [H0 | H0]]; auto.
Qed.

Definition is_higher_rank_than_rootb (k : option A) (t: Tree) : bool :=
  match t with
  | Leaf => true
  | Node _ k1 _ => k ≻? (Some k1)
  end.

Definition is_higher_rank_than_root (k : option A) (t: Tree) : Prop :=
  match t with
  | Leaf => True
  | Node _ k1 _ => k ≻ (Some k1)
  end.

Ltac get_root :=
  match goal with
    | H : is_higher_rank_than_root _ (Node _ _ _) |- _ => unfold is_higher_rank_than_root in H end.

Lemma is_higher_rank_than_root_trans : forall t x x0,
    is_higher_rank x0 x ->
    is_higher_rank_than_root x t ->
    is_higher_rank_than_root x0 t.
  intros. destruct x, x0; destruct t; auto.
  - simpl. inversion H; inversion H0; intuition eauto using Nat.lt_trans; lia.
  - inversion H.
Qed.

Opaque is_higher_rank.

(* coupe t en 2 sous-arbre : les éléments plus petits et les éléments plus grands *)
Equations unzip (t: Tree) (k: A) : Tree * Tree :=
  | Leaf, k => (Leaf, Leaf)
  | Node t1 kt t2, k with (k =? kt, k <? kt) => {
    | (true, _) => (t1, t2)
    | (_, true) with unzip t1 k => {
        | (st1, gt1) => (st1, Node gt1 kt t2)
      }
    | _ with unzip t2 k => {
        | (st2, gt2) => (Node t1 kt st2, gt2)
      }
    }.

(*Goal forall a b, unzip t k = (a, b) -> occurs k t -> elements t = elements a ++ [k] ++ elements b
 Goal forall a b, unzip t k = (a, b) ->  ~ (occurs k t) -> elements t = elements a ++ elements b
 Goal forall a b, unzip t k = (a, b) ->  elements t = elements a ++ delta (occursb t k) k ++ elements b.
 *)

Equations insert (t: Tree) (k: A) : Tree :=
| Leaf, k => singleton_list k
| Node t1 kt t2, k with kt !≻? k => {
  | false with unzip (Node t1 kt t2) k => {
      | (st, gt) => Node st k gt
    }
  | true with kt <? k => {
    | false => Node (insert t1 k) kt t2
    | true => Node t1 kt (insert t2 k)
    }
  }.

Inductive heap: Tree -> Prop :=
| leaf_heap : heap Leaf
| rec_heap : forall t1 k t2,
    heap t1 -> heap t2 ->
    is_higher_rank_than_root (Some k) t1 -> is_higher_rank_than_root (Some k) t2 ->
    heap (Node t1 k t2).

Definition zip_tree (t: Tree) : Prop := heap t /\ abr t.

#[local] Hint Rewrite app_assoc: app.

Lemma unzip_elts_occurs_k : forall t k a b, abr t ->
    unzip t k = (a, b) -> occurs k t ->
    elements t = elements a ++ [k] ++ elements b.
Proof.
  intros t k. funelim (unzip t k); try easy.
  - intros. subst. rewrite Nat.eqb_eq in *. subst. rewrite <- Heqcall in *. get_couples. auto.
  - intros. rewrite <- Heqcall in *. get_couples. simp elements. autorewrite with app. repeat f_equal.
    rewrite <- app_assoc. apply abr_node in H1 as Habr. intuition. apply Hind; auto. apply Nat.ltb_lt in H0.
    eapply abr_lt_occurs; eauto.
  - intros. rewrite <- Heqcall in *. get_couples. simp elements.
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
  - intros. rewrite Nat.eqb_eq in *. subst. contradict H2. auto.
  - intros. rewrite <- Heqcall in *. get_couples. simp elements. autorewrite with app. repeat f_equal.
    apply abr_node in H1 as Habr. intuition. apply Hind; eauto.
  - intros. rewrite <- Heqcall in *. get_couples. simp elements.
    replace ((elements t1 ++ [kt] ++ elements st2) ++ elements b)
      with (elements t1 ++ [kt] ++ elements st2 ++ elements b)
      by autorewrite with app using auto.
    repeat f_equal. apply abr_node in H1 as Habr. intuition. apply Hind; eauto.
Qed.

Lemma unzip_elts_occursb : forall t k a b,
    abr t -> unzip t k = (a, b) -> elements t = elements a ++ delta (occursb k t) k ++ elements b.
  intros t k. remember (occursb k t). destruct b.
  - apply eq_sym, occursb_correct in Heqb. intros. simpl delta. apply unzip_elts_occurs_k; auto.
  - apply eq_sym in Heqb. intros. simpl. eapply unzip_elts_not_occurs_k; eauto. intro.
    apply occursb_correct in H1. congruence.
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

Lemma unzip_smallers : forall t k a b, abr t -> unzip t k = (a, b) -> all_smallers a k.
Proof.
  intros t k. funelim (unzip t k).
  -  simp unzip. intros. inversion H0. subst. constructor.
  - apply Nat.eqb_eq in H. subst. intros. apply abr_node in H. intuition. congruence.
  - intros. apply abr_node in H1. specialize (Hind st1 gt1). intuition. congruence.
  - intros. apply abr_node in H1. specialize (Hind st2 gt2). intuition. rewrite H2 in Heqcall. inversion Heqcall.
    subst. unfold all_smallers. simp elements. apply opti_tricho in H; auto.
    repeat (apply Forall_app; intuition eauto). eapply smaller_trans; eauto.
Qed.

Lemma unzip_greaters : forall t k a b, abr t -> unzip t k = (a, b) -> all_greaters b k.
Proof.
  intros t k. funelim (unzip t k).
  -  simp unzip. intros. inversion H0. subst. constructor.
  - apply Nat.eqb_eq in H. subst. intros. apply abr_node in H. intuition. congruence.
  - intros. apply abr_node in H1. specialize (Hind st1 gt1). intuition. rewrite H2 in Heqcall. inversion Heqcall.
    subst. unfold all_greaters. simp elements. apply Nat.ltb_lt in H0.
    repeat (apply Forall_app; intuition eauto). eapply greater_trans; eauto.
  - intros. apply abr_node in H1. specialize (Hind st2 gt2). intuition. congruence.
Qed.

Lemma insert_elts : forall t k a b,
    abr t -> unzip t k = (a, b) -> elements (insert t k) = elements a ++ [k] ++ elements b.
Proof.
  intros t k. funelim (insert t k).
  - simp unzip insert. intros. unfold singleton_list. inversion H0. auto.
  - rewrite <- Heqcall. intros. simp elements. remember (unzip t2 k). destruct p. specialize (H t t0).
    apply abr_node in H0 as Habr. intuition. rewrite H. simp unzip in H1. rewrite Nat.eqb_sym in *.
    apply ltb_neqb in Heq as Hneq. apply ltb_antisymm in Heq.
      rewrite Hneq, Heq in H1. simpl in H1. rewrite <- Heqp in H1. simpl in H1. get_couples. simp elements.
    repeat rewrite app_assoc. auto.
  - rewrite <- Heqcall. intros. unfold is_higher_rankb in *. assert (kt =? k = false).
    + apply Nat.eqb_neq. intro. subst. apply orb_prop in Heq0. intuition.
      * rewrite Nat.ltb_irrefl in *. discriminate.
      * apply andb_prop in H2. intuition. rewrite Nat.ltb_irrefl in *. discriminate.
    + apply opti_tricho in Heq; auto. simp elements. remember (unzip t1 k). destruct p. specialize (H t t0).
      apply abr_node in H0 as Habr. intuition. rewrite H. simp unzip in H1. rewrite Nat.eqb_sym in H2.
      rewrite H2 in *. apply Nat.ltb_lt in Heq. rewrite Heq in H1. simpl in H1. rewrite <- Heqp in H1.
      simpl in H1. get_couples. simp elements. autorewrite with app. auto.
  - rewrite <- Heqcall. rewrite Heq. simp elements. intros. inversion H0. subst. auto.
Qed.

Lemma insert_elts_set : forall t k x, abr t ->
    x ∈ insert t k <-> x ∈ t \/ x = k.
  unfold occurs. intros t k x H. remember (unzip t k). destruct p as [a b]. rewrite (insert_elts _ _ a b); auto.
  intuition.
  - repeat rewrite elem_of_app in H0. intuition.
    + rewrite (unzip_elts_occursb _ k a b); auto. repeat rewrite elem_of_app; auto.
    + apply elem_of_list_singleton in H0. auto.
    + rewrite (unzip_elts_occursb _ k a b); auto. repeat rewrite elem_of_app; auto.
  - rewrite (unzip_elts_occursb _ k a b) in H1; auto. repeat rewrite elem_of_app in *. intuition auto.
    destruct (occursb k t); simpl in *; auto.
    inversion H1.
  - repeat rewrite elem_of_app in *. rewrite elem_of_list_singleton. auto.
Qed.

Lemma insert_abr : forall t k,
    abr t -> abr (insert t k).
Proof. unfold abr.
  intros t k H. remember (unzip t k). destruct p as [a b].
  rewrite (insert_elts t k a b); auto. assert (Helts := H). rewrite (unzip_elts_occursb  _ k a b) in Helts; auto.
  assert (([k] ≺ elements b)%stdpp) by (eapply Forall_lt_direct, unzip_greaters; eauto).
  repeat apply sorted_app; auto.
  - eapply unzip_preserves_abr_fst; eauto.
  - constructor; auto. constructor.
  - eapply unzip_preserves_abr_snd; eauto.
  - apply pairwise_app_right_recipr.
    assert (elements a ≺ [k])%stdpp by (eapply Forall_gt_direct, unzip_smallers; eauto).
    intuition eauto using pairwise_transitive_singleton.
Qed.

Lemma unzip_preserves_is_higher_rank_than_root_fst : forall t k a b x,
    unzip t k = (a, b) ->
    heap t ->
    is_higher_rank_than_root x t ->
    is_higher_rank_than_root x a.
Proof.
  intros t k a b x. destruct x.
  - funelim (unzip t k).
    + simp unzip. intros. inversion H. auto.
    + intros. inversion H1. apply Nat.eqb_eq in H. rewrite H0 in Heqcall. get_couples. get_root.
      eauto using is_higher_rank_than_root_trans.
    + rewrite <- Heqcall. intros. get_couples. specialize (Hind a gt1 a0). inversion H2. subst.
      get_root. intuition eauto using is_higher_rank_than_root_trans.
    + rewrite <- Heqcall. intros. inversion H1. intuition.
  - intros. destruct a; constructor.
Qed.

Lemma unzip_preserves_is_higher_rank_than_root_snd : forall t k a b x,
    unzip t k = (a, b) ->
    heap t ->
    is_higher_rank_than_root x t ->
    is_higher_rank_than_root x b.
Proof.
  intros t k a b x. destruct x.
  - funelim (unzip t k).
    + simp unzip. intros. inversion H. auto.
    + intros. inversion H1. apply Nat.eqb_eq in H. rewrite H0 in Heqcall. get_couples. get_root.
      eauto using is_higher_rank_than_root_trans.
    + rewrite <- Heqcall. intros. get_couples. auto.
    + rewrite <- Heqcall. intros. get_couples. specialize (Hind st2 b a0). inversion H2. subst.
      get_root. intuition eauto using is_higher_rank_than_root_trans.
  - intros. destruct b; constructor.
Qed.

Lemma unzip_preserves_heap_fst : forall t k a b, unzip t k = (a, b) -> heap t -> heap a.
Proof.
  intros t k a b. funelim (unzip t k).
  - simp unzip. intros. get_couples. auto.
  - rewrite <- Heqcall. intros. get_couples. inversion H1. auto.
  - rewrite <- Heqcall. intros. get_couples. specialize (Hind a gt1). inversion H2. intuition auto.
  - rewrite <- Heqcall. intros. get_couples. specialize (Hind st2 b). inversion H2.
    constructor; eauto using unzip_preserves_is_higher_rank_than_root_fst.
Qed.

Lemma unzip_preserves_heap_snd : forall t k a b, unzip t k = (a, b) -> heap t -> heap b.
Proof.
  intros t k a b. funelim (unzip t k).
  - simp unzip. intros. inversion H. auto.
  - rewrite <- Heqcall. intros. get_couples. inversion H1. auto.
  - rewrite <- Heqcall. intros. get_couples. specialize (Hind a gt1). inversion H2.
    constructor; eauto using unzip_preserves_is_higher_rank_than_root_snd.
  - rewrite <- Heqcall. intros. get_couples. specialize (Hind st2 b). inversion H2. intuition auto.
Qed.

Lemma insert_preserves_is_higher_rank_than_root : forall t k x,
    is_higher_rank_than_root x t ->
    is_higher_rank x (Some k) ->
    is_higher_rank_than_root x (insert t k).
Proof.
  unfold is_higher_rank_than_root. intros. destruct x.
  - destruct t.
    + simp insert. auto.
    + simp insert. remember (a0 !≻? k). destruct b; simpl.
      * apply eq_sym, is_higher_rank_dec in Heqb. destruct (a0 <? k); simpl; auto.
      * destruct (unzip (Node t1 a0 t2) k). simpl. auto.
  - destruct (insert t k); auto.
Qed.

Lemma insert_preserves_heap : forall t k, heap t -> heap (insert t k).
  intros t k. funelim (insert t k).
  - simp insert. constructor; simpl; auto.
  - intro. inversion H0. subst. intuition. rewrite <- Heqcall. apply is_higher_rank_dec in Heq0.
    constructor; auto using insert_preserves_is_higher_rank_than_root.
  - intro. inversion H0. subst. intuition. rewrite <- Heqcall. apply is_higher_rank_dec in Heq0.
    constructor; auto using insert_preserves_is_higher_rank_than_root.
  - intro H0.  inversion H0. subst. intuition. rewrite <- Heqcall. 
    constructor; eauto using unzip_preserves_heap_fst, unzip_preserves_heap_snd.
    + destruct (is_higher_rank_tricho (Some kt) (Some k)) as [Hrank | [Hrank | Hrank]].
      * apply is_higher_rank_dec in Hrank. congruence.
      * inversion Hrank. subst. simp unzip in Heq. rewrite Nat.eqb_refl in Heq. simpl in Heq. get_couples. auto.
      * eauto using unzip_preserves_is_higher_rank_than_root_fst.
    + destruct (is_higher_rank_tricho (Some kt) (Some k)) as [Hrank | [Hrank | Hrank]].
      * apply is_higher_rank_dec in Hrank. congruence.
      * inversion Hrank. subst. simp unzip in Heq. rewrite Nat.eqb_refl in Heq. simpl in Heq. get_couples. auto.
      * eauto using unzip_preserves_is_higher_rank_than_root_snd.
Qed.

Theorem insert_correct : forall t k,
    zip_tree t ->
    zip_tree (insert t k) /\ (forall y, y ∈ (insert t k) <-> occurs y t \/ y=k).
Proof.
  intros. unfold zip_tree in *. destruct H. auto using insert_preserves_heap, insert_abr, insert_elts_set.
Qed.
