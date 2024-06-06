From BalancedTrees Require Import definitions.


(* Un lemme très simple, visant à simplifier impliquant des couples, notamment en ce qui
 concerne unzip *)

Lemma couple_to_fst_snd : forall {A B} {a: A} {b: B} {p}, (a, b) = p -> a = fst p /\ b = snd p.
  intros. rewrite <- H. simpl. auto.
Qed.

(* Une trichotomy un peu plus optimisée, pour aller plus vite dans les preuves avec les
fonction d'égalité et d'infériorité booléennes *)
Lemma opti_tricho : forall {a b}, false = (a =? b) -> false = (a <? b) -> b < a.
Proof.
  intros. apply eq_sym in H, H0. apply Nat.eqb_neq in H. apply Nat.ltb_nlt in H0.
  destruct (Nat.lt_trichotomy a b); try contradiction. destruct H1; try contradiction.
  auto.
Qed.


(* Prouve une forme de récurrence sur occurs*)
Lemma occurs_rec : forall x t1 k r t2, x ∈ (Node t1 k r t2) <-> x = k \/ x ∈ t1 \/ x ∈ t2.
Proof.
  intros x t1 k r t2. unfold occurs. funelim (elements (Node t1 k r t2)); inversion eqargs.  subst. split.
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
Lemma occurs_rec_direct : forall x t1 k r t2, x ∈ Node t1 k r t2 -> x = k \/ x ∈ t1 \/ x ∈ t2.
  apply occurs_rec.
Qed.

Lemma occurs_rec_recipr : forall x t1 k r t2, x = k \/ x ∈ t1 \/ x ∈ t2 -> x ∈ Node t1 k r t2.
  apply occurs_rec.
Qed.

#[export] Hint Resolve occurs_rec_direct occurs_rec_recipr: core.

Lemma smaller_trans : forall t x y, all_smallers t x -> x < y -> all_smallers t y.
Proof.
  unfold all_smallers.
  intuition eauto using Nat.lt_trans.
Qed.
