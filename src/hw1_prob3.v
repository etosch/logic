Require Import EqNat.
Require Import List.
Require Import ListSet.
Require Import PropLogic.

Import ListNotations.

(* define when two assign. agree on the atomic formulas *)
Inductive in_assignment: atomic -> assignment -> Prop :=
| in1 : forall a tv,
          in_assignment a [(a, tv)]
| in2 : forall a b c,
          in_assignment a b -> in_assignment a (c::b).

Inductive suitable_2 : formula -> assignment -> Prop :=
| s1 : forall atm a b, 
         in_assignment atm a -> suitable_2 (Atom atm) a -> suitable_2 (Atom atm) (b::a)
| s2 : forall f a b,
         suitable_2 f a -> suitable_2 (Negation f) a -> suitable_2 (Negation f) (b::a)
| s3 : forall f g a b,
         suitable_2 f a /\ suitable_2 g a -> suitable_2 (Disjunction f g) a -> suitable_2 (Disjunction f g) (b::a).

(*   s1 : forall (a : assignment)  (atm : atomic), *)
(*          in_assignment atm a -> suitable_2 (Atom atm) a *)
(* | s2 : forall f a b, *)
(*          suitable_2 f a -> suitable_2 f (b::a). *)
(* | s2 : forall f a, *)
(*          suitable_2 f a -> suitable_2 (Negation f) a *)
(* | s3 : forall f g a, *)
(*          suitable_2 f a -> suitable_2 g a -> suitable_2 (Disjunction f g) a. *)

Inductive agree : assignment -> assignment -> list atomic -> Prop :=
  a1 : forall a b,
         agree a b []
| a2 : forall a b c d,
         agree a b c -> in_assignment d a /\ in_assignment d b -> agree a b (d::c).

Fixpoint atomicfs (f : formula) : list atomic :=
  match f with
    | Atom atm => [atm]
    | Negation f' => atomicfs f'
    | Disjunction f' g => atomicfs f' ++ atomicfs g
  end.

Lemma all_formulae_have_atoms: forall F,
                                 atomicfs F <> [].
Proof. 
  unfold not.
  induction F; try (intros; inversion H).
  apply IHF.
  apply H1.
  apply app_eq_nil in H1.
  inversion H1.
  generalize H0.
  apply IHF1.
Qed.

Lemma empty_assignment_not_suitable: forall F,
                                       suitable_2 F [] -> False.
Proof. 
  intros.
  inversion H.
Qed.  

Lemma suitable_atomic_bidirectional: forall a atm,
                                       suitable_2 (Atom atm) a -> in_assignment atm a.
  induction atm.
  intros.
  inversion H.
  apply in2.
  apply H1.
Qed.

Lemma atoms_negation_invariant: forall F,
                                  atomicfs F = atomicfs (Negation F).
Proof. 
  induction F; simpl; reflexivity.
Qed.

Lemma atoms_disjunction_invariant: forall F G,
                                     atomicfs F ++ atomicfs G = atomicfs (Disjunction F G).
Proof. 
  induction F; destruct G; simpl; reflexivity.
Qed.

Lemma negation_suitable_invariant: forall F a,
                                     suitable_2 F a <-> suitable_2 (Negation F) a.
Proof. 
  induction F.
  split; intros.
  induction a0.
  inversion H.
  apply s2.
Admitted.

Lemma suitable_invariant_under_assignment_aug: forall F a b,
                                                 suitable_2 F a -> suitable_2 F (b::a).
Proof. 
  induction a.
  intros.
  inversion H.
  intros.
  induction F; intros; simpl.
  apply s1. 
  apply suitable_atomic_bidirectional in H.
  apply H.
  apply H.
  apply s2.
  apply negation_suitable_invariant.
  apply H.
  apply H.
  inversion H.
  apply s3.
  split; inversion H2.
  generalize H5.
  apply IHF1.
  generalize H6.
  apply IHF2.
  

Lemma suitable_assignment_contains_all_atoms: forall F a atm,
                                                suitable_2 F a -> In atm (atomicfs F) -> in_assignment atm a.
Proof.
  induction F.
  intros.
  apply suitable_atomic_bidirectional.
  unfold atomicfs in H0.
  inversion H0.
  rewrite H1 in H.
  apply H.
  inversion H1. 
  intros.
  simpl in H0.
  induction a.
  inversion H.
  generalize H0.  
  apply negation_suitable_invariant in H.
  generalize H.
  apply IHF.
  intros.
  inversion H.
  simpl in H0.
  apply in_app_or in H0.
  inversion H0.
  generalize H6.
  inversion H3.
  

Lemma suitable_extract : forall a F atm,
                           suitable_2 F a -> (In atm (atomicfs F)) -> in_assignment atm a.
Proof. 
  intros.
  induction F.
  apply suitable_atomic_bidirectional in H.
  simpl in H0.
  inversion H0.
  rewrite <- H1.
  apply H.
  inversion H1.
  apply IHF.


Theorem hw1_prob3 : forall a b F,
                      (suitable F a) /\ (suitable F b) /\ agree a b (atomicfs F) -> ((eval_formula F a) = (eval_formula F b)).  
Proof. 
  intros; induction F.
