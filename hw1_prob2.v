(* this is the exercise/follow-along file *)
Require Import EqNat.
Require Import List.
Require Import Bool.
Require Export PropLogic.

(* Wanna write some exercies for the students in a way that they can use the definitions *)

(* function that return true if F is a well-formed formula *)


(* How can we generate the truth table? *)

Definition some_assignments : assignment := ((A 1), false)::((A 2), true)::nil.

Example suitable_ex : suitable (Negation (Atom (A 1))) some_assignments.
Proof. compute; intros H; inversion H. Qed.

Example models_ex : models (Negation (Atom (A 1))) some_assignments.
Proof. compute; reflexivity. Qed.

Example sat_ex : satisfiable (Negation (Atom (A 1))).
Proof. unfold satisfiable; exists some_assignments; compute; reflexivity. Qed.

Example unsat_ex : unsatisfiable (Negation (Disjunction (Atom (A 1)) (Negation (Atom (A 1))))).
Proof. 
  unfold unsatisfiable.
  unfold suitable.
  intros.
  simpl. simpl in H.
  destruct (find_assignment (A 1) a).
  destruct b; simpl; reflexivity.
  unfold not in H.
  assert (H1 : False -> None = Some false).
  + intros. inversion H0.
  + apply H1. apply H. reflexivity.
Qed.

Example valid_ex: valid (Disjunction (Atom (A 1)) (Negation (Atom (A 1)))).
Proof. rewrite -> tautology. apply unsat_ex. Qed.

Theorem suitable_subformula: forall F G a, ((subformula G F) = true) /\ (suitable F a) -> (suitable G a).   
Admitted.
  
Lemma beq_atomic_refl: forall A, beq_atomic A A = true.
Proof.
  intros.
  destruct A.
  simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma beq_formula_refl: forall F, (beq_formula F F)=true.
Proof.
  intros.
  induction F.
  simpl. rewrite beq_atomic_refl. reflexivity.
  simpl. rewrite -> IHF. reflexivity.
  simpl. rewrite -> IHF1. rewrite -> IHF2. simpl. reflexivity.
Qed.
  

(*Lemma sub_ex: forall G F, subformula G (Negation (Disjunction (Negation F) (Negation G))) = true.
Proof.
  intro G.
  induction G.
  simpl.
  rewrite beq_atomic_refl.
  intro F.
  rewrite orb_true_r.
  reflexivity.
  intro F.
  induction F.
  assert (beq_formula G (Disjunction (Negation F) (Negation (Negation G)))=false).
  apply 
  rewrite beq_formula_refl. simpl. rewrite -> orb_true_r. reflexivity.
  simpl.
  rewrite IHG.
  assert (beq_formula (Atom a) (Disjunction (Negation F) (Negation (Atom a)))=false).
  simpl. reflexivity.
  rewrite H0.
  assert (beq_formula (Atom a) (Negation F)=false).
  simpl. reflexivity.
  rewrite H1.
  destruct (subformula (Atom a) F).
  simpl. reflexivity. 
  simpl.
  assert (beq_atomic a a=true).
  destruct a.
  simpl. SearchAbout nat. rewrite <- beq_nat_refl. reflexivity.
  rewrite H2.
  reflexivity.
  simpl.
  assert (beq_formula G G=true).
  destruct G. simpl. reflexivity.*)


Theorem q21_h1: forall F G, valid(Negation (Disjunction (Negation F) (Negation G))) /\ valid(F) -> valid(G).
Proof.
  intros.
  inversion H.
  unfold valid in H1.
  unfold valid in H0.
  unfold valid.
  intros.
  assert (sub1: (subformula G (Negation (Disjunction (Negation F) (Negation G)))) = true).
    simpl.
    induction G. 
    simpl. destruct (subformula (Atom a0)). 
    simpl. reflexivity. simpl. unfold beq_atomic. destruct a0. assert ((beq_nat n n)=true). destruct n. reflexivity. simpl. reflexivity.
    destruct (beq_formula G (Negation (Disjunction (Negation F) (Negation G)))).
    reflexivity.
    destruct (beq_formula G (Disjunction (Negation F) (Negation G))).
    reflexivity.
    destruct (beq_formula G (Negation G)). destruct (beq_formula G (Negation F)).
    simpl. reflexivity.
    destruct (subformula G F). simpl. reflexivity. reflexivity.
    destruct (subformula G G). destruct (beq_formula G (Negation F)).
    reflexivity.
    destruct (subformula G F).
    reflexivity. reflexivity.
    destruct (beq_formula G (Negation F)).
    reflexivity.
    destruct (subformula G F).
    reflexivity.
    simpl. 
    induction G. simpl. destruct (subformula (Atom a0) F). 
    simpl. reflexivity. simpl. 

(* Not true. Can find a counterexample*)
Theorem q22_h1: forall F G, satisfiable(Negation (Disjunction (Negation F) (Negation G))) /\ satisfiable(F) -> satisfiable(G).

 
Theorem q23_h1: forall F G, valid(Negation (Disjunction (Negation F) (Negation G))) /\ satisfiable(F) -> satisfiable(G).
Proof.
  intros.
  inversion H.
  unfold valid in H0.
  unfold satisfiable.
  unfold satisfiable in H1.
  inversion H1.
  exists (x).
  intros.

