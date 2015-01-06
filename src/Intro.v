(* this is the exercise/follow-along file *)
Require Import EqNat.
Require Import List.
Require Import Bool.
Require Export PropLogic.

(* Wanna write some exercies for the students in a way that they can use the definitions *)

(* function that return true if F is a well-formed formula *)

Definition WFF (f:formula) := true.

Eval simpl in WFF (Atom (A 1)).

Eval simpl in WFF (Negation (Atom (A 1))).

(* Eval simpl in WFF true. *)
(* Eval simpl in WFF (Negation (Atom (A 1)) (Atom (A 2))). *)

(* Examples of the evaluation of a formula, given it is a suitable assign.*)

Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), true)::((A 2), true)::nil).
Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), true)::((A 2), false)::nil).
Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), false)::((A 3), false)::nil).

Eval simpl in get_all_atoms (Disjunction (Negation (Atom (A 1))) (Disjunction (Atom (A 2)) (Atom (A 3)))).
Eval simpl in subformula (Atom (A 2)) (Disjunction (Negation (Atom (A 1))) (Disjunction (Atom (A 2)) (Atom (A 3)))).

Example ex1: subformula (Disjunction (Atom (A 1)) (Atom (A 2))) (Disjunction (Atom (A 3)) (Disjunction (Atom (A 1)) (Atom (A 2)))) = true.
Proof.
 simpl. reflexivity.
Qed.

Eval simpl in subformula (Negation (Atom (A 2))) (Disjunction (Negation (Atom (A 1))) (Disjunction (Atom (A 2)) (Atom (A 3)))).

Definition some_assignments : assignment := ((A 1), false)::((A 2), true)::nil.

(* illustration of semantic equality *)


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

Theorem atom_intersection_comm : forall a1 a2, 
                                   atom_set_eq (atom_intersection a1 a2) (atom_intersection a2 a1) = true.
Proof. 
  induction a1; induction a2.
  reflexivity.
  simpl. rewrite <- IHa2. simpl. reflexivity.
  simpl. rewrite IHa1. simpl. reflexivity.
  destruct (atom_intersection (a::a1) (a0::a2)) eqn:foo1.
  destruct (atom_intersection (a0::a2) (a::a1)) eqn:foo2.
  reflexivity.
  inversion foo2.

  unfold atom_set_eq.
  simpl.

  inversion foo.
  destruct (beq_atomic a0 a) eqn:bar.
  inversion H0.
  destruct (find_atomic a2 a) eqn:baz.
  inversion H0.
  rewrite H0.
  simpl.
  simpl. unfold atom_set_eq. unfold atom_subset. 
destruct (beq_atomic a0 a); destruct (beq_atomic a a0).

  
(*------*)
  
  induction F; destruct G.
  destruct (get_unique_atoms (Atom a)); destruct (get_unique_atoms (Atom a0));
   try reflexivity;
   try (induction l; try reflexivity; simpl; try apply IHl).
  destruct (beq_atomic a1 a2); destruct (beq_atomic a2 a1).
  

  
Theorem suitable_atomic_subset : forall F G,
                                   subformula F G = true -> 
                                   atom_intersection (get_unique_atoms F) (get_unique_atoms G) = get_unique_atoms F.
Proof. 
  intros.
  induction F.
  destruct G.
  destruct (get_unique_atoms (Atom a)) eqn:foo;
  destruct (get_unique_atoms (Atom a0)) eqn:bar;
  simpl; (try reflexivity).
  simpl.
'  

Theorem suitable_subformula: forall F G a, ((subformula G F) = true) /\ (suitable F a) -> (suitable G a).   
Proof. 
  intros.
  inversion H.
  unfold suitable.
  unfold suitable in H1.
  
  induction G.
  

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
  

Lemma sub_ex: forall G F, subformula G (Negation (Disjunction (Negation F) (Negation G))) = true.
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
    destruct G. simpl. reflexivity.




