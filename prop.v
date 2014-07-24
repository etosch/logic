Require Import EqNat.
Require Import List.
Require Import Peano.
(* syntax of propositional logic, Schoening p 4, lecture notes *)

Inductive atomic :=
| A : nat -> atomic. 

Definition beq_atomic (a : atomic) (b : atomic) :=
  match a, b with
    | A n, A m => beq_nat n m
  end.

Inductive formula :=
  | Atom : atomic -> formula 
  | Negation : formula -> formula
  | Disjunction : formula -> formula -> formula.

Fixpoint beq_formula (f : formula) (g : formula) :=
  match f, g with
    | Atom foo, Atom bar => beq_atomic foo bar
    | Negation foo, Negation bar => beq_formula foo bar
    | Disjunction foo boo, Disjunction far bar => andb (beq_formula foo far) (beq_formula boo bar)
    | _, _ => false
  end.

Fixpoint get_atoms (f : formula) : list atomic :=
  match f with
    | Atom foo => foo::nil
    | Negation foo => get_atoms foo
    | Disjunction foo bar => (get_atoms foo) ++ (get_atoms bar)
  end.

(* computational definition *)

Fixpoint subformula (F : formula) (G : formula) : bool :=
  (* checks whether F is a subformula of G *)
  if beq_formula F G
  then true
  else match G with
         | Atom foo => false
         | Negation foo => subformula F foo
         | Disjunction foo bar => orb (subformula F foo) (subformula F bar)
       end.

Inductive subformulaR : formula -> formula -> Prop :=
| R_Atom : forall a b,
             beq_atomic a b = true -> subformulaR (Atom a) (Atom b)
| R_Negation : forall f,
                 subformulaR f (Negation f)
| R_Disjunction_L : forall f g,
                      subformulaR f (Disjunction f g)
| R_Disjunction_R : forall f g,
                      subformulaR g (Disjunction f g).

Theorem comp_rel_subformula_eq : forall F G,
                                   subformula F G = true <-> subformulaR F G.
Proof. 
  intros. split.
  + intros.
    induction G.
    simpl in H.
    destruct (beq_formula F (Atom a)) eqn:foo.
    destruct F.
    generalize foo.
    apply R_Atom.
    inversion H.
    apply IHG in H.    
    generalize H. apply R_Negation.

Eval simpl in get_atoms (Disjunction (Negation (Atom (A 1))) (Disjunction (Atom (A 2)) (Atom (A 3)))).
Eval simpl in subformula (Atom (A 2)) (Disjunction (Negation (Atom (A 1))) (Disjunction (Atom (A 2)) (Atom (A 3)))).

Example ex1: subformula (Disjunction (Atom (A 1)) (Atom (A 2))) (Disjunction (Atom (A 3)) (Disjunction (Atom (A 1)) (Atom (A 2)))) = true.
Proof.
 simpl. reflexivity.
Qed.

Example ex2 : subformulaR (Disjunction (Atom (A 2)) (Atom (A 3))) (Disjunction (Atom (A 2)) (Atom (A 3))).

Eval simpl in subformula (Negation (Atom (A 2))) (Disjunction (Negation (Atom (A 1))) (Disjunction (Atom (A 2)) (Atom (A 3)))).

(* relational definition *)

Definition assignment := list (atomic * bool).

Fixpoint find_assignment (a : atomic) (assignments : assignment) : option bool :=
  match assignments with
    | nil => None
    | (b, truth_value)::tail => if beq_atomic a b
                                then Some truth_value
                                else find_assignment a tail
  end.

(* When we define the semantics of propositional logic, we do so by saying that there exists
   some function (which we call the assignment) of the atomic formulae, which we can expand to be
   true for all formulae built up from the atomic formulae. The function we define here in Coq
   works from the top-down, rather than from the bottom-up. Could we think of the informal proof
   as being like weak induction and the formal one as being like strong induction? Or this mostly 
   just the difference between using a function vs using propositions?
*)


Fixpoint eval_formula (phi : formula) (a : assignment) : option bool :=
  (* for now we use the option type to handle cases when the assignment isn't ... *)
  match phi with
    | Atom foo => find_assignment foo a
    | Negation foo => match (eval_formula foo a) with
                        | None => None
                        | Some x => Some (negb x)
                      end
    | Disjunction foo bar => match (eval_formula foo a) with
                               | None => None
                               | Some x => match (eval_formula bar a) with
                                             | None => None
                                             | Some y => Some (orb x y)
                                           end
                             end
  end.

Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), true)::((A 2), true)::nil).
Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), true)::((A 2), false)::nil).
Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), false)::((A 2), false)::nil).

(* computational models *)
Definition suitable1 (f : formula) (a : assignment) := eval_formula f a <> None.

Fixpoint suitable2 (f : formula) (a : assignment) :=
  match a with
    | nil => True
    | (literal, _)::tl => (In literal (get_atoms f)) /\ (suitable2 f tl)
  end.

Definition models (f : formula) (a : assignment) := eval_formula f a = Some true.

Definition satisfiable (f : formula) := exists a,
                                          suitable1 f a -> eval_formula f a = Some true.

Definition unsatisfiable (f : formula) := forall a,
                                            suitable1 f a -> eval_formula f a = Some false.

Definition valid (f : formula) := forall a,
                                    suitable1 f a -> eval_formula f a = Some true.

(* relational models *)

(* Inductive suitableR : formula -> assignment -> Prop := *)
(* | R_Atom : forall (f : formula) (atom : atomic) (a : assignment), *)
(*              find_assignment atom a <> None -> suitableR (Atom atom) a *)
(* | R_Negation : forall (f : formula) (atom : atomic) (a : assignment), *)
(*                  find_assignment atom a <> None -> suitableR f a -> suitableR (Negation f) a  *)
(* | R_Disjunction : forall (f g : formula) (atom : atomic) (a : assignment), *)
(*                     find_assignment atom a <> None -> suitableR f a -> suitableR g a -> suitableR (Disjunction f g) a. *)

(* Inductive satisfiableR : formula -> assignment -> Prop := *)
(* | R_Atom : forall (f : formula) (atom : atomic) (a : assignment), *)
(*              (suitableR f a) f atom a ->  *)

(* Illustrate some examples *)

Definition some_assignments : assignment := ((A 1), false)::((A 2), true)::nil.

Example suitable_ex : suitable1 (Negation (Atom (A 1))) some_assignments.
Proof. compute; intros H; inversion H. Qed.

(* Example suitableR_ex : suitableR (Negation (Atom (A 1))) some_assignments. *)
(* Proof.  *)
(*   unfold some_assignments. *)
(*   apply R_Negation with (atom:=(A 1)). *)
(*   compute; intros; inversion H. *)
(*   apply R_Atom. *)


Example models_ex : models (Negation (Atom (A 1))) some_assignments.
Proof. compute; reflexivity. Qed.

Example sat_ex : satisfiable (Negation (Atom (A 1))).
Proof. unfold satisfiable; exists some_assignments; compute; reflexivity. Qed.

(*Notation "'Conjunction' A B" := (Negation (Disjunction (Negation A) (Negation B))) (at level 85, left associativity).
Check (Conjunction (Atom (A 1)) (Atom (A 2))). *)

(* this is a candidate problem? *)
Example unsat_ex : unsatisfiable (Negation (Disjunction (Atom (A 1)) (Negation (Atom (A 1))))).
Proof. 
  unfold unsatisfiable.
  unfold suitable1.
  intros.
  simpl. simpl in H.
  destruct (find_assignment (A 1) a).
  destruct b; simpl; reflexivity.
  unfold not in H.
  assert (H1 : False -> None = Some false).
  + intros. inversion H0.
  + apply H1. apply H. reflexivity.
Qed.

Lemma empty_assignment_not_suitable : forall F,
                                        eval_formula F nil = None -> ~ suitable1 F nil.
Proof.
  induction F as [|F' IHF| F' IHF];
  try (simpl; intros; unfold not; intros; compute in H0; apply H0 in H; inversion H);
  try (intros; unfold not; unfold suitable; unfold not; intros; apply H0 in H; inversion H).
Qed.

(* Schoening, p 9 : A formula F is a tautology iff ~F is unsat *)
(* Lemma not_unsat_sat : forall F, *)
(*                         ~ (unsatisfiable F) -> exists a, *)
                                                 
Lemma  suitable_invariant_negation : forall F a,
                                       suitable1 F a <-> suitable1 (Negation F) a.
Proof. 
  intros. split.
  + induction F; unfold suitable1; unfold not; intros;  simpl in H; simpl in H0.
    (* atomic *)
    destruct (find_assignment a0 a).
    inversion H0.
    (* negation *)
    apply H; apply H0.
    destruct (eval_formula F a).
    inversion H0.
    (* disjunction *)
    apply H; apply H0.
    destruct (eval_formula F1 a).
    destruct (eval_formula F2 a).
    inversion H0.
    apply H; apply H0.
    apply H; apply H0.
  + induction F; unfold suitable1; unfold not; intros.
    (* atomic *)
    simpl in H0.
    destruct (find_assignment a0 a) eqn:stuff.
    inversion H0.
    apply H.
    simpl.
    rewrite stuff. 
    reflexivity.
    (* negation *)
    simpl in H0.
    destruct (eval_formula F a) eqn:stuff.
    inversion H0.
    apply H. 
    simpl.
    rewrite stuff.
    reflexivity.
    (* disjunction *)
    simpl in H. simpl in H0.
    destruct (eval_formula F1 a) eqn:stuff1.
    destruct (eval_formula F2 a) eqn:stuff2.
    inversion H0.
    apply H; apply H0.
    apply H; apply H0.
Qed.


Lemma atom_eq : forall a b,
                  beq_atomic a b = true -> a = b.
Proof. 
  intros.
  induction a. destruct b.
  inversion H. 
  apply beq_nat_true_iff in H1.
  rewrite H1. reflexivity.
Qed.  

Lemma eq_nat_beq : forall n m,
                     n = m -> beq_nat n m = true.
Proof. 
  intros. rewrite H. symmetry. apply beq_nat_refl.
Qed.  

Lemma subformula_atomic_reverse : forall a b,
                                    subformulaR (Atom a) (Atom b) -> beq_atomic a b = true.
Proof. 
  intros.
  destruct (Atom a).
  

  generalize a b.
  induction H.
  intros.
  


Lemma subformula_atom_subset: forall F G,
                                subformulaR F G -> 
                                forall a,
                                  In a (get_atoms F) -> In a (get_atoms G).
Proof.
  intros. induction F; induction G.
  simpl. left. simpl in H0. inversion H0.
  rewrite <- H1.  

