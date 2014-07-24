Require Import EqNat.
Require Import List.

(* syntax of propositional logic, Schoening p 4, lecture notes *)

Inductive atomic :=
| A : nat -> atomic. 

Inductive formula :=
  | Atom : atomic -> formula 
  | Negation : formula -> formula
  | Disjunction : formula -> formula -> formula.

Definition beq_atomic (a : atomic) (b : atomic) :=
  match a, b with
    | A n, A m => beq_nat n m
  end.

(* semantics *)
Definition assignment := list (atomic * bool).

Fixpoint find_assignment (a : atomic) (assignments : assignment) : option bool :=
  match assignments with
    | nil => None
    | (b, truth_value)::tail => if beq_atomic a b
                                then Some truth_value
                                else find_assignment a tail
  end.


Fixpoint beq_formula (f : formula) (g : formula) :=
  match f, g with
    | Atom foo, Atom bar => beq_atomic foo bar
    | Negation foo, Negation bar => beq_formula foo bar
    | Disjunction foo boo, Disjunction far bar => andb (beq_formula foo far) (beq_formula boo bar)
    | _, _ => false
  end.

Fixpoint subformula (F : formula) (G : formula) : bool :=
  (* checks whether F is a subformula of G *)
  if beq_formula F G
  then true
  else match G with
         | Atom foo => false
         | Negation foo => subformula F foo
         | Disjunction foo bar => orb (subformula F foo) (subformula F bar)
       end.

(* relational definition *)
Inductive subformulaR : formula -> formula -> Prop :=
| R_Atom : forall a b,
             beq_atomic a b = true -> subformulaR (Atom a) (Atom b)
| R_Negation : forall f,
                 subformulaR f (Negation f)
| R_Disjunction_L : forall f g,
                      subformulaR f (Disjunction f g)
| R_Disjunction_R : forall f g,
                      subformulaR g (Disjunction f g).




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
Example simple_proof : 
  eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), true)::((A 2), true)::nil) = Some false.
  reflexivity.
Qed.

Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), true)::((A 2), false)::nil).
Eval simpl in eval_formula (Negation (Disjunction (Atom (A 1)) (Atom (A 2)))) 
                           (((A 1), false)::((A 2), false)::nil).

(* computational model *)
Definition suitable (f : formula) (a : assignment) := eval_formula f a <> None.

(* Inductive suitableR : formula -> assignment -> Prop := *)
(* | R_Atom : forall (f : formula) (atom : atomic) (a : assignment), *)
(*              find_assignment atom a = true -> formula_eq atom f = true -> suitableR f a *)
(* | R_Negation : forall (f : formula) (atom : atomic) (a : assignment), *)
(*                  find_assignment atom a = true ->  *)

Definition models (f : formula) (a : assignment) := eval_formula f a = Some true.

Definition satisfiable (f : formula) := exists a,
                                          suitable f a -> eval_formula f a = Some true.

Definition unsatisfiable (f : formula) := forall a,
                                            suitable f a -> eval_formula f a = Some false.

Definition valid (f : formula) := forall a,
                                    suitable f a -> eval_formula f a = Some true.

(* Illustrate some examples *)

Definition some_assignments : assignment := ((A 1), false)::((A 2), true)::nil.

Example suitable_ex : suitable (Negation (Atom (A 1))) some_assignments.
Proof. compute; intros H; inversion H. Qed.

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

Lemma empty_assignment_not_suitable : forall F,
                                        eval_formula F nil = None -> ~ suitable F nil.
Proof.
  induction F as [|F' IHF| F' IHF];
  try (simpl; intros; unfold not; intros; compute in H0; apply H0 in H; inversion H);
  try (intros; unfold not; unfold suitable; unfold not; intros; apply H0 in H; inversion H).
Qed.

(* Schoening, p 9 : A formula F is a tautology iff ~F is unsat *)
(* Lemma not_unsat_sat : forall F, *)
(*                         ~ (unsatisfiable F) -> exists a, *)
                                                 
Lemma  suitable_invariant_negation : forall F a,
                                       suitable F a <-> suitable (Negation F) a.
Proof. 
  intros. split.
  + induction F; unfold suitable; unfold not; intros;  simpl in H; simpl in H0.
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
  + induction F; unfold suitable; unfold not; intros.
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

Lemma eval_Negation: forall (b:bool) (F:formula) (a:assignment), suitable F a -> ((eval_formula F a = Some b) <-> (eval_formula (Negation F) a = Some (negb b))).  
Proof.
  intros.
  split.
  unfold suitable in H. intros.
  destruct F.
  (* atom *)
  simpl. simpl in H0. rewrite H0. destruct b; simpl; reflexivity.
  (* negation *)
  simpl. simpl in H0. simpl in H. 
    destruct (eval_formula F a). 
     destruct b. simpl. 
      destruct b0. simpl. rewrite <- H0; simpl. reflexivity. simpl. reflexivity.
      destruct b0. simpl. reflexivity. simpl. rewrite <- H0. simpl. reflexivity.
     inversion H0. 
  (* disjunction *)
  simpl. simpl in H. simpl in H0. 
    destruct (eval_formula F1 a).
     destruct (eval_formula F2 a).
      destruct b.
       simpl. destruct b0. simpl. reflexivity. simpl. simpl in H0. destruct b1. simpl. reflexivity. simpl. rewrite H0. reflexivity.
       simpl. destruct b0. simpl. simpl in H0. rewrite H0. reflexivity. simpl. simpl in H0. destruct b1. simpl. rewrite H0. reflexivity. simpl. reflexivity.
      inversion H0.
      inversion H0.
  simpl. unfold suitable in H.
  intros.
  destruct (eval_formula F a).
   destruct b. 
    destruct b0. reflexivity. simpl in H0. rewrite H0. reflexivity. 
    destruct b0. simpl in H0. rewrite H0. reflexivity. reflexivity.
   inversion H0.
Qed.

Theorem tautology : forall F,
                      valid F <-> unsatisfiable (Negation F).
Proof. 
  intros.  
  split.
  (* -> *)
  unfold unsatisfiable.
  unfold valid.
  intros.
  destruct F;
    unfold eval_formula;
    unfold eval_formula in H;
    rewrite <- suitable_invariant_negation in H0;
    apply H in H0;
    rewrite H0;
    simpl; reflexivity.
  (* <- *)
  unfold unsatisfiable.
  unfold valid.
  intros.
  rewrite suitable_invariant_negation in H0.
  apply H in H0.
  rewrite eval_Negation.
  rewrite H0.
  simpl.
  reflexivity.
  rewrite suitable_invariant_negation.
  unfold suitable.
  rewrite H0.
  unfold not.
  intros.
  inversion H1.
Qed.


Theorem suitable_subformula: forall F G a, ((subformula G F) = true) /\ (suitable F a) -> (suitable G a).   
Admitted.


(* Lemma suitable_invariant_disjunction : forall F G a,
                                         (suitable F a) /\ (suitable G a) <-> suitable (Disjunction F G) a.
Proof. 
 Admitted. *)


(* For every suitable assignment of Flist and G, if that assignment models each of the F's, then it also models G *)
(* need to figure out a better way of stating this than a list? *)
(* hinting toward the compactness theorem? *)
(* Theorem consequence : forall (G : formula) (Flist : list formula) *)

(* need to define "Big And" for arbitrary arity *)
(* maybe use dependent types? *)


(*Lemma cons_taut_equiv : forall F G,
                          consequence G F <-> tautology (Implies (BigConj F) G).
Lemma cons_unsat_equiv : forall F G,
                           consequence G F <-> unsatisifiable (Conjunction (BigConj F) (Negation G)).
Lemma taut_unsat_equiv : forall F G,
                           tautology (Implies (BigConj F) G) <-> unsatisifiable (Conjunction (BigConj F) (Negation G)).*)

                             
