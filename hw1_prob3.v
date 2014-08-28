Require Import EqNat.
Require Import List.
Require Import ListSet.
Require Import PropLogic.

Import ListNotations.

(* define when two assign. agree on the atomic formulas *)
Inductive suitable_2 : formula -> assignment -> Prop :=
  s1 : forall (a : assignment)  (atm : atomic) (tv : bool),
         (In (atm, tv) a) -> suitable_2 (Atom atm) a
| s2 : forall f a,
         suitable_2 f a -> suitable_2 (Negation f) a
| s3 : forall f g a,
         suitable_2 f a -> suitable_2 g a -> suitable_2 (Disjunction f g) a.

Inductive agree : assignment -> assignment -> list atomic -> Prop :=
  a1 : forall a b,
         agree a b []
| a2 : forall a b c d tv,
         agree a b c -> (In (d, tv) a) /\ (In (d, tv) b) -> agree a b (d::c).

Fixpoint atomicfs (f : formula) : list atomic :=
  match f with
    | Atom atm => [atm]
    | Negation f' => atomicfs f'
    | Disjunction f' g => atomicfs f' ++ atomicfs g
  end.


Theorem hw1_prob3 : forall a b F,
                      (suitable F a) /\ (suitable F b) /\ agree a b (atomicfs F) -> ((eval_formula F a) = (eval_formula F b)).  
Proof. 
  intros; induction F.
