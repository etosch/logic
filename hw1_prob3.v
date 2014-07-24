Require Import EqNat.
Require Import List.
Require Import ListSet.
Require Import PropLogic.

(* define when two assign. agree on the atomic formulas *)
Fixpoint get_all_atoms_assign (a : assignment) : set atomic :=
  match a with
    | nil => nil
    | (b, truth_value)::t => b::(get_all_atoms_assign t)
  end.

Fixpoint atoms_that_agree (a b : assignment) : set atomic :=
  match a with
    | nil => nil
    | a0::ta =>  

Theorem hw1_prob3 : forall a b F,
                      (suitable F a) /\ (suitable F b) /\ (agree(a b F) = true) -> ((eval_formula F a) = (eval_formula F b)).  
