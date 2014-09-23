Require Import List.
Require Import EqNat.

Definition alist := list (nat * bool).

Fixpoint in_assignment n (a : alist) : Prop :=
  match a with
    | nil => False
    | (h,_)::t => if beq_nat n h
                  then True
                  else in_assignment n t
  end.

Lemma in_empty : forall a, in_assignment a nil -> False.
  intros; compute in H; apply H.
Qed.

Fixpoint find_assignment n (a : alist) : in_assignment n a -> bool :=
  match a with
    | nil => fun pf => match (in_empty n) pf with end
    | (h, tv)::t => if beq_nat h n
                    then fun _ => tv
                    else find_assignment n t
  end.
