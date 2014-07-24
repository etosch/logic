Require Import EqNat.
Require Import List.
Require Import ListSet.

Inductive atomic :=
| A : nat -> atomic. 

(* not important *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP. apply HQ. apply HR. Qed.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HAB HBA].
  split.
  apply HBA.
  apply HAB. Qed.

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof.
  intros P. split.
  intros. apply H. intros. apply H.
Qed.


Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros.
  split.
  inversion H. rewrite <- H0. apply H1.
  inversion H. rewrite <- H0. apply H2.
Qed.  

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    apply or_intror. apply HP.
    apply or_introl. apply HQ. Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  intros H.
  split.
  inversion H.
  left. apply H0.
  inversion H0.
  right. apply H1.
  inversion H.
  left. apply H0.
  inversion H0.
  right. apply H2.
Qed.

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H. Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
    inversion H.
    right. reflexivity.
    left. reflexivity.
Qed.

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H. Qed.  

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q. intros H.
  intros negQ.
  unfold not.
  intros.
  apply H in H0.
  unfold not in negQ.
  apply negQ in H0.
  apply H0.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  inversion H.
  apply H1 in H0.
  apply H0.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra. Qed.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  (*Case "b = true".*) reflexivity.
  (*Case "b = false".*)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

(*Theorem false_beq_nat : forall n m : nat,
     n <> m -> beq_nat n m = false.
Proof.
  intros n m H.
  induction n.
    induction m.
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
    simpl.
    reflexivity.

    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    induction m.
    

Qed.*)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n , n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m1 Hm].
  exists (2 + m1).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  inversion H0 as [x1 Hx].
  apply Hx.
  apply H.
 Qed.

Definition excluded_middle := forall P:Prop, 
  P \/ ~P.

(*Theorem not_exists_dist : excluded_middle -> 
    forall (X:Type) (P : X -> Prop), ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intro.
  unfold excluded_middle in H.
  intros.
  unfold not.  
  intro.
  
  inversion H0.*)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop), 
          (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  (* -> *)
  intro.
  inversion H as [x0 Hw].
  inversion Hw.
  left.
  exists (x0).
  apply H0.
  right.
  exists (x0).
  apply H0.
  (* <- *)
  intro.
  inversion H.
  inversion H0 as [x0 Hw].
  exists (x0).
  left. apply Hw.
  inversion H0 as [x0 Hw].
  exists (x0).
  right. apply Hw.
Qed.

Lemma leibniz_equality : forall (X : Type) (x y: X), 
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intro. intro. intro. intro. intro P0. intro.
  rewrite <- H.
  apply H0.
Qed.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
  (* Case "n = 0".*)
    intros m.
    destruct m as [|m'].
    (*SCase "m = 0".*)
      left. reflexivity.
    (*SCase "m = S m'".*)
      right. intros contra. inversion contra.
  (*Case "n = S n'".*)
    intros m.
    destruct m as [|m'].
    (*SCase "m = 0".*)
      right. intros contra. inversion contra.
    (*SCase "m = S m'".*)
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal. apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined.

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2). (* observe what appears as a hypothesis *)
  (*Case "k1 = k2".*)
    rewrite <- e.
    symmetry. apply Hx1.
  (*Case "k1 <> k2".*)
    reflexivity. Qed.

Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  reflexivity.
  reflexivity.
Qed.


Lemma dist_and_or_eq_implies_and : forall P Q R,
       P /\ (Q \/ R) /\ Q = R -> P/\Q.
Proof.
  intros P Q R.
  intro.
  inversion H.
  split.
  apply H0.
  inversion H1.
  inversion H2.
  apply H4.
  rewrite H3.
  apply H4.
Qed.

 (*end of not important*)

Definition beq_atomic (a : atomic) (b : atomic) :=
  match a, b with
    | A n, A m => beq_nat n m
  end.

Theorem eq_atomic : forall a b : atomic, {a=b} + {a<>b}.
Proof.
  intros a b.
  induction a as [n].
  induction b as [m].
  induction n.
    induction m.
    



  intros a. 
  induction a as [n]; induction n as [|nn].
  intros b.
  destruct b as [m]; induction m as [|mm].
  left; reflexivity.
  destruct IHmm as [eq|neq].
  right. inversion eq. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.

  intros. destruct b as [m]; induction m as [|mm].
  right. unfold not; intros. inversion H.
(* stuck -- when this proof is done, we need to end it with "Defined"*)
Admitted.
    

Inductive formula :=
  | Atom : atomic -> formula 
  | Negation : formula -> formula
  | Disjunction : formula -> formula -> formula.

(* would have preferred notation, but I can't seem to get it to work *)
Definition Conjunction A B :=
  Negation (Disjunction (Negation A) (Negation B)).

Definition Implies A B :=
  Disjunction (Negation A) B.

(* check if they are syntactically equal *)
Fixpoint beq_formula (f : formula) (g : formula) :=
  match f, g with
    | Atom foo, Atom bar => beq_atomic foo bar
    | Negation foo, Negation bar => beq_formula foo bar
    | Disjunction foo boo, Disjunction far bar => andb (beq_formula foo far) (beq_formula boo bar)
    | _, _ => false
  end.

Fixpoint subformula (F : formula) (G : formula) : bool :=
  if beq_formula F G
  then true
  else match G with
         | Atom foo => false
         | Negation foo => subformula F foo
         | Disjunction foo bar => orb (subformula F foo) (subformula F bar)
       end.

Fixpoint count_atoms (a : atomic) (lst : list atomic) :=
  match lst with
    | nil => 0
    | h::tl => if (beq_atomic h a)
               then 1 + (count_atoms a tl)
               else count_atoms a tl
  end.

Fixpoint get_all_atoms (f : formula) : set atomic :=
  match f with
    | Atom foo => set_add foo empty_set
    | Negation foo => get_all_atoms foo
    | Disjunction foo bar => @set_union atomic (get_all_atoms foo) (get_all_atoms bar)
  end.

Definition get_unique_atoms (f : formula) := 
  unique_atoms (get_all_atoms f).

let f := fun (a : atomic) (b : boolean) 
         => fun (l : list (atomic * boolean)) => cons (a, b) l
in
Fixpoint generate_truth_table_rec (a : list atomic) : (list (list (atomic * boolean))) :=
  match a with
    | nil => [nil ; nil]
    | h::t => (concat (map (f h true) (generate_truth_table_rec t))
                      (map (f h false) (generate_truth_table_rec t)))
  end.

Definition generate_truth_table (f : formula) : list (list (atomic * boolean)) :=
  let atoms = (get_unique_atoms f)
  in generate_truth_table_rec atoms.
  

Fixpoint find_atomic l a :=
  match l with
    | nil => false
    | h::t => if (beq_atomic h a)
              then true
              else find_atomic t a
  end.

Fixpoint atom_intersection l1 l2 :=
  match l1 with
    | nil => nil
    | h::t => if (find_atomic l2 h)
              then h::(atom_intersection t l2)
              else atom_intersection t l2
end.

Fixpoint atom_subset l1 l2 :=
  match l1 with
    | nil => true
    | h::t => if (find_atomic l2 h)
              then (atom_subset t l2)
              else false
  end.

Definition atom_set_eq l1 l2 := andb (atom_subset l1 l2) (atom_subset l2 l1).

Definition min (F G : option bool) : option bool :=
  match F, G with 
    | _ , None | None, _ => None
    | _, Some false | Some false, _ => Some false
    | _, _ => Some true
  end.



Definition assignment := list (atomic * bool).

Fixpoint find_assignment (a : atomic) (assignments : assignment) : option bool :=
  match assignments with
    | nil => None
    | (b, truth_value)::tail => if beq_atomic a b
                                then Some truth_value
                                else find_assignment a tail
  end.



Check @set_union atomic.

Theorem atomic_eq_refl :
  forall x y : atomic, {x=y} + {x<>y}.
Proof.
  intros.
  destruct x; destruct y;
  induction n; induction n0.
  left. reflexivity. 
  right. unfold not.
  intro H; inversion H.
  right. intro H; inversion H.
  inversion IHn.
  destruct H.
  right. unfold not. intros. inversion H. apply 
  


Fixpoint eval_formula (phi : formula) (a : assignment) : option bool :=
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

Definition suitable (f : formula) (a : assignment) := eval_formula f a <> None.

Definition models (f : formula) (a : assignment) := eval_formula f a = Some true.

Definition satisfiable (f : formula) := exists a,
                                          suitable f a -> eval_formula f a = Some true.

Definition unsatisfiable (f : formula) := forall a,
                                            suitable f a -> eval_formula f a = Some false.

Definition valid (f : formula) := forall a,
                                    suitable f a -> eval_formula f a = Some true.

Definition form_equiv (F G : formula) a b :=
                          eval_formula F a = b <-> eval_formula G a = b.
                          

Lemma empty_assignment_not_suitable : forall F,
                                        eval_formula F nil = None -> ~ suitable F nil.
Proof.
  induction F as [|F' IHF| F' IHF];
  try (simpl; intros; unfold not; intros; compute in H0; apply H0 in H; inversion H);
  try (intros; unfold not; unfold suitable; unfold not; intros; apply H0 in H; inversion H).
Qed.

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
