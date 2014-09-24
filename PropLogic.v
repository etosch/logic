Require Import EqNat.
Require Import List.
Require Import ListSet.
Require Import Coq.Bool.BoolEq.

Section background.

  Inductive atomic :=
  | A : nat -> atomic. 
  
  Definition beq_atomic (a : atomic) (b : atomic) :=
    match a, b with
      | A n, A m => beq_nat n m
    end.

  (* from Software Foundations: http://www.cis.upenn.edu/~bcpierce/sf/current/MoreLogic.html *)
  Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  Proof.
    (* WORKED IN CLASS *)
    intros n.
    induction n as [|n'].
    intros m.
    destruct m as [|m'].
    left. reflexivity.
    right. intros contra. inversion contra.
    intros m.
    destruct m as [|m'].
    right. intros contra. inversion contra.
    destruct IHn' with (m := m') as [eq | neq].
   left. apply f_equal. apply eq.
    right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
  Defined.

  (* This is needed to use ListSet *)
  Definition atomic_eq : forall a b : atomic, {a = b} + {a <> b}.
    decide equality.
    apply eq_nat_dec.
  Defined.

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

  Inductive eq_formula : formula -> formula -> Prop :=
  | atom_eq : forall a1 a2, a1 = a2 -> eq_formula (Atom a1) (Atom a2)
  | neg_eq : forall f g, eq_formula f g -> eq_formula (Negation f) (Negation g)
  | disj_eq : forall f g h, eq_formula f g -> eq_formula (Disjunction f h) (Disjunction g h).
  
  Fixpoint subformula (F : formula) (G : formula) : bool :=
    if beq_formula F G
    then true
    else match G with
           | Atom foo => false
           | Negation foo => subformula F foo
           | Disjunction foo bar => orb (subformula F foo) (subformula F bar)
         end.

  Inductive subformulaR: formula -> formula -> Prop :=
  | base_subf : forall f g, eq_formula f g -> subformulaR f g
  | neg_subf : forall f g, subformulaR f g -> subformulaR f (Negation g)
  | disj_subf : forall f g h, subformulaR f g -> subformulaR f (Disjunction g h).

  Fixpoint count_atoms (a : atomic) (lst : list atomic) :=
    match lst with
      | nil => 0
      | h::tl => if (beq_atomic h a)
                 then 1 + (count_atoms a tl)
                 else count_atoms a tl
    end.

  Fixpoint get_all_atoms_formula (f : formula) : set atomic :=
    match f with
      | Atom foo => set_add atomic_eq foo (@empty_set atomic)
      | Negation foo => get_all_atoms_formula foo
      | Disjunction foo bar => set_union atomic_eq (get_all_atoms_formula foo) (get_all_atoms_formula bar)
    end.

  Definition min (F G : option bool) : option bool :=
    match F, G with 
      | _ , None | None, _ => None
      | _, Some false | Some false, _ => Some false
      | _, _ => Some true
    end.

  (* This doesn't solve the problem we had before with defining things in terms of option types.
     It just temporarily commutes the problem. We will need to get dependent types working in order
     to really prove things in a way that looks like "informal" proofs. *)
  (* Inductive truth_value := *)
  (* | Top : True -> truth_value *)
  (* | TV : bool -> truth_value *)
  (* | Bot : False -> truth_value. *)
  
  Definition assignment : Set := list (atomic * bool).
  
  Fixpoint generate_all_assignments (a : list atomic) : (list assignment) :=
    let f := fun atm v assign => (atm, v)::assign
    in match a with
         | nil => nil::nil
         | h::t =>  let f' := f h
                    in (map (f' true) (generate_all_assignments t)) 
                         ++ (map (f' false) (generate_all_assignments t))
    end.

  Eval simpl in (generate_all_assignments ((A 3)::((A 2)::((A 1)::nil)))).

  (* Inductive in_assignment (a : atomic) : assignment -> Prop := *)
  (*   | asgn_found : forall h tv ays ays', *)
  (*                    h = a -> in_assignment a (ays'++(h,tv)::ays). *)

  Fixpoint in_assignment_bool (a : atomic) (ays : assignment) : bool :=
    match ays with
      | nil => false
      | (h,_)::t => if beq_atomic h a
                    then true
                    else in_assignment_bool a t
    end.

  Fixpoint in_assignment_prop (a : atomic) (ays : assignment) : Prop :=
    match ays with
      | nil => False
      | (h, _)::t => if beq_atomic h a 
                     then True
                     else in_assignment_prop a t
    end.

  Theorem in_assignment_bool_eq_in_assignment_prop : forall a ays, 
                                                       in_assignment_bool a ays = true <-> in_assignment_prop a ays.
  Proof.
    split.
    (* in_assignment_bool a ays = true -> in_assignment_prop a ays *)
    induction ays; intros.
    simpl in H; inversion H.    
    destruct a0.
    simpl.
    remember (beq_atomic a0 a) as hcmp.
    destruct hcmp.
    apply I.
    simpl in H.
    rewrite <- Heqhcmp in H.
    generalize H.
    apply IHays.
    (* in_assignment_prop a ays -> in_assignment_bool a ays = true *)
    induction ays; intros.
    simpl in H; inversion H.
    destruct a0.
    simpl.
    remember (beq_atomic a0 a) as hcmp.
    destruct hcmp.
    reflexivity.
    simpl in H.
    rewrite <- Heqhcmp in H.
    generalize H.
    apply IHays.
  Qed.

  (* Fixpoint in_assignment (a : atomic) (ays : assignment) : Prop := *)
  (*   match ays with *)
  (*     | nil => False *)
  (*     | (h,_)::t => if beq_atomic h a *)
  (*               then True *)
  (*               else in_assignment a t *)
  (*   end. *)

  Definition in_empty : forall a, in_assignment_prop a nil -> False.
    intros.
    inversion H.
  Qed.

  Lemma index_atomic_equal : forall n m,
                               n = m -> A n = A m.
    intros. rewrite H. reflexivity.
  Qed.

  Lemma beq_atomic_true : forall a,
                            beq_atomic a a = true.
    destruct a.
    simpl. apply beq_nat_true_iff. reflexivity.
  Qed.

  Lemma eq_beq_atomic_true : forall a b,
                               a = b -> beq_atomic a b = true.
    intros.
    rewrite H. apply beq_atomic_true.
  Qed.                          

  (* Lemma atomic_index_equal : forall n m, *)
  (*                              A n = A m -> n = m. *)
  (*   intros; induction n; remember m; destruct m as [|foo]. *)
  (*   rewrite Heqn. *)
  (*   reflexivity. *)
  (*   apply eq_beq_atomic_true in H.  *)
  (*   simpl in H. *)
  (*   rewrite Heqn in H. *)
  (*   inversion H. *)
  (*   rewrite Heqn0. *)
  (*   rewrite Heqn0 in H. *)
  (*   rewrite Heqn0 in IHn. *)
    

  (* Lemma in_assignment_head_or_tail: forall a t h tv, *)
  (*                                     in_assignment_prop a ((h,tv)::t) -> *)
  (*                                     a = h \/ in_assignment_prop a t. *)
  (*   intros. *)
  (*   unfold in_assignment_prop in H. *)
  (*   remember (beq_atomic h a). *)
  (*   destruct b. *)
  (*   destruct a; destruct h. *)
  (*   simpl in Heqb. *)
  (*   left. *)




  Lemma in_assignment_additive: forall a t h P,
                                  in_assignment_prop a t -> P -> (in_assignment_prop a (h::t) -> P).
    (* need to prive in_assignment_head_or_tail first *)
  Admitted.


  (* I think what we need here is to somehow provide a proof that 
     in_assignment_prop a t -> boolin_assignment_prop a t -> bool
     implies 
     in_assignment_prop a ((h, tv) :: t) -> bool *)
  Fixpoint find_assignment (a : atomic) (ays : assignment) : in_assignment_prop a ays -> bool :=
    match ays with
      | nil => fun pf => match (in_empty a) pf with end
      | (h,tv)::t => if beq_atomic a h
                     then fun _ => tv
                     else in_assignment_additive a t (h,tv) bool (find_assignment a t) 
    end.

  Definition get_first_atom_in_assignment (ays : assignment) :=
    match ays with
      | nil => None
      | (h,_)::t => Some h
    end.

  (* Lemma in_assignment_head_or_rest : forall a b ays, *)
  (*                                      in_assignment a ays -> *)
  (*                                      get_first_atom_in_assignment ays = Some a  *)
  (*                                      \/ in_assignment a (b::ays). *)
  (*   intros. *)
    
    


  (* Lemma in_assignment_additive : forall a h ays, *)
  (*                                  in_assignment a ays -> in_assignment a (h::ays). *)
  (*   induction ays. *)
  (*   intros. *)
  (*   apply in_empty in H. *)
  (*   inversion H. *)
  (*   intros. *)
    
    

  (* Fixpoint find_assignment (a : atomic) (ays : assignment) : in_assignment a ays -> bool := *)
  (*   match ays with *)
  (*     | nil => fun pf => match (in_empty a) pf with end *)
  (*     | (h, tv)::t => if beq_atomic a h *)
  (*                     then fun _ => tv *)
  (*                     else (fun _ => find_assignment a t) (find_assignment a ays) *)
  (*   end. *)
                              

  Fixpoint find_assignment (a : atomic) (ays : assignment) : option bool :=
    match ays with 
      | nil => None
      | (h,tv)::t => if beq_atomic h a
                     then Some tv
                     else find_assignment a t
    end.


  (* Fixpoint find_assignment (a : atomic) (ays : { x : assignment | in_assignment a x }) : bool := *)
  (*   (* (sig (fun x => in_assignment a x)) *) *)
  (*   match ays with *)
  (*     | exist nil pf => match (in_empty a) pf with end *)
  (*     | exist ((h, tv)::t) pf  => if beq_atomic a h *)
  (*                                 then tv *)
  (*                                 else find_assignment a (exist (in_assignment a) t pf) *)
  (*   end. *)



  Fixpoint get_all_atoms_assignment (a : assignment) : set atomic :=
    (* assignment is not a set; new assignments shadow others. we only return teh newest *)
    match a with
      | nil => @empty_set atomic
      | (h, _)::t => match find_assignment h t with
                       | None => set_add atomic_eq h (get_all_atoms_assignment t)
                       | _ =>  get_all_atoms_assignment t
                     end
    end.
  
  Definition suitable (f : formula) (a : assignment) := 
    set_diff atomic_eq (get_all_atoms_formula f) (get_all_atoms_assignment a) = @empty_set atomic.

  (* this thing is totally wrong; will think about it more later *)
  (* Definition none_found : forall a ays, find_assignment (Atom a) ays = None -> False. *)
  (*   (* we need something like this to be able to run eval_formula using dependent types*) *)
  (* Admitted. *)

  (* in progress *)
  Fixpoint eval_formula (phi : formula) (a : assignment) : suitable phi a -> bool :=
    match phi return suitable phi a -> bool with
      | Atom foo => match find_assignment foo a with
                      | None => fun pf => match (none_found foo a) pf with end
                      | Some b => fun _ => b
                    end
      | Negation foo => eval_formula foo a
      | Disjunction foo bar => orb (eval_formula foo a) (eval_formula bar a)
    end.

  Definition truth_table_entry := (truth_value * assignment)%type.

  Definition generate_truth_table (f : formula) : list truth_table_entry :=
  let atoms := (get_all_atoms_formula f)
  in let assignments := (generate_all_assignments atoms)
     in map (fun assignment =>  ((eval_formula f assignment), assignment)) assignments.
  
  Definition formula_eq : forall F G a, 
                            { eval_formula F a = eval_formula G a } + { eval_formula F a <> eval_formula G a}.
    decide equality.
    apply eq_dec with (beq:=fun a b => (orb (andb a b) (andb (negb a) (negb b)))).
    intros. destruct x. simpl. reflexivity.
    simpl. reflexivity.
    destruct x; destruct y; simpl; try (intros; reflexivity); try (intros; inversion H).
  Defined.

  Lemma assignment_atomic_eq : forall a1 a2 ays,
                                 find_assignment a1 ays = find_assignment a2 ays -> a1 = a2.
    intros.
    induction ays; destruct a1; destruct a2.
    simpl in H.



  Definition eval_formula_eq : forall F G a,
                                 eval_formula F a = eval_formula G a -> F = G.
    induction F; destruct G; intros.
    simpl in H.
    unfold find_assignment in H.
    



  Theorem disjunction_commute : forall F G,
                                  Disjunction F G = Disjunction G F.
  Proof. 
    induction F; destruct G.
    apply formula_eq.
    
  (*Definition suitable (f : formula) (a : assignment) := eval_formula f a <> None. *)

  Lemma get_all_atoms_negation_invariant : forall F,
                                             get_all_atoms_formula F = get_all_atoms_formula (Negation F).
    induction F; simpl; reflexivity.
  Qed.    

  Lemma suitable_negation_invariant : forall F a,
                                        suitable F a <-> suitable (Negation F) a.
    intros. split; unfold suitable; intros. 
    rewrite <- get_all_atoms_negation_invariant; apply H.
    rewrite <- get_all_atoms_negation_invariant in H; apply H.
  Qed.

  Lemma suitable_disjunction_constituants : forall F G a,
                                              suitable (Disjunction F G) a -> 

  Lemma suitable_disjunction_constituants : forall F G a,
                                              ~ suitable F a -> ~ suitable (Disjunction F G) a.
    induction F as [atm |F' IHF'| F1 IHF1 F2 IHF2].
    unfold not; unfold suitable; simpl.
    intros.
    apply H.
    destruct (set_mem atomic_eq atm (get_all_atoms_assignment a)).
    compute. reflexivity.
    compute. 


  Lemma empty_assignment_not_suitable : forall F,
                                          eval_formula F nil = None -> ~ suitable F nil.
  Proof.
    induction F as [|F' IHF| F1 IHF1 F2 IHF2]; simpl; intros; try (unfold not); try (unfold suitable); simpl.
    (* atomic *)
    compute; intros; inversion H0.
    (* negation *)
    destruct (eval_formula F' nil) as [somebool|].
    inversion H.
    apply IHF in H. unfold not in H. unfold suitable in H. simpl in H. apply H.
    (* disjunction *)
    destruct (eval_formula F1 nil) as [abool|]; destruct (eval_formula F2 nil) as [bbool|].
    inversion H.
    apply IHF2 in H.

  Definition models (f : formula) (a : assignment) := eval_formula f a = Some true.
  
  Definition satisfiable (f : formula) := exists a,
                                            suitable f a -> eval_formula f a = Some true.

  Definition unsatisfiable (f : formula) := forall a,
                                              suitable f a -> eval_formula f a = Some false.

  Definition valid (f : formula) := forall a,
                                      suitable f a -> eval_formula f a = Some true.

  Definition form_equiv (F G : formula) a b :=
                          eval_formula F a = b <-> eval_formula G a = b.
                          

      

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
