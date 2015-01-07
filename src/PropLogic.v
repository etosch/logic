Require Import EqNat.
Require Import List.
Require Import ListSet.
Require Import Coq.Bool.BoolEq.
Require Import Arith.Peano_dec.

Section background.

  (********** Atoms **********)

  Inductive atomic :=
  | A : nat -> atomic. 
  
  Definition beq_atomic (a : atomic) (b : atomic) :=
    match a, b with
      | A n, A m => beq_nat n m
    end.

  (* This is needed to use ListSet *)
  Definition atomic_eq : 
    forall a b : atomic, {a = b} + {a <> b}.
    decide equality.
    apply eq_nat_dec.
  Defined.

  (********** Formulae **********)

  Inductive formula :=
  | Atom : atomic -> formula 
  | Negation : formula -> formula
  | Disjunction : formula -> formula -> formula.
  
  Notation "A_[ i ]" :=
    (Atom (A i))
      (at level 200, right associativity).
  Check (Atom (A 1)).

  Notation "'Conjunction' A B " := 
    (Negation (Disjunction (Negation A) (Negation B)))
      (at level 80, left associativity).
  Check (Negation (Disjunction (Negation (A_[1])) (Negation (A_[2])))).

  Notation "'Implies' A B" :=
    (Disjunction (Negation A) B)
      (at level 60, left associativity).
  Check (Disjunction (Negation (A_[1])) (A_[2])).

  Fixpoint get_all_atoms_formula (f : formula) : set atomic :=
    match f with
      | Atom foo => set_add atomic_eq foo (@empty_set atomic)
      | Negation foo => get_all_atoms_formula foo
      | Disjunction foo bar => set_union atomic_eq (get_all_atoms_formula foo) (get_all_atoms_formula bar)
    end.

  Fixpoint in_formula (a : atomic) (f : formula) : Prop :=
    match f with
      | Atom atm => match atomic_eq atm a with
                        | left _ => True
                        | right _ => False
                    end
      | Negation f' => in_formula a f'
      | Disjunction f' f'' => in_formula a f' \/ in_formula a f''
    end.

  Theorem in_formula_in_all_atoms:
    forall f a,
      In a (get_all_atoms_formula f) <-> in_formula a f.
  Proof. 
    split; induction f; simpl; intros; try (inversion H); 
      try (destruct (atomic_eq a0 a));
      try (trivial).
    + unfold not in n.
      apply n.
      apply H0.
    + apply IHf in H.
      apply H.
    + left. 
      apply IHf1.
      (* need to relate set union and append in H *)


      
  Theorem in_formula_disjunction_commute: 
    forall a f g, 
      in_formula a (Disjunction f g) <-> in_formula a (Disjunction g f).
  Proof. 
    split; unfold in_formula; intros; induction f; destruct g; fold in_formula; 
     try (apply or_comm; apply H);
     try (destruct (atomic_eq a0 a)).
  Qed.

  Theorem in_formula_disjunction_add:
    forall a f g,
      in_formula a f -> in_formula a (Disjunction f g).
  Proof.
    intros.
    simpl.
    left. 
    apply H.
  Qed.

  (********** Assignments & Suitability  **********)

  Definition assignment : Set := list (atomic * bool).
  
  Fixpoint generate_all_assignments (a : list atomic) : (list assignment) :=
    let f := fun atm v assign => (atm, v)::assign in
    match a with
         | nil => nil::nil
         | h::t => let f' := f h
                   in (map (f' true) (generate_all_assignments t))
                        ++ (map (f' false) (generate_all_assignments t))
       end.

  Fixpoint in_assignment (a : atomic) (ays : assignment) : Prop :=
    match ays with
      | nil => False
      | (h,_)::t =>  match atomic_eq a h with
                       | left _ => True
                       | right _ => in_assignment a t
                     end
    end.

  Definition suitable (f : formula) (ays : assignment) : Prop := 
    forall a, 
      in_formula a f -> in_assignment a ays.

  Theorem generated_assignments_are_suitable:
    forall f ays,
      In ays (generate_all_assignments (get_all_atoms_formula f)) -> suitable f ays.
  Proof.
    unfold suitable; intros; induction ays; destruct f; simpl in H; try (inversion H); simpl. 
    + inversion H1.
    + inversion H1; inversion H2.
    + unfold In in H.
      unfold generate_all_assignments in H.
      unfold get_all_atoms_formula in H.

  Theorem suitable_negation_invariant: 
    forall f ays, 
      suitable f ays <-> suitable (Negation f) ays.
  Proof. 
    split; intros; unfold suitable; unfold suitable in H; intros; apply H; simpl in H0.
    + apply H0.
    + simpl; apply H0.
  Qed.

  Theorem suitable_disjunction_invariant:
    forall f g ays,
    suitable (Disjunction f g) ays -> suitable f ays /\ suitable g ays.
  Proof. 
    unfold suitable; intros.
    split.
    + intros.
      apply in_formula_disjunction_add with (g:=g) in H0.
      generalize H0.
      apply H.
    + intros.
      apply in_formula_disjunction_add with (g:=f) in H0.
      apply in_formula_disjunction_commute in H0.
      generalize H0.
      apply H.
  Qed.
    
  Lemma in_empty : forall a, in_assignment a nil -> False.
    intros; compute in H; apply H.
  Qed.

  (* Thanks to @arjunguha *)
  Lemma in_partition : forall (a k : atomic) (tv : bool) (ays : assignment),
                         in_assignment a ((k,tv)::ays) ->
                         a <> k ->
                         in_assignment a ays.
  Proof with auto using list.
    intros; induction ays; simpl in H; destruct (atomic_eq a k); try contradiction.
    simpl. apply H.
  Qed.
  
  Fixpoint find_assignment a (ays : assignment) { struct ays }: in_assignment a ays -> bool.
  refine (match ays with
            | nil => _
            | (h,tv)::t => 
              match atomic_eq a h with
                | left eq_proof => fun _ => tv
                | right neq_proof => fun pf => find_assignment a t (@in_partition a h tv t pf neq_proof)
              end
          end).
  Proof.
    + intros.
      apply in_empty in H.
      inversion H.
  Qed.

  (********** Truth Tables **********)
  
  Definition truth_table_entry := (bool * assignment)%type.
  
  (* Truth tables are tied to evaluation *)
  Fixpoint eval_formula (phi : formula) (ays : assignment) : suitable phi ays -> bool.
  refine (match phi with
            | Atom atm => fun _ => find_assignment atm ays _
            | Negation phi' => fun _ => negb (eval_formula phi' ays _)
            | Disjunction phi' phi'' => fun _ => orb (eval_formula phi' ays _)
                                                      (eval_formula phi'' ays _)
          end).
  Proof. 
    intros; unfold suitable in _H; apply _H; simpl.
    destruct (atomic_eq atm atm); trivial.
    + unfold not in n; apply n; trivial.
    + apply suitable_negation_invariant; apply _H.
    + apply suitable_disjunction_invariant in _H; inversion _H.
      apply H.
    + apply suitable_disjunction_invariant in _H; inversion _H.
      apply H0.
  Qed.

  Definition generate_truth_table (f : formula) : list truth_table_entry :=
    let atoms := (get_all_atoms_formula f) in
    let assignments := (generate_all_assignments atoms) in
    map (fun assignment =>  
           let pf := suitable f assignment in
           ((eval_formula f assignment pf), assignment))
        assignments.


  Fixpoint atoms_equal (f_atoms g_atoms : set atomic) : bool :=
    match f_atoms, g_atoms with
      | nil, nil  => true
      | nil, _ | _, nil => false
      | h::t, _ => if set_mem atomic_eq h g_atoms
                   then atoms_equal t (set_remove atomic_eq h g_atoms)
                   else false
    end.

  
 (********** Formula Equality **********)
  
  Fixpoint beq_formula (f g : formula) : bool :=
    let f_atoms := get_all_atoms_formula f in
    let g_atoms := get_all_atoms_formula g in
    if atoms_equal f_atoms g_atoms 
    then     
      let f_assignments := generate_all_assignments f_atoms in
      let g_assignments := generate_all_assignments g_atoms in
      
    else false.

    

  Definition formula_eq : forall f g : formula, 
                            {f = g} + {f <> g}.
    decide equality.
    apply atomic_eq.
  Defined.

  (* Later when we have truth tables, we can use those to define another, better  equality function. *)


  Theorem disjunction_commute : forall f g, 
                                  Disjunction f g = Disjunction g f.


  Inductive eq_formula : formula -> formula -> Prop :=
  | atom_eq : forall a1 a2, a1 = a2 -> eq_formula (Atom a1) (Atom a2)
  | neg_eq : forall f g, eq_formula f g -> eq_formula (Negation f) (Negation g)
  | disj_eq : forall f g h, eq_formula f g -> eq_formula (Disjunction f h) (Disjunction g h).

  Proof. 
    induction f; simpl.
    destruct g.
    


  Fixpoint bsub_formula (F : formula) (G : formula) : bool :=
    if beq_formula F G
    then true
    else match G with
           | Atom _ => false
           | Negation foo => bsub_formula F foo
           | Disjunction foo bar => orb (bsub_formula F foo) (bsub_formula F bar)
         end.

  Inductive sub_formula: formula -> formula -> Prop :=
  | base_subf : forall f g, eq_formula f g -> sub_formula f g
  | neg_subf : forall f g, sub_formula f g -> sub_formula f (Negation g)
  | disj_subf : forall f g h, sub_formula f g -> sub_formula f (Disjunction g h).

  


  Fixpoint count_atoms (a : atomic) (lst : list atomic) :=
    match lst with
      | nil => 0
      | h::tl => if (beq_atomic h a)
                 then 1 + (count_atoms a tl)
                 else count_atoms a tl
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
  

  (* this thing is totally wrong; will think about it more later *)
  (* Definition none_found : forall a ays, find_assignment (Atom a) ays = None -> False. *)
  (*   (* we need something like this to be able to run eval_formula using dependent types*) *)
  (* Admitted. *)

  (* in progress *)
  
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
