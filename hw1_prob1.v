(** Show from our definition of semantics and our abbreviation for $$\wedge$$, that for any truth assignment $$\mathcal{A}$$ that is suitable for $$F \wedge G, \mathcal{A}(F \wedge G) = min(\mathca{F},\mathcal{A}(G))$$. *)
Add LoadPath ".".
Require Import PropLogic.

Example hw1_prob1 : forall (a : assignment) (F G : formula),
                      let f := (Negation (Disjunction (Negation F) (Negation G)))
                      in suitable f a -> eval_formula f a = min (eval_formula F a) (eval_formula G a).
Proof. 
  intros.
  destruct F; destruct G;
  (* both atoms *)
  unfold f; unfold eval_formula.
  destruct (find_assignment a0 a) eqn:foo.
  destruct (find_assignment a1 a) eqn:bar.
  destruct b; destruct b0; simpl; reflexivity.
  destruct b; simpl; reflexivity.
  destruct (find_assignment a1 a) eqn:baz;
    try (destruct b); simpl; reflexivity.
  (* Atom F, Negation G *)
  fold eval_formula.
  destruct (find_assignment a0 a) eqn:foo;
  destruct (eval_formula G a) eqn:bar;
    try (destruct b); 
    try (destruct b0); 
  simpl; reflexivity.
  (* Atom F, Disjunction G 1 G_2 *)
  fold eval_formula.
  destruct (find_assignment a0 a) eqn:foo;
    destruct (eval_formula G1 a) eqn:bar1;
    destruct (eval_formula G2 a) eqn:bar2;
  try (destruct b); try (destruct b0); try (destruct b1); simpl; reflexivity.
  (* Negation F, Atom G *)
  fold eval_formula.
  destruct (eval_formula F a) eqn: foo;
    destruct (find_assignment a0 a);
    try (destruct b);
    try (destruct b0);
    simpl; reflexivity.
  (* Negation F, Negation G *)
  fold eval_formula.
  destruct (eval_formula F a) eqn:foo;
    destruct (eval_formula G a) eqn:bar;
    try (destruct b);
    try (destruct b0);
    simpl; reflexivity.
  (* Negation F, Disjunction G1 G2 *)
  fold eval_formula.
  destruct (eval_formula F a);
    destruct (eval_formula G1 a);
    destruct (eval_formula G2 a);
    try (destruct b); try (destruct b0; destruct b1);
    simpl; reflexivity.
  (* Disjunction F1 F2, Atom *)
  fold eval_formula.
  destruct (eval_formula F1 a);
    destruct (eval_formula F2 a);
    destruct (find_assignment a0 a);
    try (destruct b);
    try (destruct b0);
    try (destruct b1);
    try (destruct b2);
    simpl; reflexivity.
  (* Disjunction F1 F2, Negation (Negation G) *)
  fold eval_formula.
  destruct (eval_formula F1 a);
    destruct (eval_formula F2 a);
    destruct (eval_formula G a);
    try (destruct b);
    try (destruct b0);
    try (destruct b1);
    try (destruct b2);
    simpl; reflexivity.
  (* Disjunction F1 F2, Disjunction G1 G2 *)
  fold eval_formula.
  destruct (eval_formula F1 a);
    destruct (eval_formula F2 a);
    destruct (eval_formula G1 a);
    destruct (eval_formula G2 a);
    try (destruct b);
    try (destruct b0);
    try (destruct b1);
    try (destruct b2);
    simpl; reflexivity.
Qed.  
