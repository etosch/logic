(** (cf. Exercise 13, p. 14) Prove Craig’s Interpolation Theorem for Propositional Logic: Suppose
that |= (F → G) for propositional formulas F and G. Prove that there is a formula
I – called the interpolant – such that |= (F → I), |= (I → G), and atom(I) =
atom(F) ∩ atom(G). [Hint: prove this by induction on n = |atom(F) − atom(G)|, i.e, the
number of atomic formulas that occur in F but not in G. Note that your base case should be
n = 0. In Exercise 13, Sch¨oning just states this theorem for n ≥ 1 because he doesn’t have
⊤ and ⊥ as propositional formulas, but we do.] *)
Require Import PropLogic.
Require Import List.

(* assume |= (F -> G) *)
Theorem Craigs_Interpolation_Theorem : forall F G,
                                           valid (Implies F G) -> 
                                           exists (I : formula),
                                             (valid (Implies F I) /\ 
                                              valid (Implies I G) /\ 
                                              (get_unique_atoms I = atom_intersection (get_unique_atoms F) (get_unique_atoms G))).
Proof.
  intros.  
  
  
