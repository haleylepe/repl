
Require Import List.
Import ListNotations.

Parameter atomic : Set.
Parameter goal : Set.

Inductive result (T : Type) :=
| ok (t : T)
| failure.

Arguments ok {T}.
Arguments failure {T}.

Parameter step_atomic : goal -> atomic -> result goal -> Prop.

Inductive tactic :=
| skip
| base (a : atomic)
| seq (t1 t2 : tactic)
| plus (t1 t2 : tactic).

Inductive k :=
| _seq (t2 : tactic).

Definition ttup : Type := goal * tactic * list k * list (goal * tactic * list k).

Inductive step_tactic : ttup -> result ttup -> Prop :=
| s_base_ok : forall g g' a ks bs,
    step_atomic g a (ok g') ->
    step_tactic (g, base a, ks, bs) (ok (g', skip, ks, bs))
| s_base_err_back : forall g g' a ks ks' t' bs,
    step_atomic g a failure ->
    step_tactic (g, base a, ks, (g', t', ks') :: bs) (ok (g', t', ks', bs))
| s_base_err_stop : forall g a ks,
    step_atomic g a failure ->
    step_tactic (g, base a, ks, []) failure
| s_skip : forall g t ks bs,
    step_tactic (g, skip, _seq t :: ks, bs) (ok (g, t, ks, bs))
| s_seq : forall g t1 t2 ks bs,
    step_tactic (g, seq t1 t2, ks, bs) (ok (g, t1, _seq t2 :: ks, bs))
| s_plus : forall g t1 t2 ks bs,
    step_tactic (g, plus t1 t2, ks, bs) (ok (g, t1, ks, (g, t2, ks) :: bs)).

Inductive multi_step_tactic : ttup -> result ttup -> Prop :=
| multi_refl : forall ts,
  multi_step_tactic ts (ok ts)
| multi_step : forall ts ts' ts'',
  step_tactic ts (ok ts') ->
  multi_step_tactic ts' ts'' ->
  multi_step_tactic ts ts''
| multi_step_fail : forall ts,
  step_tactic ts failure ->
  multi_step_tactic ts failure.

Definition stepsto (g : goal) (t : tactic) (g' : goal) : Prop :=
  exists bs, multi_step_tactic (g, t, [], []) (ok (g', skip, [], bs)).

(* PROPERTIES *)

Theorem step_multi_step : forall ts r,
  step_tactic ts r -> multi_step_tactic ts r.
Proof.
intros. 
destruct H.
- eapply multi_step.
  + apply s_base_ok. apply H.
  + apply multi_refl.
- eapply multi_step.
  + apply s_base_err_back. apply H.
  + apply multi_refl.
- eapply multi_step_fail.
  apply s_base_err_stop. apply H.
- eapply multi_step.
  + apply s_skip.
  + apply multi_refl.
- eapply multi_step.
  + apply s_seq.
  + apply multi_refl.
- eapply multi_step.
  + apply s_plus.
  + apply multi_refl.
Qed. 

Theorem multi_step_transitive : forall ts ts' ts'',
  multi_step_tactic ts (ok ts') ->
  multi_step_tactic ts' (ok ts'') ->
  multi_step_tactic ts (ok ts'').
Proof.
intros ts ts' ts'' H1 H2.
remember (ok ts'). induction H1.
- inversion Heqr. subst. apply H2.
- subst. eapply multi_step.
  + apply H.
  + apply IHmulti_step_tactic. reflexivity.
- eapply multi_step.
  + inversion Heqr. 
  + apply H2.
  Qed.   



Qed.

(* TESTING *)

Parameter tru : goal.
Parameter fls : goal.
Parameter disj : goal -> goal -> goal.

Parameter lft : atomic.
Parameter rght : atomic.
Axiom s_lft : forall g1 g2, step_atomic (disj g1 g2) lft (ok g1).
Axiom s_rght : forall g1 g2, step_atomic (disj g1 g2) rght (ok g2).

Parameter none : goal.
Parameter istru : atomic.
Axiom s_istru_tru : step_atomic tru istru (ok none).
Axiom s_istru_fls : step_atomic fls istru failure.

Hint Constructors step_tactic : core.
Hint Resolve s_lft s_rght s_istru_tru s_istru_fls : core.

Ltac solve_base :=
  match goal with
  | [ |- step_tactic (_, base _, _, _) _] => solve [apply s_base_ok; auto]
  end.

Ltac solve_stepsto :=
  unfold stepsto; exists [];
  repeat (eapply multi_step; [first [solve [eauto 10] | solve_base] |]);
  apply multi_refl.

(* Goal True.
   Proof. apply I.
 *)
Goal stepsto tru (base istru) none.
Proof.
  solve_stepsto.
Qed.

(* Goal False \/ True.
   Proof. right; apply I.
 *)
Goal stepsto (disj fls tru) (seq (base rght) (base istru)) none.
Proof.
  solve_stepsto.
Qed.

(* Goal False \/ True.
   Proof. (left + right); apply I.
 *)
Goal stepsto (disj fls tru) (seq
                               (plus (base lft) (base rght))
                               (base istru))
             none.
Proof.
  solve_stepsto.
Qed.

(* Goal True \/ False.
   Proof. (right + left); apply I.
 *)
Goal stepsto (disj tru fls) (seq
                               (plus (base rght) (base lft))
                               (base istru))
             none.
Proof.
  solve_stepsto.
Qed.

(* Goal (False \/ False) \/ (False \/ True).
   Proof. (left + right); (left + right); apply I.
 *)
Goal stepsto (disj (disj fls fls) (disj fls tru))
             (seq
                 (plus (base lft) (base rght))
                 (seq
                    (plus (base lft) (base rght))
                    (base istru)))
             none.
Proof.
  solve_stepsto.
Qed.

