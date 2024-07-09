Require Import List.
Import ListNotations.
From Repl Require Import
  (* Moqtop
  Result *) 
  Syntax.

Inductive result : Type :=
| success (gs : list goal)
| failure.

Parameter run_atomic : atomic -> goal -> result.

Inductive execute_atomic : atomic -> goal -> result -> Prop :=
| e_atomic : forall a g,
  execute_atomic a g (run_atomic a g).

Inductive execute_tactic : tactic -> goal -> result -> Prop :=
| e_single : forall a g out,
  execute_atomic a g out ->
  execute_tactic (single a) g out
| e_zero : forall g,
  execute_tactic zero g failure
| e_plus_okay1 : forall t1 t2 g outl1,
  execute_tactic t1 g (success outl1) ->
  execute_tactic (plus t1 t2) g (success outl1)
| e_plus_okay2 : forall t1 t2 g outl2,
  execute_tactic t1 g (failure) ->
  execute_tactic t2 g outl2 ->
  (* ------------------------------- *)
  execute_tactic (plus t1 t2) g (outl2).


Goal forall t1 t2 g outl2,
  execute_tactic t1 g (failure) ->
  execute_tactic t2 g (success outl2) ->
  execute_tactic (plus t1 t2) g (success outl2).
Proof.
intros t1 t2 g out H1 H2.
apply e_plus_okay2.
- apply H1. 
- apply H2.
Qed.   



(* | e_fail : forall g, 
  execute_tactic "fail" g(failure [g])
| e_first_nil : forall g, 
   *)

   