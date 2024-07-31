Require Import List.
Require Import String. 
Import ListNotations.
From Repl Require Import
  (* Moqtop
  Result *) 
  Syntax.


Inductive result : Type :=
| success (gs : list goal)
| recoverableErr (e : exception) 
| irrecoverable (e: exception). 

Parameter run_atomic : atomic -> goal -> result.

Inductive execute_atomic : atomic -> goal -> result -> Prop :=
| e_atomic : forall a g,
  execute_atomic a g (run_atomic a g).

Inductive execute_tactic : tactic -> goal -> result -> Prop :=
| e_single : forall a g out,
  execute_atomic a g out ->
  execute_tactic (single a) g out
| e_zero : forall g e ,
  execute_tactic (zero e) g (recoverableErr e ) 
| e_plus_okay1 : forall t1 x t2 g outl1,
  execute_tactic t1 g (success outl1) ->
  execute_tactic (plus t1 x t2) g (success outl1)
| e_plus_okay2 : forall t1 x t2 g outl2 e,
  execute_tactic t1 g (recoverableErr e) ->
  execute_tactic (subst_tactic t2 x e) g outl2 ->
  execute_tactic (plus t1 x t2) g (outl2)
| e_throw : forall e g , 
execute_tactic (throw e) g (irrecoverable e ) 
| e_plus_notOkay1 : forall t1 t2 g e x ,
execute_tactic t1 g (irrecoverable e) ->
execute_tactic (plus t1 x t2) g (irrecoverable e)
| tMatch_t1okay : forall t1 t2 g out , 
  execute_tactic t1 g out -> 
  execute_tactic (tMatch exn_f1 t1 t2) g out
| tMatch_t2okay : forall t1 t2 g out,
  execute_tactic t2 g out -> 
  execute_tactic (tMatch exn_f2 t1 t2) g out.

(* Test if proof will only output first tactic that works *)
Goal forall t1 t2 g x outl1 outl2,
execute_tactic t1 g (success outl1) ->
execute_tactic t2 g (success outl2) ->
execute_tactic (plus t1 x t2) g (success outl1).
Proof.
intros. 
apply e_plus_okay1. apply H.
Qed.

(* "NEW" ensure that the success t2 will not be
 execute if t1 an irrecoverable error*)
Goal forall t1 t2 g outl2 e x ,
execute_tactic t1 g(irrecoverable e ) ->
execute_tactic t2 g (success outl2) ->
execute_tactic (plus t1 x t2) g (irrecoverable e). 
Proof. 
intros.
apply e_plus_notOkay1.
- apply H.
Qed.    



Goal forall g t1 t2 t3 out,
 execute_tactic t1 g (recoverableErr exn_f1)  -> 
 execute_tactic (subst_tactic t2 "x" exn_f1) g out -> 
 execute_tactic (plus t1 "x" (tMatch (exn_var "x") t2 t3)) g out.
Proof. 
 intros.
 eapply e_plus_okay2.
 - eauto.
 - simpl.
   apply tMatch_t1okay. eauto.
Qed.

Goal forall g t1 t2 t3 out,
 execute_tactic t1 g (recoverableErr exn_f2) ->
 execute_tactic (subst_tactic t3 "x" exn_f2 ) g out ->
 execute_tactic (plus t1 "x" (tMatch (exn_var "x") t2 t3)) g out.
Proof. 
intros.
eapply e_plus_okay2.
- apply H. 
- simpl. eapply tMatch_t2okay. apply H0.
Qed. 


(* examples *)

(* Example simple_ex : (True \/ False) /\ (False \/ True).
Proof. *)









   