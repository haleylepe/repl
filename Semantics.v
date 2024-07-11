Require Import List.
Require Import String. 
Import ListNotations.
From Repl Require Import
  (* Moqtop
  Result *) 
  Syntax.


Inductive result : Type :=
| success (gs : list goal)
(* | failure - took out to have multiple types of errors *) 
(* added two types of failer recoverable vs irrecoverable*)
| recoverableErr (* "TODO" not sure if we need to add exception as a parameter here
- did not add it currently because we do not need to throw an exception*)
| irrecoverable (e: exception). 

(* "Other TODO"  
-look through stlc chapter about substitution, 
- adding throw in result for irrecoverable type of plus
- ignore exn type assume second tactic is always done (tbh 
I do not remember why)
*)
(* also look possibly look at imp *)
(* | unit (u : unit ) *)

(* Definition thunk := unit -> a. *)
(* Definition thunk := unit -> result. *)


Parameter run_atomic : atomic -> goal -> result.

Inductive execute_atomic : atomic -> goal -> result -> Prop :=
| e_atomic : forall a g,
  execute_atomic a g (run_atomic a g).

  (* Definition execute_thunk (t : thunk) : result :=
    t. *)


Inductive execute_tactic : tactic -> goal -> result -> Prop :=
| e_single : forall a g out,
  execute_atomic a g out ->
  execute_tactic (single a) g out
| e_zero : forall g e ,
  execute_tactic (zero e) g (recoverableErr) 
| e_plus_okay1 : forall t1 t2 g outl1,
  execute_tactic t1 g (success outl1) ->
  execute_tactic (plus t1 t2) g (success outl1)
| e_plus_okay2 : forall t1 t2 g outl2,
  execute_tactic t1 g (recoverableErr ) ->
  execute_tactic t2 g outl2 ->
  execute_tactic (plus t1 t2) g (outl2)
| e_throw : forall e g , 
execute_tactic (throw e) g (irrecoverable e ) 
(* "TODO" | create a new definition to take in here.
Would this be  having a irrecoverableErr in the first opening of plus? *)
| e_plus_notOkay1 : forall t1 t2 g e ,
execute_tactic t1 g (irrecoverable e) ->
execute_tactic (plus t1 t2) g (irrecoverable e). 


(* Ensuring backtracking on plus, 
with recoverable error/failure on first tactics *)
Goal forall t1 t2 g outl2,
  execute_tactic t1 g (recoverableErr ) ->
  execute_tactic t2 g (success outl2) ->
  execute_tactic (plus t1 t2) g (success outl2).
Proof.
intros t1 t2 g out H1 H2.
apply e_plus_okay2.
- apply H1. 
- apply H2.
Qed.   

(* Test if proof will only output first tactic that works *)
Goal forall t1 t2 g outl1 outl2,
execute_tactic t1 g (success outl1) ->
execute_tactic t2 g (success outl2) ->
execute_tactic (plus t1 t2) g (success outl1).
Proof.
intros. 
apply e_plus_okay1. apply H.
Qed.

(* "NEW" ensure that the success t2 will not be
 execute if t1 an irrecoverable error*)
Goal forall t1 t2 g outl2 e,
execute_tactic t1 g(irrecoverable e ) ->
execute_tactic t2 g (success outl2) ->
execute_tactic (plus t1 t2) g (irrecoverable e). 
Proof. 
intros.
apply e_plus_notOkay1.
- apply H.
Qed.    

(* "TODO " trying to figure out how I can create a Goal for throw
or if it is even conceptually possible*)
Goal forall e g,
execute_tactic . 
Admitted. 


   