Require Import String.
Require Import List.
Import ListNotations.

Definition ident := string.

Parameter atomic : Set.
Parameter goal : Set.

Inductive tactic : Type := 
| single (a : atomic)
(* | semicolon (t1 t2: tactic) *)
(* | try (t1 : tactic) *)
| zero (* todo: how to deal with thunking *)
| plus (t1 t2 : tactic).
(* | first (t1 : tactic) (t2 tactic_list). *)

