Require Import String.
Require Import List.
Import ListNotations.

Definition ident := string.

Parameter atomic : Set.
Parameter goal : Set.



Inductive exception : Type :=
(* | exn : string -> exception. *)
| exn_f1
| exn_f2
| exn_var (x: string). 

(* Parameter unit : Set.  *)

Inductive tactic : Type := 
| single (a : atomic)
| zero (e : exception) (* Ltac2 Documentation: val zero : exn -> 'a*)
| plus (t1 t2 : tactic) (*Ltac2 documentation: val plus
 : (unit -> 'a) -> (exn -> 'a) -> 'a*)
| throw (e : exception) (*ltac2 documentation: val throw : exn -> 'a*)
| tMatch (e :exception) (handle1 handle2 : tactic). 
