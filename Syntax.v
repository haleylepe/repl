Require Import String.
Require Import List.
Import ListNotations.

Definition ident := string.

Parameter atomic : Set.
Parameter goal : Set.



Inductive exception : Type :=
(* | exn : string -> exception. *)
| exn_f1 (*fail in the first tactic*)
| exn_f2 (* fail in the second tactic*)
| exn_var (x: string). (*specific type of exn? *)

(* Parameter unit : Set.  *)

Inductive tactic : Type := 
| single (a : atomic)
| zero (e : exception) (* Ltac2 Documentation: val zero : exn -> 'a*)
| plus (t1 : tactic) ( x: string) (t2 :tactic) (*Ltac2 documentation: val plus
 : (unit -> 'a) -> (exn -> 'a) -> 'a*)
| throw (e : exception) (*ltac2 documentation: val throw : exn -> 'a*)
| tMatch (e :exception) (handle1 handle2 : tactic). (*what is with this implentation?*)

Definition subst_exn (e1 : exception) (x : string) (e2 : exception) : exception :=
    match e1 with 
    | exn_f1 => exn_f1
    | exn_f2 => exn_f2
    | exn_var x' => if String.eqb x x'
                        then e2
                    else e1
    end. 

Fixpoint subst_tactic (t : tactic) (x : string) (e : exception)  : tactic :=
    match t with 
    | single _ => t
    | zero e' => zero (subst_exn e' x e)
    | throw e' => throw (subst_exn e' x e)
    | tMatch e' t1 t2 => tMatch (subst_exn e' x e) (subst_tactic t1 x e) (subst_tactic t2 x e) 
    | plus t1 x' t2 => if String.eqb x x'
                            then plus (subst_tactic t1 x e) x' t2
                        else plus (subst_tactic t1 x e) x' (subst_tactic t2 x e)
    end. 

    
