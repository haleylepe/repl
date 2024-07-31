Example simple_ex : (True \/ False) /\ (False \/ True).
Proof.
  split . 
  - (left + right). apply I. 
  - right; apply I . 
  Qed.

  (* from ltac2fun2 *)

Example simple_ex1 : (True \/ False) /\ (False \/ True).
Proof. 
    split; (left + right); apply I. 
    Qed. 



