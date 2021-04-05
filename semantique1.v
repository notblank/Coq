From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition ident := string.

Inductive aexp : Type :=
  | CONST (n : Z)
  | VAR (x : ident)
  | PLUS (a1 : aexp) (a2 : aexp)
  | MINUS (a1 : aexp) (a2 : aexp).

Definition store : Type := ident -> Z. 

Fixpoint aeval (a : aexp) (s : store) : Z :=
  match a with 
  | CONST n => n
  | VAR x => s x
  | PLUS a1 a2 => aeval a1 s + aeval a2 s
  | MINUS a1 a2 => aeval a1 s - aeval a2 s
  end.

(* evaluer ce qu'on peut - Reduire *)
Eval cbn in (aeval (PLUS (VAR "x") (MINUS (CONST 10) (CONST 1)))).

(* on a toujours x + 1 > x pour tout etat memoire *)
Lemma aeval_xplus1:
  forall s x, aeval (PLUS (VAR x) (CONST 1)) s > aeval (VAR x) s.
Proof.
  intros.  (* hypotheses *)
  cbn.     (* callbinding *)
  lia.     (* Plus un affaire de semanthique, linear integer arithmetic *)
Qed.


