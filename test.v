From  Coq Require Import Arith Bool.

Check 3.
Check 4 - 4.

(* Eval programs *)
Eval compute in 4 + 1.

(*  Fail succeeds when given an error *)
Fail Check print.

Print bool.

Inductive week_day :=
  | Mon : week_day
  | Tue : week_day.

Check Mon.

Definition add_one (x : nat) : nat := x + 1.

Check add_one.

Eval compute in  add_one 4.

(* pattern matching *)
Definition is_Mon (w : week_day) : bool :=
  match w with 
  | Mon => true
  | _ => false
  end.

Check is_Mon.

Eval compute in is_Mon Mon.

(* Search *)
Search (bool -> bool).

Eval compute in negb true.

(* EXO: define tail *)
Inductive week_day_list :=
  | Nil : week_day_list
  | Cons : week_day -> week_day_list -> week_day_list.

Check week_day_list.

Check (Cons Mon (Cons Tue Nil)).

Definition tail (l : week_day_list) :week_day_list :=
  match l with 
  | Nil => Nil
  | Cons _ w => w
  end.

Eval compute in tail (Cons Tue (Cons Mon Nil)).

(* Notation *)
(* .. ellipsis *)

Notation "[ ]" := Nil.

Notation "[ w ]" := (Cons w Nil).

Notation "[ w1 ; w2 ; .. ; wn ]" := (Cons w1 (Cons w2 .. (Cons wn Nil) .. )).
 
Definition three_mons := [Mon; Mon; Mon].

Check three_mons.

Eval compute in tail three_mons.

(* recursion is called fixpoint *)

Fixpoint length (l : week_day_list) : nat :=
  match l with 
  | [] => 0
  | Cons h t => 1 + length(t)
  end.

Eval compute in length [Mon; Tue; Mon].

(* proofs *)

Lemma test1 : forall x y : week_day, x = y -> x = y.
Proof.
  intros.
  apply H.
Qed.
(* can use Abort. while proving *)

Check test1.

Lemma test2 : Mon = Mon.
Proof.
  reflexivity.
Qed.











