(* Lambda Calculus with De Bruijn indices *)

Require Import Coq.Arith.EqNat.

(* (Non-closed) lambda terms *)
Inductive term :=
| Var: nat -> term
| Abs: term -> term
| App: term -> term -> term
.

(* Definition eqDec_term (p q: term) : {p = q} + {p <> q}.
  decide equality. (* For term *)
  decide equality. (* For nat, on which term depends *)
Defined. *)

Scheme Equality for term.


(* TODO check indexing by nats to count nr of free vars *)
(* https://staff.fnwi.uva.nl/t.w.j.kappe/teaching/coq/materials/lecture-7c.v *)

Notation "# n" := (Var n) (at level 10).
Notation "\ p" := (Abs p) (at level 20).
(* u $ v $ w = (u $ v) $ w *)
(* Left associativity will be confusing for Haskell users but I can't
think of a better symbol for application *)
Notation "$ p q" := (App p q) (at level 0, p at level 0, q at level 0, left associativity).

Module test_term.
  (* Unbound variable #0 *)
  Definition x: term := #0. 
  Print x.

  (* Identity function λx. x *)
  Definition id: term := \#0.
  Unset Printing Notations.
  (* ASK this is still printing with Notations somewhy *)
  Print id.
  Set Printing Notations.
End test_term.

(* Some utils for later tests *)
Definition lc_true: term := \\#1.
Definition lc_false: term := \\#0.
Definition if_then_else: term := \\\ $ ($ #2 #1) #0.

Fixpoint closed_aux (p: term) (level: nat): Prop :=
  match p with
  | #n => n < level
  | \q => closed_aux q (S level)
  | $ q r => (closed_aux q level) /\ (closed_aux r level)
  end
.

Definition closed (p: term): Prop :=
  closed_aux p 0
.

Record closed_term := {
  t: term;
  c: closed t;
}.

Module test_applicator_closed.
  Definition applicator := \\$#0#1.
  Program Definition test_closed_term := {|
    t := applicator
  |}.
  Next Obligation. (* closed applicator *)
    compute.
    (* ASK how to simplify/unroll this? = unfold closed_aux*)
    split.
    - simpl.
      apply le_S.
      apply le_n.
    - simpl.
      apply le_n.
  Qed.
End test_applicator_closed.
