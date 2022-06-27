
Require Import Basics.
Require Import Reduction.

Fixpoint church_nat_aux (n: nat) (f: term): term :=
  match n with
  | 0 => Var 0
  | S n' => App f (church_nat_aux n' f)
  end
.



(* Module test_church_nat.
  Compute church_nat 0.
  Compute church_nat 1.
  Compute church_nat 2.
  (* etc. *)
End test_church_nat. *)

(* Church encoding of a given natural *)
Definition church_nat (n: nat): term :=
  \\(church_nat_aux n (#1))
.

Record term_nat := {
  t: term;
  (* We are strict: a Church numeral has to be in normal form to be considered as one, hence = instead of ==: *)
  n: exists (n: nat), t = church_nat n;
}.

Program Definition church_nat' (n: nat): term_nat := {|
  t := church_nat n;
|}.

Next Obligation.
  now exists n0.
Qed.


(* TODO fix this notation? *)
Definition church_succ: term :=
  \\\ App (#1) (App (App (#2) (#1)) (#0))
.

(* apply CTrans with (x' := p);
[ apply CStep; unfold beta_step; simpl; now left | ]. *)

Lemma church_succ_respects_nat (n: nat): $ church_succ (church_nat n) == church_nat (S n).
Proof.
  induction n.
  - common_reduct.
  - next_reduct (\\ App (#1) (App (App (church_nat (S n0)) (#1)) (#0))).
    unfold church_nat.
    apply CTrans with (x' := (\\ $ (# 1) $ (\ church_nat_aux (S n0) (# 1)) (# 0))).
    + apply CStep.
      unfold beta_step.
      (* simpl. *) (* This kills the Coq *)

    next_reduct (\\ $ (# 1) $ (\ church_nat_aux (S n0) (# 1)) (# 0)).
    Compute beta_reducts (\ (\ $ (# 1) $ $ (\ (\ (#999))) (# 1) (# 0))).
    (* Maybe RHS can be reduced a bit further? *)

    (* LHS is equiv to: *)
    (* next_reduct (\\ $ (# 1) (church_nat_aux (S n0) (# 1))). *)
    (* which cannot be beta-reduced any further. *)

    unfold church_nat.
    destruct (S (S n0)).

    apply CTrans with (x' := \\ $ (# 1) (church_nat_aux (S n0) (# 1)));
    [ apply CStep|].
    next_reduct (\\ $ (# 1) (church_nat_aux (S n0) (# 1))).
    next_reduct (\\ church_nat_aux (S (S n0)) (# 1)).
    next_reduct (\\ (App (# 1) (church_nat_aux (S n0) (# 1))) (# 1)).


  next_reduct $ (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (\ (\ church_nat_aux n (# 1))).



  induction n.
  - common_reduct.
  - unfold church_nat.
    destruct (S n0).
    + common_reduct.
    + simpl.
      

Require Import Coq.Classes.Morphisms. (* to use f_equiv if necessary *)


(* We need to prove that $ church_succ is an injective morphism *)
(* Lemma succ_inj: forall (x y: term_nat), ($ church_succ (t x)) == ($ church_succ (t y)) -> (t x) == (t y).
Proof.
  intros.
  
Qed. *)




Lemma succ_zero: forall (x: term_nat), ~(($ church_succ (t x)) == church_nat 0).
Proof.
  (* TODO maybe use injectivity of church_nat to "undo" church_succ and use the equivalent fact in nat to prove this? *)

  intro.
  unfold "==".

  induction (t x).
  - unfold church_succ.
    unfold church_nat.
    unfold church_nat_aux.
    unfold "==".
    



(* ASK associativity is weird as hell, why does Coq want THOSE parentheses? *)
Definition plus: term := \\\\ $ ($ #3 #1) $ $ #2 #1 #0.

(* TODO Notation ++ *)


(* 0 + 0 == 0 *)
Lemma neutral: ($ $ plus (church_nat 0) (church_nat 0)) == (church_nat 0).
Proof.
  common_reduct.
Qed.