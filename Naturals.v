
Require Import Basics.
Require Import Reduction.

Fixpoint church_nat_aux (n: nat): term :=
  match n with
  | 0 => #0
  | S n' => $ (#1) (church_nat_aux n')
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
  \\(church_nat_aux n)
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
  \\\ $ (#1) ($ ($ (#2) (#1)) (#0))
.

(* apply CTrans with (x' := p);
[ apply CStep; unfold beta_step; simpl; now left | ]. *)

(* Lemma replace_lemma (n: nat): $ (\ (\ church_nat_aux n)) (# 1) == \ church_nat_aux n.
Proof.
  induction n.
  (* TODO do base case! *)
  Focus 2.
  unfold church_nat_aux; fold church_nat_aux. *)


Fixpoint abstractionless (p: term): Prop :=
  match p with
  | #n => True
  | \q => False
  | $ q r => (abstractionless q) /\ (abstractionless r)
  end
.
Require Import Coq.Arith.EqNat.

Compute beta $ (\ #23) (#0) PRoot.

(* Lemma eta_lemma (p: term) (_: abstractionless p) (n: nat): replace p (#n) n = p.
Proof.
  induction p.
  - unfold replace.
    destruct (EqNat.eq_nat_decide n n0).
    + f_equal.
      unfold increase_free_variables.
      destruct (Compare_dec.le_lt_dec 0 n).
      * 
      now apply eq_nat_eq.
    + reflexivity.
  - contradict H.
  - unfold replace; fold replace.
    destruct H.
    f_equal.
    + now apply IHp1.
    + now apply IHp2.
Qed.


Lemma eta (p: term) (_: abstractionless p): $ (\ p) (#0) == p.
Proof.
  apply CStep.
  exists PRoot.
  unfold beta.
  f_equal.
  now apply eta_lemma.
Qed.

Lemma eta1 (p: term) (_: abstractionless p): $ (\\ p) (#1) == \p.
Proof.
  apply CStep.
  exists PRoot.
  unfold beta.
  unfold replace; fold replace.
  f_equal.
  f_equal.
  now apply eta_lemma.
Qed.

Lemma abstractionless_church_nat_aux (n: nat): abstractionless (church_nat_aux n).
Proof.
  induction n.
  - now unfold church_nat_aux.
  - unfold church_nat_aux; fold church_nat_aux.
    now unfold abstractionless; fold abstractionless.
Qed. *)

Compute let n:=2 in (increase_free_variables (church_nat_aux n) 2 2, church_nat_aux n).

Lemma aux (n: nat): increase_free_variables (church_nat_aux n) 2 2 = church_nat_aux n.
Proof.
  induction n.
  - now simpl.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    now rewrite IHn.
Qed.


Lemma aux' (n: nat): increase_free_variables (church_nat_aux n) 1 2 = church_nat_aux n.
Proof.
  induction n.
  - now simpl.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    now rewrite IHn.
Qed.



Lemma aux'' (n: nat): increase_free_variables (church_nat_aux n) 0 2 = church_nat_aux n.
Proof.
  induction n.
  - now simpl.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    now rewrite IHn.
Qed.



Require Import Coq.Classes.Morphisms. (* to use f_equiv if necessary *)

Compute (replace (church_nat_aux 0) (# 1) 1).
Compute (replace (church_nat_aux 1) (# 1) 1).
Compute (replace (church_nat_aux 2) (# 1) 1).
Compute (replace (church_nat_aux 3) (# 1) 1).

Lemma lemma_replace (n: nat): replace (replace (church_nat_aux n) (# 1) 1) (# 0) 0 = church_nat_aux n.
Proof.
  induction n.
  - easy.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    f_equal.
    apply IHn.
Qed.

Lemma church_succ_respects_nat (n: nat): $ church_succ (church_nat n) == church_nat (S n).
Proof.
  unfold church_succ.
  Compute beta ($ (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (church_nat n)) (PRoot).
  transitivity (\ (\ $ (# 1) $ $ (church_nat n) (# 1) (# 0))).
  - apply CStep.
    exists PRoot.
    simpl.
    unfold church_nat.
    now rewrite (aux n).
  - unfold church_nat.
    unfold church_nat_aux; fold church_nat_aux.
    destruct n.
    + common_reduct.
    + unfold church_nat_aux; fold church_nat_aux.
      transitivity (\\ $ (#1) $ (\ $ (#2) (replace (church_nat_aux n0) (#1) 1)) (#0)).
      * apply CStep.
        now exists (PAbs (PAbs (PRight (PLeft PRoot)))).
      * transitivity (\ (\ $ (# 1) $ (# 1) (replace (replace (church_nat_aux n0) (# 1) 1) (# 0) 0))).
        -- apply CStep.
           now exists (PAbs (PAbs (PRight PRoot))).
        -- now rewrite lemma_replace.
Qed.




Lemma church_nat_inj: forall (n m: nat), church_nat n == church_nat m -> n = m.
Proof.
  intros.
  induction n0, m.
  - easy.
  - unfold church_nat in H.
    unfold church_nat_aux in H; fold church_nat_aux in H.
    Admitted.

Lemma church_succ_inj: forall (x y: term_nat), ($ church_succ (t x)) == ($ church_succ (t y)) -> (t x) == (t y).
Proof.
  (* TODO create a tactic to rewrite term_nats into church_nat n? *)
  intros.
  destruct x, y.
  destruct n0, n1.
  simpl.
  rewrite e.
  rewrite e0.
  simpl in H.
  rewrite e, e0 in H.
  rewrite church_succ_respects_nat in H.
  rewrite church_succ_respects_nat in H.
  apply church_nat_inj in H.
  injection H.
  intro.
  rewrite H0.
  reflexivity.
Qed.


(* TODO explain possible pitfall: \ x == \ #0 f_equal x == #0 !!! out of context #0 is nothing *)

Lemma succ_zero: forall (x: term_nat), ~(($ church_succ (t x)) == church_nat 0).
Proof.
  intro.
  destruct x.
  destruct n0.
  simpl.
  rewrite e.
  rewrite church_succ_respects_nat.
  intro.
  now apply church_nat_inj in H.
Qed.



(* ASK associativity is weird as hell, why does Coq want THOSE parentheses? *)
(* Definition plus: term := \\\\ $ ($ #3 #1) $ $ #2 #1 #0. *)

Definition plus: term := \\ $ $ (#1) church_succ (#0).
Definition zero: term_nat := church_nat' 0.

(* Lemma add_nat: forall (x y: nat), $ $ plus (church_nat x) (church_nat y) == church_nat (x + y).
Proof.
  intros.
  induction x.
  -  *)


Lemma repl_lemma (n: nat): replace (church_nat_aux n) (church_nat 0) 2 = church_nat_aux n.
Proof.
  induction n.
  - easy.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    now rewrite IHn.
Qed.

Lemma repl_lemma' (n: nat): replace (church_nat_aux n) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) 3 =
church_nat_aux n.
Proof.
  induction n.
  - easy.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    now rewrite IHn.
Qed.


Lemma repl_lemma'' (n: nat): replace (church_nat_aux n) (\ (\ church_nat_aux 0)) 2 = church_nat_aux n.
Proof.
  induction n.
  - easy.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    repeat f_equal.
    unfold church_nat_aux in IHn at 2.
    apply IHn.
Qed.

Lemma repl_lemma''' (n: nat): replace (church_nat_aux n) $ plus (\ (\ church_nat_aux 0)) 3 = church_nat_aux n.
Proof.
  induction n.
  - easy.
  - unfold church_nat_aux; fold church_nat_aux.
    simpl.
    repeat f_equal.
    unfold church_nat_aux in IHn at 2.
    apply IHn.
Qed.



Lemma zero_neutral: forall (n: nat), $ $ plus (church_nat n) (church_nat 0) == church_nat n.
Proof.
  intros.
  induction n0.
  - common_reduct.
  - rewrite <- church_succ_respects_nat.
    rewrite <- IHn0 at 2.
    unfold plus.
    transitivity ($ (\ $ ($ ($ church_succ (church_nat n0)) church_succ) (# 0)) (church_nat 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equiv;
      unfold church_nat;
      repeat f_equal;
      apply aux' | ].
    transitivity ($ $ $ church_succ (church_nat n0) church_succ (church_nat 0));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold church_nat at 2;
      repeat f_equal;
      apply repl_lemma | ].
    symmetry.
    transitivity ($ church_succ $ (\ $ $ (church_nat n0) church_succ (# 0)) (church_nat 0));
    [ apply CStep;
      exists (PRight (PLeft PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux' | ].
    transitivity ($ church_succ $ $ (church_nat n0) church_succ (church_nat 0));
    [ apply CStep;
      exists (PRight PRoot);
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply repl_lemma | ].
    unfold church_succ.
    transitivity (\\ $ (# 1) $ $ ($ $ (church_nat n0) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (church_nat 0)) (# 1) (# 0));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux | ].
    symmetry.
    transitivity ($ $ (\ (\ $ (# 1) $ $ (church_nat n0) (# 1) (# 0))) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (church_nat 0));
    [ apply CStep;
      exists (PLeft (PLeft PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux | ].
    transitivity ($ ((\ $ ((\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0))))) $ $ (church_nat n0) ((\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0))))) (# 0))) (church_nat 0));
    [ apply CStep;
      exists (PLeft PRoot);
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply repl_lemma' | ].
    transitivity (($ (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) $ $ (church_nat n0) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (church_nat 0)));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply repl_lemma'' | ].
    transitivity (((\ (\ $ (# 1) $ $ ($ $ (church_nat n0) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (church_nat 0)) (# 1) (# 0)))));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux | ].
    reflexivity.
Qed.

Definition mult := \\$ $ (#1) ($ plus #0) (church_nat 0).

Lemma mult_nil (n: nat): $ $ mult (church_nat n) (church_nat 0) == church_nat 0.
Proof.
  unfold mult.
  transitivity ($ ((\ $ $ ((church_nat n)) $ plus (# 0) (church_nat 0))) (church_nat 0));
  [ apply CStep;
    exists (PLeft PRoot);
    simpl;
    repeat f_equal;
    unfold church_nat;
    repeat f_equal;
    apply aux' | ].
  transitivity ((($ $ ((church_nat n)) $ plus (church_nat 0) (church_nat 0))));
  [ apply CStep;
    exists (PRoot);
    simpl;
    repeat f_equal;
    unfold church_nat;
    repeat f_equal;
    apply repl_lemma | ].
  induction n.
  - common_reduct.
  - rewrite <- church_succ_respects_nat.
    unfold church_succ.
    transitivity ($ $ ((\ (\ $ (# 1) $ $ ((church_nat n0)) (# 1) (# 0)))) $ plus (church_nat 0) (church_nat 0));
    [ apply CStep;
      exists (PLeft (PLeft PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux | ].
    transitivity ($ ((\ $ ($ plus (church_nat 0)) $ $ (church_nat n0) ($ plus (church_nat 0)) (# 0))) (church_nat 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply repl_lemma''' | ].
    transitivity (($ $ plus (church_nat 0) $ $ (church_nat n0) $ plus (church_nat 0) ((church_nat 0))) );
    [ apply CStep;
      exists ((PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply repl_lemma | ].
    unfold plus at 1.
    transitivity ($ ((\ $ $ (church_nat 0) church_succ (# 0))) $ $ (church_nat n0) $ plus (church_nat 0) (church_nat 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply repl_lemma | ].
    transitivity (($ $ (church_nat 0) church_succ ($ $ (church_nat n0) $ plus (church_nat 0) (church_nat 0))));
    [ apply CStep;
      exists ((PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux'' | ].
    unfold church_nat at 1.
    unfold church_nat_aux.
    transitivity ($ ((\ # 0)) $ $ (church_nat n0) $ plus (church_nat 0) (church_nat 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal | ].
    transitivity ($ $ (church_nat n0) $ plus (church_nat 0) (church_nat 0));
    [ apply CStep;
      exists ((PRoot));
      simpl;
      repeat f_equal;
      unfold church_nat;
      repeat f_equal;
      apply aux'' | ].
      apply IHn.
Qed.
