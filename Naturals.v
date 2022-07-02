
Require Import Basics.
Require Import Reduction.

Fixpoint encode_aux (n: nat): term :=
  match n with
  | 0 => #0
  | S n' => $ (#1) (encode_aux n')
  end
.

(* Module test_encode.
  Compute encode 0.
  Compute encode 1.
  Compute encode 2.
  (* etc. *)
End test_encode. *)

(* Church encoding of a given natural *)
Definition encode (n: nat): term :=
  \\(encode_aux n)
.


Definition succ: term :=
  \\\ $ (#1) ($ ($ (#2) (#1)) (#0))
.

Require Import Coq.Arith.EqNat.

Compute beta $ (\ #23) (#0) PRoot.

Compute let n:=2 in (increase_free_variables (encode_aux n) 2 2, encode_aux n).


(* Some lemmas for the main thms *)
Lemma aux (n: nat): increase_free_variables (encode_aux n) 2 2 = encode_aux n.
Proof.
  induction n.
  - now simpl.
  - unfold encode_aux; fold encode_aux.
    simpl.
    now rewrite IHn.
Qed.

Lemma aux' (n: nat): increase_free_variables (encode_aux n) 1 2 = encode_aux n.
Proof.
  induction n.
  - now simpl.
  - unfold encode_aux; fold encode_aux.
    simpl.
    now rewrite IHn.
Qed.

Lemma aux'' (n: nat): increase_free_variables (encode_aux n) 0 2 = encode_aux n.
Proof.
  induction n.
  - now simpl.
  - unfold encode_aux; fold encode_aux.
    simpl.
    now rewrite IHn.
Qed.



Require Import Coq.Classes.Morphisms. (* to use f_equiv if necessary *)

Compute (replace (encode_aux 0) (# 1) 1).
Compute (replace (encode_aux 1) (# 1) 1).
Compute (replace (encode_aux 2) (# 1) 1).
Compute (replace (encode_aux 3) (# 1) 1).

Lemma lemma_replace (n: nat): replace (replace (encode_aux n) (# 1) 1) (# 0) 0 = encode_aux n.
Proof.
  induction n.
  - easy.
  - unfold encode_aux; fold encode_aux.
    simpl.
    f_equal.
    apply IHn.
Qed.

Lemma succ_encode (n: nat): $ succ (encode n) == encode (S n).
Proof.
  unfold succ.
  Compute beta ($ (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (encode n)) (PRoot).
  transitivity (\ (\ $ (# 1) $ $ (encode n) (# 1) (# 0))).
  - apply CStep.
    exists PRoot.
    simpl.
    unfold encode.
    now rewrite (aux n).
  - unfold encode.
    unfold encode_aux; fold encode_aux.
    destruct n.
    + common_reduct.
    + unfold encode_aux; fold encode_aux.
      transitivity (\\ $ (#1) $ (\ $ (#2) (replace (encode_aux n) (#1) 1)) (#0)).
      * apply CStep.
        now exists (PAbs (PAbs (PRight (PLeft PRoot)))).
      * transitivity (\ (\ $ (# 1) $ (# 1) (replace (replace (encode_aux n) (# 1) 1) (# 0) 0))).
        -- apply CStep.
           now exists (PAbs (PAbs (PRight PRoot))).
        -- now rewrite lemma_replace.
Qed.

(* Sx = Sy -> x = y *)
Lemma encode_inj: forall (n m: nat), encode n == encode m -> n = m.
Proof.
  intros.
  unfold encode in H.
  induction n, m.
  - easy.
  - unfold encode in H.
    unfold encode_aux in H; fold encode_aux in H.
    (* TODO should be easy, haven't had time *)
    Admitted.

Lemma succ_inj: forall (x y: nat), ($ succ (encode x)) == ($ succ (encode y)) -> (encode x) == (encode y).
Proof.
  intros.
  rewrite succ_encode in H.
  rewrite succ_encode in H.
  apply encode_inj in H.
  injection H.
  intro.
  rewrite H0.
  reflexivity.
Qed.

(* x + 0 = 0 *)
Lemma succ_zero: forall (x: nat), ~(($ succ (encode x)) == encode 0).
Proof.
  intro.
  rewrite succ_encode.
  intro.
  now apply encode_inj in H.
Qed.

Definition plus: term := \\ $ $ (#1) succ (#0).


(* More useful lemmas *)
Lemma repl_lemma' (n: nat) (p: term): replace (encode_aux n) p 3 = encode_aux n.
Proof.
  induction n.
  - easy.
  - unfold encode_aux; fold encode_aux.
    simpl.
    repeat f_equal.
    unfold encode_aux in IHn at 2.
    apply IHn.
Qed.

Lemma repl_lemma (n: nat) (p: term): replace (encode_aux n) (p) 2 = encode_aux n.
Proof.
  induction n.
  - easy.
  - unfold encode_aux; fold encode_aux.
    simpl.
    repeat f_equal.
    unfold encode_aux in IHn at 2.
    apply IHn.
Qed.

(* x + 0 = x *)
Lemma zero_neutral: forall (n: nat), $ $ plus (encode n) (encode 0) == encode n.
Proof.
  intros.
  induction n.
  - common_reduct.
  - rewrite <- succ_encode.
    rewrite <- IHn at 2.
    unfold plus.
    transitivity ($ (\ $ ($ ($ succ (encode n)) succ) (# 0)) (encode 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equiv;
      unfold encode;
      repeat f_equal;
      apply aux' | ].
    transitivity ($ $ $ succ (encode n) succ (encode 0));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold encode at 2;
      repeat f_equal;
      apply repl_lemma | ].
    symmetry.
    transitivity ($ succ $ (\ $ $ (encode n) succ (# 0)) (encode 0));
    [ apply CStep;
      exists (PRight (PLeft PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux' | ].
    transitivity ($ succ $ $ (encode n) succ (encode 0));
    [ apply CStep;
      exists (PRight PRoot);
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply repl_lemma | ].
    unfold succ.
    transitivity (\\ $ (# 1) $ $ ($ $ (encode n) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (encode 0)) (# 1) (# 0));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux | ].
    symmetry.
    transitivity ($ $ (\ (\ $ (# 1) $ $ (encode n) (# 1) (# 0))) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (encode 0));
    [ apply CStep;
      exists (PLeft (PLeft PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux | ].
    transitivity ($ ((\ $ ((\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0))))) $ $ (encode n) ((\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0))))) (# 0))) (encode 0));
    [ apply CStep;
      exists (PLeft PRoot);
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply repl_lemma' | ].
    transitivity (($ (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) $ $ (encode n) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (encode 0)));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply repl_lemma | ].
    transitivity (((\ (\ $ (# 1) $ $ ($ $ (encode n) (\ (\ (\ $ (# 1) $ $ (# 2) (# 1) (# 0)))) (encode 0)) (# 1) (# 0)))));
    [ apply CStep;
      exists PRoot;
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux | ].
    reflexivity.
Qed.

(* Automate some work *)
Ltac step p rt := transitivity p;
  [ apply CStep;
    exists rt;
    simpl;
    repeat f_equal;
    unfold encode;
    repeat f_equal;
    try apply repl_lemma;
    try apply repl_lemma';
    try apply aux;
    try apply aux';
    try apply aux'' | ].

(* x + S(y) = S(x + y) *)
Lemma plus_succ (n m: nat): $ $ plus (encode n) ($ succ (encode m)) == $ succ $ $ plus (encode n) (encode m).
Proof.
  induction m.
  - rewrite zero_neutral.
    unfold plus.
    step ($ ((\ $ $ (encode n) succ (# 0))) $ succ (encode 0)) (PLeft PRoot).
    step (($ $ (encode n) succ ($ succ (encode 0)))) (PRoot).
    induction n.
    + common_reduct.
    + rewrite <- succ_encode.
      unfold succ at 1.
      step ($ $ ((\ (\ $ (# 1) $ $ (encode n) (# 1) (# 0)))) succ $ succ (encode 0)) (PLeft (PLeft PRoot)).
      step ($ ((\ $ succ $ $ (encode n) succ (# 0))) $ succ (encode 0)) (PLeft PRoot).
      step (($ succ $ $ (encode n) succ $ succ (encode 0))) PRoot.
      f_equiv.
      apply IHn.
  - rewrite <- succ_encode.
    unfold plus at 1.
    step ($ ((\ $ $ (encode n) succ (# 0))) $ succ $ succ (encode m)) (PLeft PRoot).
    step (($ $ (encode n) succ ($ succ $ succ (encode m)))) (PRoot).
    rewrite IHm.
    clear IHm.
    induction n.
    + unfold encode at 1.
      unfold encode_aux at 1.
      step ($ (\ # 0) $ succ $ succ (encode m)) (PLeft PRoot).
      step ($ succ $ succ (encode m)) (PRoot).
      repeat f_equiv.
      unfold plus, encode at 2.
      symmetry.
      step ($ ((\ $ $ (\ (\ encode_aux 0)) succ (# 0))) (encode m)) (PLeft PRoot).
      step ((($ $ (\ (\ encode_aux 0)) succ (encode m))) ) (PRoot).
      unfold encode_aux.
      step ($ ((\ # 0)) (encode m)) (PLeft PRoot).
      step (encode m) (PRoot).
      reflexivity.
    + rewrite <- succ_encode in *.
      unfold succ at 1.
      step ($ $ ((\ (\ $ (# 1) $ $ (encode n) (# 1) (# 0)))) succ $ succ $ succ (encode m)) (PLeft (PLeft PRoot)).
      step ($ ((\ $ succ $ $ (encode n) succ (# 0))) $ succ $ succ (encode m)) (PLeft PRoot).
      step (($ succ $ $ (encode n) succ ($ succ $ succ (encode m)))) (PRoot).
      f_equiv.
      transitivity ($ succ $ succ $ $ plus (encode n) (encode m)).
      * apply IHn.
      * f_equiv.
        symmetry.
        unfold plus at 1.
        step ($ ((\ $ $ $ succ (encode n) succ (# 0))) (encode m)) (PLeft PRoot).
        step (($ $ $ succ (encode n) succ (encode m))) PRoot.
        unfold succ at 1.
        step ($ $ ((\ (\ $ (# 1) $ $ ((encode n)) (# 1) (# 0)))) succ (encode m)) (PLeft (PLeft PRoot)).
        step ($ ((\ $ succ $ $ (encode n) succ (# 0))) (encode m)) (PLeft PRoot).
        step ($ succ $ $ (encode n) succ (encode m)) PRoot.
        f_equiv.
        symmetry.
        unfold plus.
        step ($ ((\ $ $ (encode n) succ (# 0))) (encode m)) (PLeft PRoot).
        step ($ $ (encode n) succ (encode m)) PRoot.
        reflexivity.
Qed.

Definition mult := \\$ $ (#1) ($ plus #0) (encode 0).

(* x * 0 = 0 *)
Lemma mult_nil (n: nat): $ $ mult (encode n) (encode 0) == encode 0.
Proof.
  unfold mult.
  transitivity ($ ((\ $ $ ((encode n)) $ plus (# 0) (encode 0))) (encode 0));
  [ apply CStep;
    exists (PLeft PRoot);
    simpl;
    repeat f_equal;
    unfold encode;
    repeat f_equal;
    apply aux' | ].
  transitivity ((($ $ ((encode n)) $ plus (encode 0) (encode 0))));
  [ apply CStep;
    exists (PRoot);
    simpl;
    repeat f_equal;
    unfold encode;
    repeat f_equal;
    apply repl_lemma | ].
  induction n.
  - common_reduct.
  - rewrite <- succ_encode.
    unfold succ.
    transitivity ($ $ ((\ (\ $ (# 1) $ $ ((encode n)) (# 1) (# 0)))) $ plus (encode 0) (encode 0));
    [ apply CStep;
      exists (PLeft (PLeft PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux | ].
    transitivity ($ ((\ $ ($ plus (encode 0)) $ $ (encode n) ($ plus (encode 0)) (# 0))) (encode 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply repl_lemma' | ].
    transitivity (($ $ plus (encode 0) $ $ (encode n) $ plus (encode 0) ((encode 0))) );
    [ apply CStep;
      exists ((PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply repl_lemma | ].
    unfold plus at 1.
    transitivity ($ ((\ $ $ (encode 0) succ (# 0))) $ $ (encode n) $ plus (encode 0) (encode 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply repl_lemma | ].
    transitivity (($ $ (encode 0) succ ($ $ (encode n) $ plus (encode 0) (encode 0))));
    [ apply CStep;
      exists ((PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux'' | ].
    unfold encode at 1.
    unfold encode_aux.
    transitivity ($ ((\ # 0)) $ $ (encode n) $ plus (encode 0) (encode 0));
    [ apply CStep;
      exists (PLeft (PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal | ].
    transitivity ($ $ (encode n) $ plus (encode 0) (encode 0));
    [ apply CStep;
      exists ((PRoot));
      simpl;
      repeat f_equal;
      unfold encode;
      repeat f_equal;
      apply aux'' | ].
      apply IHn.
Qed.

(* x * S(y) = x * y + x *)
Lemma mult_plus (n m: nat): $ $ mult (encode n) ($ succ (encode m)) == $ $ plus $ $ mult (encode n) (encode m) (encode n).
Proof.
  induction n, m.
  - common_reduct.
  - rewrite <- succ_encode.
    unfold mult.
    step ($ ((\ $ $ ((encode 0)) $ plus (# 0) (encode 0))) $ succ $ succ (encode m)) (PLeft PRoot).
    step (($ $ (encode 0) $ plus ($ succ $ succ (encode m)) (encode 0))) PRoot.
    unfold encode at 1.
    simpl.
    step ($ ((\ # 0)) (encode 0)) (PLeft PRoot).
    step (encode 0) PRoot.
    symmetry.
    unfold plus at 1.
    step ($ ((\ $ $ ($ $ (\ (\ $ $ (# 1) $ plus (# 0) (encode 0))) (encode 0) $ succ (encode m)) succ (# 0))) (encode 0)) (PLeft PRoot).
    step (($ $ $ $ (\ (\ $ $ (# 1) $ plus (# 0) (encode 0))) (encode 0) $ succ (encode m) succ ((encode 0)))) PRoot.
    step ($ $ $ ((\ $ $ (encode 0) $ plus (# 0) (encode 0))) $ succ (encode m) succ (encode 0)) (PLeft (PLeft (PLeft PRoot))).
    step ($ $ ($ $ (encode 0) $ plus ($ succ (encode m)) (encode 0)) succ (encode 0)) (PLeft (PLeft PRoot)).
    unfold encode at 1.
    simpl.
    step ($ $ $ ((\ # 0)) (encode 0) succ (encode 0)) (PLeft (PLeft (PLeft PRoot))).
    step ($ $ (encode 0) succ (encode 0)) (PLeft (PLeft PRoot)).
    unfold encode at 1.
    simpl.
    step ($ ((\ # 0)) (encode 0)) (PLeft PRoot).
    step (encode 0) PRoot.
    reflexivity.
  - rewrite mult_nil.
    rewrite mult_nil in IHn.
    rewrite <- succ_encode.
    rewrite plus_succ.
    rewrite <- IHn.
    unfold mult at 1.
    step ($ ((\ $ $ $ succ (encode n) $ plus (# 0) (encode 0))) $ succ (encode 0)) (PLeft PRoot).
    step (($ $ $ succ (encode n) $ plus ($ succ (encode 0)) (encode 0))) PRoot.
    symmetry.
    unfold mult at 1.
    step ($ succ $ ((\ $ $ ((encode n)) $ plus (# 0) (encode 0))) $ succ (encode 0)) (PRight (PLeft PRoot)).
    step ($ succ ($ $ (encode n) $ plus ($ succ (encode 0)) (encode 0))) (PRight PRoot).
    symmetry.
    (* unfold plus at 1.
    step ($ $ $ succ (encode n) ((\ $ $ ($ succ (encode 0)) succ (# 0))) (encode 0)) (PLeft (PRight PRoot)). *)
    unfold succ at 1.
    step ($ $ ((\ (\ $ (# 1) $ $ ((encode n)) (# 1) (# 0)))) $ plus $ succ (encode 0) (encode 0)) (PLeft (PLeft PRoot)).
    step ($ ((\ $ ($ plus $ succ (encode 0)) $ $ (encode n) ($ plus $ succ (encode 0)) (# 0))) (encode 0)) (PLeft PRoot).
    step (( $ $ plus $ succ (encode 0) $ $ (encode n) $ plus $ succ (encode 0) (encode 0))) PRoot.
Admitted.
