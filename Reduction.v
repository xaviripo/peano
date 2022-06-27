Require Import Coq.Arith.EqNat.

Require Import Basics.

(* replace_at l v 0 replaces all first-level instances of #0 with v in l *)
(* every time we enter an abstraction, we increase n by 1 *)
Fixpoint replace_at (l: term) (v: term) (n: nat): term :=
  match l with
  | #n' => if beq_nat n n' then v else #n'
  | \p => \(replace_at p v (S n))
  | $ p q => $ (replace_at p v n) (replace_at q v n)
  end
.

Module test_replace_at.
  Definition test: term := replace_at (\#1) (\#4) 0.
  Compute test. (* -> \ (\ # 4) *)
End test_replace_at.

(* Elementary beta step, only works on terms of the form (\x) $ y *)
Definition beta (p: term): term :=
  match p with
  | #n => p
  | \q => p
  | $ q r => match q with
    | #_ => p
    | \s => replace_at s r 0 (* Replace the variable with q *)
    | $ _ _ => p
    end
  end
.

Module test_beta.
  Definition test := $ (\\#1) (\#7).
  Compute test.
  Compute beta test.
  Definition expr: term := $ $ $ if_then_else lc_true #10 #20.
  Compute expr.
  (* This doesn't reduce because the outermost application (if_then_else $ (... $ ...)) can't reduce *)
  Compute beta expr.
End test_beta.

(* Leftmost-outermost is a normalizing reduction strategy for lc *)
(* i.e. in each step the leftmost of the outermost redexes is contracted, where an outermost redex is a redex not contained in any redexes *)
(* this is known as normal-order reduction in lc (cf. https://en.wikipedia.org/wiki/Reduction_strategy) *)
(* in lc a redex is a lambda abstraction applied to a term, so "(\ ...) $ ..." *)
(* \#0 $ \#0 is a redex that reduces to \#0 *)

(* ASK how do I do leftmost-outermost? I need to walk the tree
recursively but stop at the FIRST application of beta *)

(* fixpoint returning term + bool marking whether we have reduced *)

Fixpoint leftmost_outermost_step_aux (p: term): term * bool :=
  match p with
  | #n => (p, false)
  | \q => let (q', b) := leftmost_outermost_step_aux q in (\q', b)
  | $ q r => match q with
    | #n => let (r', b) := leftmost_outermost_step_aux r in ($ (#n) r', b)
    | \s => (replace_at s r 0, true)
    | $ s t => let (s', bs) := leftmost_outermost_step_aux q in
               let (t', bt) := leftmost_outermost_step_aux t in
      if bs then ($ s' t, bs) else ($ s t', bt)
    end
  end
.

Definition leftmost_outermost_step (p: term): term :=
  let (p', b) := leftmost_outermost_step_aux p in p'
.

Fixpoint leftmost_outermost_aux (p: term) (n: nat): term :=
  match n with
  | 0 => p
  | S m => leftmost_outermost_aux (leftmost_outermost_step p) m
  end
.

Module test_leftmost_outermost_aux.
  Definition expr: term := $ $ $ if_then_else lc_true #10 #20.
  Compute leftmost_outermost_aux expr 0.
  Compute leftmost_outermost_aux expr 1.
  Compute leftmost_outermost_aux expr 2.
  Compute leftmost_outermost_aux expr 3.
  Compute leftmost_outermost_aux expr 4.
  Compute leftmost_outermost_aux expr 5. (* -> # 10 *)
  (* TODO this is not right, fix defn *)
End test_leftmost_outermost_aux.

(* A single step of parallel outermost reduction *)
Fixpoint parallel_outermost_step (p: term): term :=
  match p with
  | #n => p
  | \q => \(parallel_outermost_step q)
  | $ q r => match q with
    | #n => $ (parallel_outermost_step q) (parallel_outermost_step r)
    | \s => replace_at s r 0 (* Replace the variable with q *)
    | $ s t => $ (parallel_outermost_step q) (parallel_outermost_step r)
    end
  end
.

Fixpoint parallel_outermost_aux (p: term) (n: nat): term :=
  match n with
  | 0 => p
  | S m => parallel_outermost_aux (parallel_outermost_step p) m
  end
.

Module test_parallel_outermost_aux.
  Definition expr: term := $ $ $ if_then_else lc_true #10 #20.
  Compute parallel_outermost_aux expr 0.
  Compute parallel_outermost_aux expr 1.
  Compute parallel_outermost_aux expr 2.
  Compute parallel_outermost_aux expr 3.
  Compute parallel_outermost_aux expr 4.
  Compute parallel_outermost_aux expr 5. (* -> # 10 *)
End test_parallel_outermost_aux.

(* n steps of parallel outermost reduction *)
Definition MAX_BETA := 100.
Definition parallel_outermost (p: term): term :=
  parallel_outermost_aux p MAX_BETA
.

(* ASK: any idea of how to approach this? Fixpoint with accumulator? *)
(* Ideally: apply beta MAX_BETA times or stop if the same term is reached twice *)
(* Most efficient way to do this would be to hash every term we go through and compare
the hash at every stage with all previous ones *)
(* The alternative is to store every visited term and compare them *)
(* Seems too expensive *)

Module test_parallel_outermost.
  Definition expr: term := $ $ $ if_then_else lc_true #10 #20.
  Compute expr.
  Compute parallel_outermost expr.
End test_parallel_outermost.

Module test_omega.
  Definition omega := (\$#0#0).
  Compute parallel_outermost_step omega.

  Definition growing := $(\$$#0#0#0)(\$$#0#0#0).
  Compute parallel_outermost_step growing.

  Definition dangerous := $(\#100)$omega omega.
  Compute parallel_outermost_step dangerous.
End test_omega.

(* Program:
- Define beta step (in any subterm)
- Define its transitive closure *)

Require Import Coq.Lists.List.
Import ListNotations.


(* List of all possible 1-step beta reducts of p *)
Fixpoint beta_reducts (p: term): list term :=
  let others := (match p with
  | #n => []
  | \q => map (fun (t: term) => \ t) (beta_reducts q)
  | $ q r => map (fun (t: term) => $ t r) (beta_reducts q) ++ map (fun (t: term) => $ q t) (beta_reducts r)
  end) in
    if term_eq_dec (beta p) p then others else beta p :: others
.

(* p ->_\beta p' *)
Definition beta_step (p p': term): Prop :=
  In p' (beta_reducts p)
.

Inductive closure {X: Type} (P: X -> X -> Prop): X -> X -> Prop :=
(* In the base case, every element of X is related to itself. *)
| CStep: forall x y, P x y -> closure P x y
| CRefl:
    forall x,
      closure P x x
| CSym:
    forall x x',
      closure P x x' ->
      closure P x' x
| CTrans:
    forall x x' x'',
      closure P x x' ->
      closure P x' x'' ->
      closure P x x''
.

Definition beta_equiv: term -> term -> Prop := closure beta_step.

Notation "p == q" := (beta_equiv p q) (at level 70, no associativity).

Lemma BetaRefl: forall (p: term), p == p.
Proof. apply CRefl. Qed.

Lemma BetaSym: forall (p q: term), p == q -> q == p.
Proof. apply CSym. Qed.

Lemma BetaTrans: forall (p q r: term), p == q -> q == r -> p == r.
Proof. apply CTrans. Qed.

Add Parametric Relation: term beta_equiv
  reflexivity proved by BetaRefl
  symmetry proved by BetaSym
  transitivity proved by BetaTrans
  as beta_eq.

Require Import Coq.Setoids.Setoid.


Add Parametric Morphism: Abs with
  signature beta_equiv ==>
    beta_equiv
  as beta_mor_abs.
Proof.
  intros.
  unfold "==" in *.
  induction H.
  - apply CStep.
    unfold beta_step in *.
    simpl.
    destruct (term_eq_dec (\x) (\x)).
    + induction (beta_reducts x).
      * now exfalso.
      * simpl.
        induction H.
        -- left.
           now rewrite H.
        -- right.
           now apply IHl.
    + intuition.
  - apply CRefl.
  - now apply CSym.
  - now apply CTrans with (x' := \ x').
Qed.

Add Parametric Morphism: App with
  signature beta_equiv ==>
    beta_equiv ==>
    beta_equiv
  as beta_mor_app.
Admitted. (* TODO *)

Fixpoint acc_step (p: term) (depth: nat): list (list term) :=
  match depth with
  | 0 => [[p]]
  | S n => let old_reducts := acc_step p n in
            let candidates := filter (fun (l: list term) => beq_nat (length l) (S n)) old_reducts in
            (* TODO maybe change hd to hd_error *)
            (* TODO can be made more efficient by filtering duplicates out *)
            old_reducts ++ flat_map (fun (candidate: list term) => map (fun reduct => (reduct :: candidate)) (beta_reducts (hd (#0) candidate))) candidates
  end
.

(* Compute acc_step ($ $ $ if_then_else lc_true #10 #20) 0.
Compute acc_step ($ $ $ if_then_else lc_true #10 #20) 1.
Compute acc_step ($ $ $ if_then_else lc_true #10 #20) 2.
Compute acc_step ($ $ $ if_then_else lc_true #10 #20) 3.
Compute acc_step ($ $ $ if_then_else lc_true #10 #20) 4. *)

Fixpoint cartesian {A B: Type} (l: list A) (m: list B): list (A * B) :=
  match l with
  | [] => []
  | a :: l' => map (fun b => (a, b)) m ++ cartesian l' m
  end
.

Definition common_reducts (l m: list (list term)): (list term * list term) :=
  hd ([], []) (filter (fun (x: list term * list term) => let (a, b) := x in term_beq (hd (#0) a) (hd (#0) b)) (cartesian l m))
.

Compute (common_reducts (acc_step ($ (\ #0) $ (\ # 10) (# 20)) 10) (acc_step (#10) 10)).

Ltac common_reduct_aux l :=
  idtac l;
  match eval compute in l with
  | nil => idtac
  | ?a :: ?l' => apply CTrans with (x' := a); (* TODO rewrite this using next_reduct *)
                [ apply CStep; unfold beta_step; simpl; left; reflexivity | ];
                common_reduct_aux l'
  end
.


Definition COMMON_REDUCT_MAX_DEPTH := 10.
Ltac common_reduct := match goal with
  | |- (?a == ?b) =>
    unfold "==";
    match eval compute in (common_reducts (acc_step a COMMON_REDUCT_MAX_DEPTH) (acc_step b COMMON_REDUCT_MAX_DEPTH)) with
    | (?k, ?l) => let k' := eval compute in (tl (rev k)) in (common_reduct_aux k');
                  apply CSym;
                  let l' := eval compute in (tl (rev l)) in (common_reduct_aux l');
            apply CRefl
    (* TODO add second matching case | None => ... and make it work *)
    end
end.


Ltac next_reduct p := apply CTrans with (x' := p);
[ apply CStep; unfold beta_step; simpl; now left | ].

Module test_beta_equiv.
  Definition expr: term := $ $ $ if_then_else lc_true #10 #20.
  Lemma test: beta_equiv expr (#10).
  Proof.
    unfold "==".
    unfold expr.
    unfold if_then_else, lc_true.
    apply CTrans with (x' := $ $ (\ (\ $ $ (\ (\ # 1)) (# 1) (# 0))) (# 10) (# 20));
    [ apply CStep; unfold beta_step; simpl; now left | ].
    apply CTrans with (x' := $ (\ $ $ (\ (\ # 1)) (# 10) (# 0)) (# 20));
    [ apply CStep; unfold beta_step; simpl; now left | ].
    apply CTrans with (x' := $ $ (\ (\ # 1)) (# 10) (# 20));
    [ apply CStep; unfold beta_step; simpl; now left | ].
    apply CTrans with (x' := $ (\ # 10) (# 20));
    [ apply CStep; unfold beta_step; simpl; now left | ].
    apply CTrans with (x' := # 10);
    [ apply CStep; unfold beta_step; simpl; now left | ].
    apply CRefl.
  Qed.
End test_beta_equiv.

(* TODO idea write a tactic for defining a reduction path
something that simplifies this process above ^ of stating transitivity paths *)
