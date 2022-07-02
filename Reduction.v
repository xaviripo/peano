Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Require Import Basics.

Require Import Coq.Arith.Compare_dec.

Fixpoint increase_free_variables (p: term) (increment level: nat): term :=
  match p with
  | #n => if (lt_dec n level) (* if n < level *)
    then #n (* #n was bound, leave it as it is *)
    else #(n + increment) (* #n was free, must increase it *)
  | \q => \(increase_free_variables q increment (S level))
  | $ q r => $ (increase_free_variables q increment level) (increase_free_variables r increment level)
  end
.

(* replace l v 0 replaces all first-level instances of #0 with v in l *)
(* every time we enter an abstraction, we increase n by 1 *)
(* level: abstraction level at which we are *)
Fixpoint replace (body argument: term) (level: nat): term :=
  match body with
  | #n => match level ?= n with
    | Lt => #(n - 1) (* #n is a free variable in body, we decrease it by 1 because we are removing an abstraction *)
    | Eq => increase_free_variables argument n 0 (* #n is the variable to replace, remember to increase the free vars in argument! *)
    | Gt => #n (* #n is bound in body *)
    end
  | \p => \(replace p argument (S level))
  | $ p q => $ (replace p argument level) (replace q argument level)
  end
.

Module test_replace.
  Compute replace (\ $ ($ #3 #1) (\ $ #0 #2)) (\ $ #4 #0) 0.
  (* The final result should be \ $ $ (# 2) (\ $ (# 5) (# 0)) (\ $ (# 0) (\ $ (# 6) (# 0))) *)
  Compute replace (\ $ ($ #3 #1) (\ \ $ #1 #3)) (\ $ #4 #0) 0.

  Definition test: term := replace (\#1) (\#4) 0.
  Compute test. (* -> \ (\ # 5) *)
End test_replace.




Inductive path :=
| PRoot
| PAbs: path -> path
| PLeft: path -> path
| PRight: path -> path
.

Fixpoint beta (p: term) (rt: path): option term :=
  match p, rt with

  | #n, _ => None (* No reduction/Invalid path *)

  | \q, PAbs rt' => let q' := beta q rt' in
    match q' with
    | Some q'' => Some (\q'')
    | None => None
    end
  | \q, _ => None (* Invalid path *)

  | $ (\q) r, PRoot => Some (replace q r 0)
  | $ q r, PLeft rt' => let q' := beta q rt' in
    match q' with
    | Some q'' => Some $ q'' r
    | None => None
    end
  | $ q r, PRight rt' => let r' := beta r rt' in
    match r' with
    | Some r'' => Some $ q r''
    | None => None
    end
  | $ _ _, _ => None (* Invalid path *)

  end
.



Definition beta_step (p p': term): Prop :=
  exists (rt: path), beta p rt = Some p'.

Module test_beta_step.
  Goal beta_step ($ \(#0) \\(#1)) (\\#1).
    unfold beta_step.
    exists PRoot.
    reflexivity.
  Qed.
End test_beta_step.


(* Leftmost-outermost is a normalizing reduction strategy for lc *)
(* i.e. in each step the leftmost of the outermost redexes is contracted, where an outermost redex is a redex not contained in any redexes *)
(* this is known as normal-order reduction in lc (cf. https://en.wikipedia.org/wiki/Reduction_strategy) *)
(* in lc a redex is a lambda abstraction applied to a term, so "(\ ...) $ ..." *)
(* \#0 $ \#0 is a redex that reduces to \#0 *)

(* TODO redefine these reduction strategies to use beta() *)
(* A single step of parallel outermost reduction *)
Fixpoint parallel_outermost_step (p: term): option term :=
  match p with
  | #n => None
  | \q => let q' := parallel_outermost_step q in match q' with
    | None => None
    | Some q'' => Some (\q'')
    end
  | $ (\q) r => beta p (PRoot)
  | $ q r => let q' := parallel_outermost_step q in
    let r' := parallel_outermost_step r in
    match (q', r') with
    | (None, Some r'') => Some ($ q r'')
    | (Some q'', None) => Some ($ q'' r)
    | (Some q'', Some r'') => Some ($ q'' r'')
    | (None, None) => None
    end
  end
.

Fixpoint parallel_outermost_aux (p: term) (n: nat): term :=
  match n with
  | 0 => p
  | S m => let p' := parallel_outermost_step p in match p' with
    | Some p'' => parallel_outermost_aux p'' m
    | None => p (* No further reduction? Just return the term as-is *)
    end
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

Module test_parallel_outermost.
  Definition expr: term := $ $ $ if_then_else lc_true #10 #20.
  Compute expr.
  Compute parallel_outermost expr.
End test_parallel_outermost.

Module test_omega.
  Definition omega := (\$#0#0).
  Compute parallel_outermost_step omega.

  Definition omega_omega := $ omega omega.
  Compute parallel_outermost_step omega_omega.

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

(* Fixpoint build_indices (p: term): list path :=
  match p with
  | #n => [ PRoot ]
  | \q => PRoot :: map PAbs (build_indices q)
  | $ q r => PRoot :: map PLeft (build_indices q) ++ map PRight (build_indices r)
  end
. *)

(* Compute build_indices (\\$#0#1). *)

Fixpoint leftmost_outermost_step (p: term): option (term * path) :=
  match p with
  | #n => None
  | \q => let q' := leftmost_outermost_step q in match q' with
    | None => None
    | Some (q'', rt) => Some (\q'', PAbs rt)
    end
  | $ (\q) r => let p' := beta p (PRoot) in
    match p' with
    | Some p'' => Some (p'', PRoot)
    | None => None
    end
  | $ q r => let q' := leftmost_outermost_step q in
    let r' := leftmost_outermost_step r in
    match (q', r') with
    | (Some (q'', rt), _) => Some ($ q'' r, PLeft rt)
    | (None, Some (r'', rt)) => Some ($ q r'', PRight rt)
    | (None, None) => None
    end
  end
.



Module test_leftmost_outermost_step.
  Definition expr: term := $ ($ ($ if_then_else lc_true) #10) #20.
  Compute expr.
  Compute leftmost_outermost_step expr.
End test_leftmost_outermost_step.


Ltac reduct rt := match goal with
| |- (?a == ?b) =>
  match eval compute in (beta a rt) with
  | Some ?a_reduct => transitivity a_reduct; [ apply CStep; exists rt; reflexivity | ]
  | None => fail
  end
end.

Goal ($ \ #0 #100) == #100.
  reduct PRoot.
  reflexivity.
Qed.


(* TODO fix this for some reason it doesn't stop at normal forms *)
Ltac common_reduct := match goal with
| |- (?a == ?b) =>
  match eval compute in (leftmost_outermost_step a) with
  | Some (?a_reduct, ?a_path) => transitivity a_reduct; [ apply CStep; exists a_path; reflexivity | ]
  | None => idtac
  end;
  symmetry;
  match eval compute in (leftmost_outermost_step b) with
  | Some (?b_reduct, ?b_path) => transitivity b_reduct; [ apply CStep; exists b_path; reflexivity | ]
  | None => idtac
  end;
  symmetry;
  try reflexivity;
  try common_reduct
end.

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
    destruct H.
    exists (PAbs x0).
    unfold beta; fold beta.
    now rewrite H.
  - apply CRefl.
  - now apply CSym.
  - apply CTrans with (x' := (\ x')); easy.
Qed.


Add Parametric Morphism: App with
  signature beta_equiv ==>
    beta_equiv ==>
    beta_equiv
  as beta_mor_app.
Proof.
  intros.
  induction x, y.
  (* The new definition of beta using option term doesn't really allow this *)
  - Admitted.
