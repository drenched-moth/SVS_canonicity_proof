Require Import Nat.
Require Import Vector.
Require Import Bvector.
Require Import Logic.
Require Import Equality.
Require Import Coq.Arith.Arith.

Lemma forall2_hd: forall {n} A (R: A->A-> Prop) x1 x2 (v1 v2: t A n), 
  Forall2 R (x1::v1) (x2::v2) -> R x1 x2.
intros.
inversion H. assumption.
Qed.

Lemma forall2_tl: forall {n} A (R: A->A-> Prop) x1 x2 (v1 v2: t A n),
  Forall2 R (x1::v1) (x2::v2) -> Forall2 R v1 v2.
intros.
dependent induction H. assumption.
Qed.

Locate "<=?".

Compute 1 <=? 1.
Compute Nat.leb 1 1.
Compute Nat.leb 1 2.

Notation "v1 c=? v2" := (fold_left andb true (map2 (Nat.leb) v1 v2)) (at level 50, left associativity).

Check [23;3] c=? [1;2].
Compute [23;3] c=? [1;2].
Check [23;3] = [1;2].
Compute [1;2] c=? [2;4].

Lemma test: ~ ([23;3] = [1;2]).
Proof.
discriminate.
Qed.

Lemma test1: [2;32] c=? [65;6] = false.
Proof.
compute.
trivial.
Qed.

Lemma test12: [1;2;5;6;8] c=? [1;3;6;190;90] = true.
compute.
trivial.
Qed.

Locate "<=".
Check le.
Check Forall2.

Definition VecIncluded {n} (a b: t nat n): Prop :=
  Forall2 le a b.

Notation "v1 c= v2" := (VecIncluded v1 v2) (at level 50, left associativity).

Check [1] c= [2].
Compute [1] c= [2].

Lemma test2: [12; 2] c= [197; 5].
Proof.
compute.
apply Forall2_cons; repeat (trivial || apply le_S).  auto. 
apply Forall2_cons; repeat (trivial || apply le_S).
apply Forall2_nil.
Qed.

Locate "<".

Definition VecNotIncluded {n} (a b: t nat n): Prop :=
  Exists2 lt b a.

(* Je n'ai pas su comment faire une preuve par négation sur la définition précédente, 
par conséquent je propose la définition alternative *)
Notation "v1 c/= v2" := (VecNotIncluded v1 v2) (at level 50).

Lemma test3: [3; 5; 6] c/= [4; 4; 4].
Proof.
compute.
eapply Exists2_cons_tl.
eapply Exists2_cons_hd.
trivial.
Qed.


Lemma test5: ~ [1;4;5] = [2;34;6].
Proof.
discriminate.
Qed.

Lemma test6: [1;0;67] = [1;0;67].
Proof.
trivial.
Qed.

Lemma vec_eq_impl_incl: forall {n} (a b: t nat n), a = b -> a c= b. 
intros. compute.
rewrite <- H.
apply Forall2_nth. intros.
trivial.
Qed. 

Check [1;2] = 1::[2].

Lemma vec_inclusion_antisymm: forall {n} (a b: t nat n), a c= b /\ b c= a -> a = b.
intros.
compute in H. destruct H as [H0 H1].
dependent induction H0. trivial.
assert (x2<=x1).
apply (forall2_hd) in H1; trivial.
assert (x1=x2).
apply Nat.le_antisymm; assumption.
apply forall2_tl in H1. apply IHForall2 in H1.
rewrite H1; rewrite H3. trivial.
Qed.

Lemma test8: forall {n} (a b: t nat n), ~(a c= b) <-> VecNotIncluded a b.
intros. split; intros.
compute in H. 
Search (_ -> False -> _).
Check except.
compute.
inversion H.
compute. compute in H.

Lemma test8: forall {n} (a b: t nat n), 0<n -> ~VecIncluded a b <-> VecNotIncluded a b.
intros.
split.
-admit.
- vm_compute. 
intros. induction n. easy. (* SearchPattern (_ < _ -> _). easy. apply PeanoNat.Nat.lt_succ_l in H. absurd H. *)
admit.
Admitted.

Definition VecComparable {n} (a b: t nat n): Prop :=
  a c= b \/ b c= a.

Definition VecNotComparable {n} (a b: t nat n): Prop :=
  a c/= b /\ b c/= a.

(* Il faut définir les vecteurs symboliques *)



