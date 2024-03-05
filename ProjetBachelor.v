Require Import Nat.
Require Import Vector.
Require Import Bvector.

Notation "v1 c=? v2" := (fold_left andb true (map2 (Nat.leb) v1 v2)) (at level 50, left associativity).

Check [23;3] c=? [1;2].
Compute [23;3] c=? [1;2].
Check [23;3] = [1;2].

Lemma test: ~ ([23;3] = [1;2]).
Proof.
discriminate.
Qed.

Lemma test1: [2;32] c=? [65;6] = false.
Proof.
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

Definition VecEq {n} (a b: t nat n): Prop :=
  a c= b /\ b c= a.

Check VecEq.

Lemma test4: VecEq [2;3] [2;3].
Proof.
compute.
split; repeat (eapply Forall2_cons; trivial) || eapply Forall2_nil.
Qed.

Require Import Logic.

Lemma test5: ~ [1;4;5] = [2;34;6].
Proof.
discriminate.
Qed.

Lemma test6: [1;0;67] = [1;0;67].
Proof.
trivial.
Qed.

Require Import Equality.

Lemma test7: forall {n} (a b: t nat n), a = b -> a c= b. 
intros.
compute.
dependent induction H.
induction n.
assert ([]=a). apply case0. trivial.
rewrite <- H. apply Forall2_nil.
rename a into b.
apply Forall2_nth. intros. trivial.
Restart.
intros. compute.
rewrite <- H.
apply Forall2_nth. intros.
trivial.
Qed.

Check test7.

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



