Require Import Nat.
Require Import Vector.
Require Import Bvector.
Require Import Logic.
Require Import Equality.
Require Import Coq.Arith.Arith.
Require Import Setoids.Setoid.

Lemma forall2_hd: forall {n} A (R: A->A-> Prop) x1 x2 (v1 v2: t A n), 
  Forall2 R (x1::v1) (x2::v2) -> R x1 x2.
intros. 
inversion_clear H. assumption.
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

Lemma jsp: 
  forall {n} (a b: t nat n), ~(a c= b) -> Exists2 lt b a.
Proof.
intros. compute in H .
Abort.

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

Lemma vec_inclusion_antisymm: forall {n} (a b: t nat n), a c= b /\ b c= a <-> a = b.
split ; intros.
- compute in H. destruct H as [H0 H1].
  dependent induction H0. reflexivity.
  assert (x2<=x1).
  apply (forall2_hd) in H1; trivial.
  assert (x1=x2).
  apply Nat.le_antisymm; assumption.
  apply forall2_tl in H1. apply IHForall2 in H1.
  rewrite H1; rewrite H3. trivial.
- dependent induction H.
  split; apply vec_eq_impl_incl; trivial.
Qed.

Lemma vec_forall2_impl_exists2 {n} {A} R (a b: t A (S n)): 
  Forall2 R a b -> Exists2 R a b.
Proof.
intros.
dependent induction H.
apply Exists2_cons_hd.
assumption.
Qed.

Search In.
Check In.
Check In_nth.

Search ((?a -> ?b) <-> (~?b -> ~?a)).

Lemma contrapose (P Q: Prop) : (P -> Q) -> ~Q -> ~P.
Proof.
compute. intros. apply H0, H, H1.
Qed.

Require Import Coq.Logic.Classical_Prop.

Lemma contrapose1 (P Q: Prop) : ((~P) -> Q) -> (~Q -> P).
Proof.
intros.
Admitted.

Lemma forall2_neg_impl_neg_forall2 {n A} R (a b: t A (S n)):
  Forall2 (fun x y => ~ R x y) a b -> ~ (Forall2 R a b).
Proof.
intros.
compute. intro.
dependent induction H0.
apply forall2_hd in H.
contradiction H.
Qed.

Lemma forall2_iff_neg_forall2_neg_relation {n A} R (a b: t A (S n)):
  Forall2 R a b <-> ~(Forall2 (fun x y => ~ R x y) a b).
Proof.
split.
intros. intro.
dependent induction H0.
contradiction H1.
apply forall2_hd in H.
assumption.
Admitted.

Theorem dist_not_exists : forall (X:Type) (P: X-> Prop),
  (forall x, P x) -> ~(exists x, ~ P x).
Proof.
intros. intros [x Hx].
unfold not in Hx.
apply Hx.
apply H.
Qed.


Lemma vec_exists2_iff_not_forall2 {n} {A} R (a b: t A (S n)):
  Exists2 R a b <-> ~ (Forall2 (fun x y => ~ R x y) a b).
Proof.
split.
- compute. intros.
  induction H.
  + apply forall2_hd in H0. contradiction H0.
  + destruct IHExists2.
    apply forall2_tl in H0.
    trivial.
- intros.
  apply forall2_iff_neg_forall2_neg_relation in H.
  assert (a = (hd a :: tl a) /\ b = (hd b :: tl b)). 
  { split. 
    dependent induction a. compute. reflexivity.
    dependent induction b. compute. reflexivity.
  }
  destruct H0.
  rewrite H0, H1.
  apply Exists2_cons_hd.
  rewrite H0, H1 in H.
  apply forall2_hd in H.
  assumption.
Qed.

Search (_ <= _ -> _ < _).
Search (_ < _ -> _ <= _).
Search (~(_ <= _) -> _).

Lemma vec_not_inclusion: forall {n} (a b: t nat (S n)), ~(a c= b) <-> a c/= b.
intros.
split; intros.
- compute. compute in H.
  apply vec_exists2_iff_not_forall2.
  intro. destruct H.
  apply to_list_Forall2, List.Forall2_flip in H0.
  assert (List.Forall2 (fun x y:nat => ~ S y <= x) (to_list a) (to_list b) -> List.Forall2 (fun x y : nat => x <= y) (to_list a) (to_list b)).
  { apply List.Forall2_impl. 
    intros.
    apply Arith_prebase.gt_S_le_stt.
    apply not_le. trivial. }
  apply to_list_Forall2, H.
  trivial.
- intro. compute in H.
  apply vec_exists2_iff_not_forall2 in H.
  destruct H.
  compute in H0.
  apply to_list_Forall2, List.Forall2_flip.
  assert (List.Forall2 (fun x y:nat => x <= y) (to_list a) (to_list b) -> List.Forall2 (fun x y : nat => ~ S y <= x) (to_list a) (to_list b)).
  { apply List.Forall2_impl.
    intros.
    apply Arith_prebase.gt_not_le_stt.
    apply Arith_prebase.le_gt_S_stt. trivial. }
  apply H, to_list_Forall2. trivial.
Qed.

Lemma vec_not_inclusion_contra {n} (a b: t _ (S n)):
  a c= b <-> ~(a c/= b).
Proof.
split.
unfold not. intros. apply vec_not_inclusion in H0. unfold not in H0. contradiction.
apply NNPP. intro.
apply imply_to_and in H. destruct H. apply vec_not_inclusion in H0. unfold not in H, H0. contradiction.
Qed.

Definition VecComparable {n} (a b: t nat n): Prop :=
  a c= b \/ b c= a.

(*
Definition VecNotComparable {n} (a b: t nat n): Prop :=
  ~ VecComparable a b.*)

Definition VecNotComparable {n} (a b: t nat n): Prop :=
  a c/= b /\ b c/= a.

Lemma lkjsalkjfdsa {n} (a b: t _ (S n)):
  VecComparable a b <-> ~ (VecNotComparable a b).
Proof.
split.
+ intro. unfold not.
  intro. unfold VecComparable in H. unfold VecNotComparable in H0.
  destruct H0.
  destruct H.
  - apply vec_not_inclusion in H0. unfold not in H0. 
    contradiction H0.
  - apply vec_not_inclusion in H1. unfold not in H1.
    contradiction H1.
+ intro. unfold VecNotComparable in H.
  apply not_and_or in H.
  unfold VecComparable.
  destruct H.
  apply vec_not_inclusion_contra in H. left; trivial.
  apply vec_not_inclusion_contra in H. right; trivial.
Qed.

Search "contra".

(* Il faut définir les vecteurs symboliques *)



