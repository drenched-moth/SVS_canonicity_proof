Require Import Nat.
Require Import Vector.
Require Import Bvector.
Require Import Logic.
Require Import Equality.
Require Import Coq.Arith.Arith.

Lemma forall2_hd {n A} R (a b: t A (S n)):
  Forall2 R (hd a::tl a) (hd b::tl b) -> R (hd a) (hd b).
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma forall2_tl {n A} R (a b: t A (S n)):
  Forall2 R (hd a::tl a) (hd b::tl b) -> Forall2 R (tl a) (tl b).
Proof.
intros.
dependent induction H.
assumption.
Qed.

Lemma forall2_hd_tl {n A} R (a b: t A (S n)):
  Forall2 R a b -> (R (hd a) (hd b) /\  Forall2 R (tl a) (tl b)).
Proof.
intros.
assert (a = (hd a:: tl a) /\ b = (hd b:: tl b)). { split; apply eta. }
destruct H0. rewrite H0, H1 in H.
split.
- apply forall2_hd.
  assumption.
- apply forall2_tl.
  assumption.
Qed.

Lemma forall2_arbitrary_hd {n A} R (ah bh: A) (av bv: t A n):
  Forall2 R (ah::av) (bh::bv) -> R ah bh.
Proof.
intros.
inversion H; trivial.
Qed.

Lemma forall2_arbitrary_tl {n A} R (ah bh: A) (av bv: t A n):
  Forall2 R (ah::av) (bh::bv) -> Forall2 R av bv.
Proof.
intros.
dependent induction H; trivial.
Qed.

Lemma forall2_arbitrary_hd_tl {n A} R (ah bh: A) (av bv: t A n):
  Forall2 R (ah::av) (bh::bv) -> R ah bh /\ Forall2 R av bv.
Proof.
intros.
split.
- apply forall2_arbitrary_hd in H; trivial.
- apply forall2_arbitrary_tl in H; trivial.
Qed.

Definition VecsToBoolVec {n} Rb (a b: t nat n): Bvector n :=
  map2 Rb a b.

Notation "v1 c=? v2" := (fold_right andb (VecsToBoolVec Nat.leb v1 v2) true) (at level 50, left associativity). 

Definition VecIncluded {n} (a b: t nat n): Prop :=
  Forall2 le a b.

Notation "v1 c= v2" := (VecIncluded v1 v2) (at level 50, left associativity).

Lemma VecIncludedBool_iff_head_tail {n} (ah bh: _) (av bv: t nat n):
  (ah :: av) c=? (bh :: bv) = true <-> (ah <=? bh = true /\ av c=? bv = true).
Proof.
split.
+ intros.
  inversion H.
  split. 
  - rewrite H1.
    apply andb_prop in H1; destruct H1.
    assumption.
  - apply andb_prop in H1; destruct H1.
    rewrite H0, H1.
    rewrite andb_diag. 
    assumption.
+ intros.
  destruct H.
  simpl.
  apply andb_true_iff.
  split; assumption.
Qed.

Lemma VecIncluded_iff_VecIncludedBool {n} (a b: t nat n):
   a c=? b = true <-> a c= b.
Proof.
split.
- intros.
  dependent induction n.
  + (* init *) 
    assert (a=[] /\ b=[]). { split; apply nil_spec. }
    destruct H0. rewrite H0, H1. 
    apply Forall2_nil.
  + (* induction *)
    assert (a = (hd a :: tl a) /\ b = (hd b :: tl b)). { split; apply eta. }
    destruct H0. rewrite H0, H1.
    rewrite H0, H1 in H.
    apply VecIncludedBool_iff_head_tail in H. destruct H.
    apply Forall2_cons.
    ++  apply leb_complete. 
        assumption.
    ++  apply IHn in H2.
        unfold "c=" in H2.
        assumption.
- intros.
  dependent induction H. compute; trivial.
  apply VecIncludedBool_iff_head_tail.
  split.
  + apply leb_correct. assumption.
  + assumption.
Qed.

Definition VecNotIncludedBool {n} (a b: t nat n) :=
  fold_right orb (VecsToBoolVec Nat.ltb b a) false. (* il faut au moins un élément b_i strictement plus petit que a_i pour que *a* ne soit pas inclu dans *b* *) 

Definition VecNotIncluded {n} (a b: t nat n): Prop :=
  Exists2 lt b a.

Notation "v1 c/=? v2" := (VecNotIncludedBool v1 v2) (at level 50).
Notation "v1 c/= v2" := (VecNotIncluded v1 v2) (at level 50).


Lemma VecNotIncludedBool_iff_head_tail {n} (ah bh: nat) (av bv: t nat n):
  VecNotIncludedBool (ah :: av) (bh :: bv) = true <-> (bh <? ah  = true \/ VecNotIncludedBool av bv = true).
Proof.
split.
- intros.
  unfold VecNotIncludedBool in H.
  inversion H.
  apply orb_true_iff in H1.
  destruct H1. 
  rewrite H0. 
  + left. compute. reflexivity.
  + right. rewrite H0. rewrite orb_true_r. unfold VecNotIncludedBool. assumption.
- intros.
  destruct H.
  unfold VecNotIncludedBool.
  simpl.
  apply orb_true_iff. left; assumption.
  unfold VecNotIncludedBool.
  simpl.
  apply orb_true_iff. right; assumption.
Qed.

Lemma VecNotIncluded_iff_VecNotIncludedBool {n} (a b: t nat n):
  a c/= b <-> a c/=? b = true.
Proof.
split.
- intros.
  induction H.
  + (* init *) 
    apply VecNotIncludedBool_iff_head_tail. left. 
    apply Nat.ltb_lt. assumption.
  + (* induction *)
    apply VecNotIncludedBool_iff_head_tail. right.
    assumption.
- intros.
  dependent induction n.
  + (* init *)
    assert (a=[] /\ b=[]). { split; apply nil_spec. }
    destruct H0. rewrite H0, H1 in H. compute in H.
    unfold "c/=".
    apply eq_true_false_abs in H.
    contradiction. reflexivity.
  + (* induction *)
    assert (a=(hd a :: tl a) /\ b=(hd b :: tl b)). { split; apply eta. }
    destruct H0. rewrite H0, H1 in H. rewrite H0, H1.
    apply VecNotIncludedBool_iff_head_tail in H.
    destruct H.
    ++  unfold "c/=".
        apply Exists2_cons_hd.
        apply Nat.ltb_lt.
        assumption.
    ++  apply Exists2_cons_tl.
        apply IHn. 
        assumption.
Qed.

Lemma VecNotIncludedBool_iff_VecIncludedBool_false {n} (a b: t nat n):
  a c/=? b = true <-> a c=? b = false.
Proof.
split.
- intros.
  dependent induction n.
  + (* init *)
    assert (a=[] /\ b=[]). { split; apply nil_spec. }
    destruct H0.
    rewrite H0, H1 in H.
    compute in H.
    apply eq_true_false_abs in H.
    contradiction. reflexivity.
  + (* induction *)
    assert (a=(hd a :: tl a) /\ b=(hd b :: tl b)). { split; apply eta. }
    destruct H0.
    rewrite H0, H1. rewrite H0, H1 in H.
    simpl.
    apply andb_false_iff.
    apply VecNotIncludedBool_iff_head_tail in H.
    destruct H.
    ++  left. 
        apply leb_iff_conv. 
        apply Nat.ltb_lt in H.
        assumption.
    ++  right.
        apply IHn.
        assumption.
- intros.
  induction n.
  + (* init *)
    assert (a = [] /\ b = []). { split; apply nil_spec. }
    destruct H0.
    rewrite H0, H1 in H.
    compute in H. 
    apply eq_true_false_abs in H.
    contradiction. reflexivity.
  + (* induction *)
    assert (a=(hd a :: tl a) /\ b=(hd b :: tl b)). { split; apply eta. }
    destruct H0.
    rewrite H0, H1. rewrite H0, H1 in H.
    simpl in H.
    apply andb_false_iff in H.
    apply VecNotIncludedBool_iff_head_tail.
    destruct H.
    ++  left.
        apply leb_iff_conv in H.
        apply Nat.ltb_lt.
        assumption.
    ++  right.
        apply IHn.
        assumption.
Qed.

Lemma vec_eq_impl_incl: forall {n} (a b: t nat n), a = b -> a c= b. 
Proof.
intros. compute.
rewrite <- H.
apply Forall2_nth. intros.
trivial.
Qed. 

Lemma vec_inclusion_antisymm: forall {n} (a b: t nat n), a c= b /\ b c= a <-> a = b.
Proof.
split ; intros.
- compute in H. 
  destruct H as [H0 H1].
  dependent induction H0.
  + (* init *)
    reflexivity.
  + (* induction *)
    apply forall2_arbitrary_hd_tl in H1; destruct H1.
    assert (x1=x2). { apply Nat.le_antisymm; assumption. }
    apply IHForall2 in H2.
    rewrite H2; rewrite H3. 
    reflexivity.
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

Lemma forall2_neg_impl_neg_forall2 {n A} R (a b: t A (S n)):
  Forall2 (fun x y => ~ R x y) a b -> ~ (Forall2 R a b).
Proof.
intros.
compute. intro.
dependent induction H.
dependent induction H1.
contradiction.
Qed.

Lemma forall2_iff_neg_forall2_neg_relation {n A} R (a b: t A (S n)):
  Forall2 R a b -> ~(Forall2 (fun x y => ~ R x y) a b).
Proof.
intros. intro.
dependent induction H0.
contradiction H1.
apply forall2_arbitrary_hd in H.
assumption.
Qed.

Lemma not_VecIncluded_iff_VecNotIncluded {n} (a b: t nat n):
  ~(a c= b) <-> a c/= b.
Proof.
intros.
split; intros.
- apply VecNotIncluded_iff_VecNotIncludedBool.
  apply VecNotIncludedBool_iff_VecIncludedBool_false.
  rewrite <- VecIncluded_iff_VecIncludedBool in H.
  apply not_true_is_false.
  assumption.
- rewrite <- VecIncluded_iff_VecIncludedBool.
  apply not_true_iff_false.
  apply VecNotIncludedBool_iff_VecIncludedBool_false.
  apply VecNotIncluded_iff_VecNotIncludedBool.  
  assumption.
Qed.

Lemma not_VecIncluded_iff_VecNotIncluded_contra {n} (a b: t _ n):
  a c= b <-> ~(a c/= b).
Proof.
split.
- intros.
  rewrite <- not_VecIncluded_iff_VecNotIncluded.
  intro. 
  contradiction.
- intros.
  rewrite <- not_VecIncluded_iff_VecNotIncluded in H.
  apply VecIncluded_iff_VecIncludedBool.
  rewrite <- VecIncluded_iff_VecIncludedBool in H.
  rewrite not_true_iff_false in H.
  apply not_false_iff_true in H.
  assumption.
Qed.

Definition VecComparable {n} (a b: t nat n): Prop :=
  a c= b \/ b c= a.

Definition VecNotComparable {n} (a b: t nat n): Prop :=
  a c/= b /\ b c/= a.

Lemma VecComparable_iff_not_VecNotComparable {n} (a b: t _ n):
  VecComparable a b <-> ~ (VecNotComparable a b).
Proof.
split.
+ intro. unfold not.
  intro. unfold VecComparable in H. unfold VecNotComparable in H0.
  destruct H0.
  destruct H.
  - apply not_VecIncluded_iff_VecNotIncluded in H0. 
    contradiction.
  - apply not_VecIncluded_iff_VecNotIncluded in H1.
    contradiction H1.
+ intro. 
  unfold VecNotComparable in H.
  unfold VecComparable.
  rewrite not_VecIncluded_iff_VecNotIncluded_contra.
  rewrite not_VecIncluded_iff_VecNotIncluded_contra.
  rewrite -> VecNotIncluded_iff_VecNotIncludedBool in H. 
  rewrite -> VecNotIncluded_iff_VecNotIncludedBool in H.
  rewrite <- andb_true_iff in H.
  apply not_true_iff_false in H.
  apply andb_false_iff in H.
  rewrite VecNotIncluded_iff_VecNotIncludedBool.
  rewrite VecNotIncluded_iff_VecNotIncludedBool.
  rewrite not_true_iff_false.
  rewrite not_true_iff_false.
  assumption.
Qed.

(* Il faut définir les vecteurs symboliques *)



