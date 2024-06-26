Require Import Nat Vector Bvector Logic Equality.
Require Import Coq.Arith.Arith.
Require Import Eqdep_dec.

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
intros H.
inversion H.
apply Eqdep.EqdepTheory.inj_pair2 in H2,H5.
subst.
assumption.
Qed.

Lemma forall2_hd_tl {n A} R (a b: t A (S n)):
  Forall2 R a b <-> (R (hd a) (hd b) /\  Forall2 R (tl a) (tl b)).
Proof.
intros.
assert (a = (hd a:: tl a) /\ b = (hd b:: tl b)). { split; apply eta. }
destruct H.
split.
- intros.
  rewrite H, H0 in H1.
  split.
  + apply forall2_hd.
    assumption.
  + apply forall2_tl.
    assumption.
- intros.
  destruct H1.
  rewrite H, H0.
  apply Forall2_cons; assumption.
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
inversion H.
apply Eqdep.EqdepTheory.inj_pair2 in H2,H5 ; subst.
assumption.
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
  induction n.
  + (* init *) 
    assert (a=[] /\ b=[]). { split; apply nil_spec. }
    destruct H0; rewrite H0, H1. 
    apply Forall2_nil.
  + (* induction *)
    assert (a = (hd a :: tl a) /\ b = (hd b :: tl b)). { split; apply eta. }
    destruct H0; rewrite H0, H1.
    rewrite H0, H1 in H.
    apply VecIncludedBool_iff_head_tail in H. destruct H.
    apply Forall2_cons.
    ++  apply leb_complete. 
        assumption.
    ++  apply IHn in H2.
        unfold "c=" in H2.
        assumption.
- intros.
  induction H.
  compute; trivial.
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

Lemma vec_inclusion_antisymm: forall {n} (a b: t nat n), 
  a c= b /\ b c= a <-> a = b.
Proof.
split ; intros.
- compute in H. 
  destruct H as [H0 H1].
  induction H0.
  + (* init *)
    reflexivity.
  + (* induction *)
    apply forall2_arbitrary_hd_tl in H1; destruct H1.
    assert (x1=x2). { apply Nat.le_antisymm; assumption. }
    apply IHForall2 in H2.
    subst; reflexivity.
- induction H.
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
rewrite <- VecIncluded_iff_VecIncludedBool.
rewrite VecNotIncluded_iff_VecNotIncludedBool.
rewrite not_true_iff_false.
apply iff_sym.
apply VecNotIncludedBool_iff_VecIncludedBool_false.
Qed.

Lemma not_VecIncluded_iff_VecNotIncluded_contra {n} (a b: t _ n):
  a c= b <-> ~(a c/= b).
Proof.
rewrite <- not_VecIncluded_iff_VecNotIncluded.
rewrite <- VecIncluded_iff_VecIncludedBool.
rewrite not_true_iff_false.
rewrite not_false_iff_true.
reflexivity.
Qed.

Lemma VecIncluded_TiersExclu {n} (a b: t nat n):
  a c= b \/ a c/= b.
Proof.
rewrite VecNotIncluded_iff_VecNotIncludedBool.
rewrite <- VecIncluded_iff_VecIncludedBool.
rewrite -> VecNotIncludedBool_iff_VecIncludedBool_false.
destruct (a c=? b); auto.
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
  destruct H; apply not_VecIncluded_iff_VecNotIncluded in H0, H1; contradiction.
+ intro. unfold VecNotComparable in H.
  assert (a c/=? b = false \/ b c/=? a = false). {  
  apply andb_false_iff.
  apply not_true_iff_false.
  rewrite andb_true_iff.
  repeat rewrite <- VecNotIncluded_iff_VecNotIncludedBool.
  assumption.
  }
  unfold VecComparable.
  repeat rewrite not_VecIncluded_iff_VecNotIncluded_contra.
  repeat rewrite VecNotIncluded_iff_VecNotIncludedBool.
  repeat rewrite not_true_iff_false.
  assumption.
Qed.

Lemma VecIncluded_impl_VecNotIncludedInversed {n} (a b: t nat (S n)):
  (a <> b) -> (a c= b) -> b c/= a.
Proof.
intros.
apply not_VecIncluded_iff_VecNotIncluded.
intro.
unfold not in H; destruct H.
apply vec_inclusion_antisymm.
split; assumption.
Qed.

Lemma VecComparable_and_NotIncluded_impl_IncludedInversed {n} (a b: t nat n):
  VecComparable a b -> (a c/= b) -> b c= a.
Proof.
intros. 
unfold VecComparable in H.
destruct H.
- apply not_VecIncluded_iff_VecNotIncluded in H0.
  contradiction H0.
- assumption.
Qed.

Definition join2vec {n} (a b: t nat n) :=
  (map2 max a b).