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

(*Notation "v1 c=? v2" := (fold_left andb true (map2 (Nat.leb) v1 v2)) (at level 50, left associativity).
*)

Definition VecsToBoolVec {n} Rb (a b: t nat n): Bvector n :=
  map2 Rb a b.

Check VecsToBoolVec Nat.leb [23;3] [1;2].
Compute VecsToBoolVec Nat.leb [23;3] [1;2].
Check VecsToBoolVec Nat.leb [1;5] [2;4].
Compute VecsToBoolVec Nat.leb [1;5] [2;4].

Check fold_right andb (VecsToBoolVec Nat.leb [1;5] [2;4]) true.
Compute fold_right andb (VecsToBoolVec Nat.leb [1;5] [2;4]) true.

Notation "v1 c=? v2" := (fold_right andb (VecsToBoolVec Nat.leb v1 v2) true) (at level 50, left associativity). 

Check [23;3] c=? [1;2].
Compute [23;3] c=? [1;2].
Check [1;2] c=? [2;4].
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
    Search (_ && _). 
    rewrite andb_diag. 
    assumption.
+ intros.
  destruct H.
  simpl.
  Search andb.
  apply andb_true_iff.
  split; assumption.
Qed.

Search (~(_ = true)).

Lemma VecIncluded_iff_VecIncludedBool {n} (a b: t nat n):
   a c=? b = true <-> a c= b.
Proof.
split.
- intros.
  dependent induction n.
  + (* init *) 
    assert (a=[]/\b=[]). { split; apply nil_spec. }
    destruct H0. rewrite H0, H1. compute. apply Forall2_nil.
  + (* induction *)
    assert (a = (hd a :: tl a) /\ b = (hd b :: tl b)). { split; apply eta. }
    destruct H0. rewrite H0, H1.
    rewrite H0, H1 in H.
    apply VecIncludedBool_iff_head_tail in H. destruct H.
    apply Forall2_cons.
    ++  Search (_ <=? _). apply leb_complete. assumption.
    ++  apply IHn in H2.
        unfold "c=" in H2.
        assumption.
- intros.
  dependent induction H. compute; trivial.
  apply VecIncludedBool_iff_head_tail.
  split.
  + Search leb. apply leb_correct. assumption.
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
split.
- intros.
  unfold VecNotIncludedBool in H.
  inversion H.
  Search (_ || _ = true). apply orb_true_iff in H1.
  destruct H1. 
  rewrite H0. left. compute. reflexivity.
  right. rewrite H0. Search (_ || true). rewrite orb_true_r. unfold VecNotIncludedBool. assumption.
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
    Search (_ <? _). apply Nat.ltb_lt. assumption.
  + (* induction *)
    apply VecNotIncludedBool_iff_head_tail. right.
    assumption.
- intros.
  dependent induction n.
  + (* init *)
    assert (a=[] /\ b=[]). { split; apply nil_spec. }
    destruct H0. rewrite H0, H1 in H. compute in H.
    unfold "c/=". Search (_ = _ -> False).
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
        apply IHn. assumption.
Qed.

Lemma VecNotIncludedBool_iff_VecIncludedBool_false {n} (a b: t nat (S n)):
  a c/=? b = true <-> a c=? b = false.
Proof.
split.
- intros.
  assert (a=(hd a :: tl a) /\ b=(hd b :: tl b)). { split; apply eta. }
  destruct H0.
  dependent induction n.
  + (* init *)
    rewrite H0, H1 in H. unfold VecNotIncludedBool in H. simpl in H.
    apply orb_true_iff in H.
    destruct H.
    ++  apply Nat.ltb_lt in H.
        rewrite H0, H1.
        simpl.
        apply andb_false_iff.
        left. apply leb_iff_conv.
        assumption.
    ++  assert (tl a = [] /\ tl b = []). { split; apply nil_spec. }
        destruct H2.
        rewrite H2, H3 in H.
        compute in H.
        rewrite H0, H1. 
        simpl.
        apply andb_false_iff.
        right.
        rewrite H2, H3. 
        compute.
        symmetry. assumption.
  + (* induction *)
    rewrite H0, H1.
    simpl.
    apply andb_false_iff. 
    rewrite H0, H1 in H.
    apply VecNotIncludedBool_iff_head_tail in H.
    destruct H.
    ++  left.
        Search (_ <=? _ = false). apply leb_iff_conv.
        Search (_ <? _ = true). apply Nat.ltb_lt in H.
        assumption.
    ++  right.
        apply IHn.
        assumption.
        apply eta.
        apply eta.
- intros.
  assert (a=(hd a :: tl a) /\ b=(hd b :: tl b)). { split; apply eta. }
  destruct H0.
  induction n.
  + (* init *)
    assert (tl a = [] /\ tl b = []). { split; apply nil_spec. }
    destruct H2.
    rewrite H0, H1. rewrite H0, H1 in H.
    rewrite H2, H3 in H. rewrite H2, H3.
    simpl in H. Search (_ && _ = false). apply andb_false_iff in H. 
    unfold VecNotIncludedBool. simpl.
    Search (_ || _ = true). rewrite orb_true_iff.
    destruct H.
    ++  left. apply leb_iff_conv in H. apply Nat.ltb_lt.
        assumption.
    ++  right. auto. (* pour symmetry; assumption. *)
  + (* induction *)
    rewrite H0, H1.
    apply VecNotIncludedBool_iff_head_tail.
    rewrite H0, H1 in H. simpl in H. apply andb_false_iff in H.
    destruct H.
    ++  left. apply leb_iff_conv in H. apply Nat.ltb_lt. assumption.
    ++  right.
        apply IHn.
        assumption.
        apply eta. apply eta.
Qed.

Lemma vec_eq_impl_incl: forall {n} (a b: t nat n), a = b -> a c= b. 
intros. compute.
rewrite <- H.
apply Forall2_nth. intros.
trivial.
Qed. 

Lemma vec_inclusion_antisymm: forall {n} (a b: t nat n), a c= b /\ b c= a <-> a = b.
split ; intros.
- compute in H. destruct H as [H0 H1].
  dependent induction H0. reflexivity.
  assert (x2<=x1). {
  apply (forall2_hd) in H1; trivial. }
  assert (x1=x2). {
  apply Nat.le_antisymm; assumption. }
  apply forall2_tl in H1. apply IHForall2 in H1.
  rewrite H1; rewrite H3. reflexivity.
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
dependent induction H0.
apply forall2_hd in H.
contradiction H.
Qed.

Lemma forall2_iff_neg_forall2_neg_relation {n A} R (a b: t A (S n)):
  Forall2 R a b -> ~(Forall2 (fun x y => ~ R x y) a b).
Proof.
intros. intro.
dependent induction H0.
contradiction H1.
apply forall2_hd in H.
assumption.
Qed.



Lemma not_VecIncluded_iff_VecNotIncluded {n} (a b: t nat (S n)):
  ~(a c= b) <-> a c/= b.
Proof.
intros.
split; intros.
- apply VecNotIncluded_iff_VecNotIncludedBool.
  apply VecNotIncludedBool_iff_VecIncludedBool_false.
  rewrite <- VecIncluded_iff_VecIncludedBool in H.
  Search (~(_=true)).
  apply not_true_is_false.
  assumption.
- rewrite <- VecIncluded_iff_VecIncludedBool.
  Search (_ <> true).
  apply not_true_iff_false.
  Search (_ c=? _).
  apply VecNotIncludedBool_iff_VecIncludedBool_false.
  Search (_ c/= _).
  apply VecNotIncluded_iff_VecNotIncludedBool.  
  assumption.
Qed.

Lemma not_VecIncluded_iff_VecNotIncluded_contra {n} (a b: t _ (S n)):
  a c= b <-> ~(a c/= b).
Proof.
Search (~_ <-> ~_).
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

Lemma VecComparable_iff_not_VecNotComparable {n} (a b: t _ (S n)):
  VecComparable a b <-> ~ (VecNotComparable a b).
Proof.
split.
+ intro. unfold not.
  intro. unfold VecComparable in H. unfold VecNotComparable in H0.
  destruct H0.
  destruct H.
  - apply not_VecIncluded_iff_VecNotIncluded in H0. unfold not in H0. 
    contradiction H0.
  - apply not_VecIncluded_iff_VecNotIncluded in H1. unfold not in H1.
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

Search "contra".

(* Il faut définir les vecteurs symboliques *)



