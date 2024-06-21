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
split; trivial.
Qed.

Definition VecComparable {n} (a b: t nat n): Prop :=
  a c= b \/ b c= a.

Definition VecNotComparable {n} (a b: t nat n): Prop :=
  a c/= b /\ b c/= a.

Lemma VecComparable_iff_not_VecNotComparable {n} (a b: t _ n):
  VecComparable a b <-> ~ (VecNotComparable a b).
Proof.
(*ancienne preuve*)
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

Definition join2vec {n} (a b: t nat n) :=
  (map2 max a b).

(* Etude des ensembles *)
(* Pour le moment la structure des vecteurs semble complétement incompatible avec les options de la librairie standard pour faire des ensembles d'ordre partiel *)
(* Il est très difficile pour l'instant de savoir quoi faire *)

(* La solution en utilisant le module d'orderedtype semble plutot bien fonctionner si l'on veut décrire un ensemble muni d'un ordre partiel avec que des vecteurs de taille prédifini au moment de la création des modules *)

Require Import VectorEq.

Require Import Coq.Lists.ListSet.
Require Import Coq.Structures.Orders.

Module VecOrderedType <: MiniDecidableType.
  Definition t := list nat.
  Lemma eq_dec : forall (x y : t), {eq x y} + {~ eq x y}.
  Proof.
    unfold t.
    apply Coq.Lists.List.list_eq_dec.
    apply Nat.eq_dec.
  Qed.
End VecOrderedType.

Check set_add.
Check set_add VectorEq.eq_dec (Vector.t nat 3) .

Check Init.Datatypes.list.
Check Init.Datatypes.list (Vector.t nat 3).



(*Require Import Coq.Structures.OrderedTypeEx.
*)
Require Import Coq.MSets.MSetWeakList.




Module VecSet := MSetWeakList.Make(Vec_UDT).
Check VecSet.mem .
Check VecSet.elt.
Compute VecSet.elt.

Notation "{}" := (VecSet.empty).
Notation "{ x1 , .. , xn }" :=
  (VecSet.add x1 .. (VecSet.add xn {}) .. ).
Check List.cons.
Check List.cons 2 List.nil.
Check VecSet.add.
VecSet.add (List.cons 2 List.nil) VecSet.empty.

Check {}.
Check {[1;2]}.
Check {[1; 2], [2; 1]}.


Module VectorOrderedType <: UsualOrderedType.
  (* Define the type of vectors *)
  Definition t {n} := Vector.t nat n.

  Definition eq {n} := @eq (t n).

  (* Define equality on vectors 
  Definition eq {n} (v1 v2 : t nat n) : Prop := v1 = v2. 
*)
  Definition eq_refl {n} := @eq_refl (t nat n).

  Definition eq_sym {n} := @eq_sym (t nat n).

  Definition eq_trans {n} := @eq_trans (t nat n).

  Definition lt {n} (x y: t nat n) := x c= y.

  Lemma lt_trans {n} (x y z : t nat n):
    x c= y -> y c= z -> x c= z.
  Proof.
  intros.
  dependent induction y.
  - (* init *)
    assert (x=[] /\ z=[]). { split; apply nil_spec. }
    destruct H1. rewrite H1. rewrite H1 in H.
    assumption.
  - (* induction *)
    assert (x=(hd x :: tl x) /\ z=(hd z :: tl z)). { split; apply eta. }
    destruct H1. rewrite H1, H2.
    apply Forall2_cons.
    + rewrite H1 in H; rewrite H2 in H0.
      apply forall2_arbitrary_hd in H, H0.
      apply Nat.le_trans with (m:=h); assumption; assumption.
    + apply IHy with (y0:=y). trivial. trivial. 
      rewrite H1 in H; apply forall2_arbitrary_tl in H; assumption.
      rewrite H2 in H0; apply forall2_arbitrary_tl in H0; assumption.
  Qed.

End VectorOrderedType.

  Lemma 
  (* Proof for the case of an empty vector *)
Lemma eq_refl_nil : forall (v : t nat 0), eq v v.
Proof.
  intros v.
  unfold eq.
  trivial.
Qed.
(* Proof for the case of a non-empty vector *)
Lemma eq_refl_cons : forall {n} (x : nat) (xs : t nat n), eq (x :: xs) (x :: xs).
Proof.
  intros n x xs.
  unfold eq.
  trivial.
Qed.

Lemma eq_refl_proof {n} (v: t nat n):
  eq v v.
Proof.
unfold eq.
trivial.
Qed.

  (* Reflexivity of equality *)
  Definition eq_refl {n} : forall (v : t nat n), eq v v :=
    fun v => eq_refl_proof v.
      (*match v with
      | Vector.nil _ => eq_refl_nil _ (* Proof that an empty vector is equal to itself *)
      | x :: xs => eq_refl_cons x xs (* Proof that a non-empty vector is equal to itself *)
      end.*)

Lemma eq_symmetry_proof {n} (x y: t nat n):
  eq x y -> eq y x.
Proof.
unfold eq. 
intros.
rewrite H.
trivial.
Qed.


  (* Symmetry of equality *)
  Definition eq_sym {n} : forall x y : t nat n, eq x y -> eq y x :=
    fun v => eq_symmetry_proof v.

Lemma eq_trans_proof {n} (x y z: t nat n):
  eq x y -> eq y z -> eq x z.
Proof.
unfold eq.
intros.
rewrite H.
assumption.
Qed.

  (* Transitivity of equality *)
  Definition eq_trans {n} : forall x y z : t nat n, eq x y -> eq y z -> eq x z :=
    fun v1 => fun v2 => fun v3 => eq_trans_proof v1 v2 v3.

  (* Define comparison function on vectors *)
  Definition compare (v1 v2 : t) : comparison :=
    ___.

  (* Define less-than relation on vectors *)
  Definition lt (v1 v2 : t) : Prop :=
    ___.

  (* Decidability of equality *)
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} :=
    ___.

End VectorOrderedType.



Make Vector.

Require Import Ensembles.



Search max.
Check max 1 2.
Compute max 1 2.

Compute join2vec [1; 2; 1] [2; 1; 32].

Check [[1; 2]; [2; 1]].

Definition join set :=
  match set with
  | nil => 
  | x :: rest => join2vec x (join rest)
  end.

Definition join 

(* Il faut définir les vecteurs symboliques *)



