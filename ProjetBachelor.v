From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Check [tuple 1;2].
Compute [tuple 1;2] == [tuple 2;3].
Compute thead [tuple 2;3].
Check [tnth [tuple 2;3] 1].
Compute [tnth [tuple 2;3] 0].

Check tnth [tuple 2;3;4].

Definition allones (s : seq nat) : Prop :=
  all (fun x => x == 1) s.

Lemma akjfdlkdsa : allones [tuple 1;1;1;1].
rewrite /allones /=. trivial.
Qed.

Definition VecIncluded {n} (a b: n.-tuple _): Prop :=
  all (fun '(x, y) => x <= y) (zip a b).

Notation "v1 c= v2" := (VecIncluded v1 v2) (at level 50, left associativity).

Check VecIncluded [::1;2] [::2;3].
Compute [::1;2] c= [tuple 2;3].

Lemma sadf: [tuple 34;100;2] c= [tuple 209; 349;90].
compute. trivial.
Qed.

Lemma vec_eq_impl_incl: forall {n} (a b: n.-tuple _), a = b -> a c= b.
intros.
rewrite H.
apply /allP.
apply /allP. intros [x y] H_in.
case in H_in.
