(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section transpose.

Variables (R : comRingType) (L : lmodType R) (I : finType) (dI : I).

Notation tsquare m := (tmatrix I R m m).

Definition transpose m (M : tsquare m) : tsquare m :=
  [ffun vi => [ffun vj => M vj vi]].

Notation focus := (focus dI).
Notation curry := (curry dI).

Definition curry0 (L : lmodType R) (v : L) : tpower I 0 L := [ffun _ => v].
Definition curryn0 n (L : lmodType R) (v : tpower I n L)
  : tpower I n (tpower I 0 L) := [ffun vi => [ffun _ => v vi]].
Definition uncurry0 (L : lmodType R) (v : tpower I 0 L) : L :=
  v [tuple of nil].

Definition cap n (l : lens n 2) : morfun I R n (n-2) :=
  fun T : lmodType R =>
    uncurry0 (L:=_) \o
    tsmor (curry0 (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
    curry l (T:=T).

Definition cup n (l : lens n 2) : morfun I R (n-2) n :=
  fun T : lmodType R =>
    uncurry l \o
    tsmor (curryn0 (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
    curry0 (L:=_).

Lemma transpose_focus (M : tsquare 1) T :
  tsmor (transpose M) T =1
  cap [lens 1; 2] (T:=_) \o
  focus [lens 1] (tsmor M) _ \o
  cup [lens 0; 1] (T:=_).
Proof.
move=> v /=.
apply/ffunP => vi /=.
Abort.

Definition id_tsquare' n : tpower I n (tpower I (n + n - n) R^o).
rewrite addKn.
exact (id_tsquare I R n).
Defined.

(*
Lemma transpose_focus n (M : tsquare n) T :
  tsmor (transpose M) T =1
  uncurry (lens_left 0 n) \o
  tsmor (curry0 (uncurry (lens_left n n) (id_tsquare I R n))) _ \o
  @curry0 _ \o
  focus (lens_right n (n+n)) (focus (lens_left n n) (tsmor M)) _ \o
  uncurry (lens_left (n+n) n) \o
  tsmor (curry (lens_left (n+n) 0) (uncurry (lens_left n n) (id_tsquare I R n))) _ \o
  curry (lens_left 0 n).
Proof.
move=> v /=.
apply/ffunP => vi /=.
rewrite !ffunE /= sum_ffunE.
Abort.
*)
