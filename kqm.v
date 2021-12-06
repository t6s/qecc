(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower qexamples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section transpose.

Variables (n : nat) (R : comRingType) (L : lmodType R) (I : finType) (dI : I).

Notation tsquare m := (tmatrix I R m m).

Definition transpose m (M : tsquare m) : tsquare m :=
  [ffun vi => [ffun vj => M vj vi]].

Notation focus := (focus dI).
Notation curry := (curry dI).

Lemma transpose_focus (M : tsquare 1) T :
  tsmor (transpose M) T =1
  uncurry (lens_left 0 1) \o
  tsmor (curry (lens_left 0 2) (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
  curry (lens_right 1 2) \o
  focus [lens (1%:O : 'I_3)] (tsmor M) _ \o
  uncurry (lens_left 2 1) \o
  tsmor (curry (lens_left 2 0) (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
  curry (lens_left 0 1).
Proof.
move=> v /=.
apply/ffunP => vi /=.
rewrite !ffunE /= sum_ffunE.
Abort.
