(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower qexamples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section transpose.

Variables (R : comRingType).
Let I := [finType of 'I_2].
Let dI : I := ord0.

Notation tsquare m := (tmatrix I R m m).
Notation endo n := (mor I R n n).

Definition transpose m (M : tsquare m) : tsquare m :=
  [ffun vi => [ffun vj => M vj vi]].

Notation focus := (focus dI).
Notation curry := (curry dI).

Definition curry0 (L : lmodType R) (v : L) : tpower I 0 L := [ffun _ => v].
Definition curryn0 n (L : lmodType R) (v : tpower I n L)
  : tpower I n (tpower I 0 L) := [ffun vi => [ffun _ => v vi]].
Definition uncurry0 (L : lmodType R) (v : tpower I 0 L) : L :=
  v [tuple of nil].

Lemma curry0_is_linear T : linear (@curry0 T).
Proof. move=> x y z. apply/ffunP => vi. by rewrite !ffunE. Qed.
Lemma uncurry0_is_linear T : linear (@uncurry0 T).
Proof. move=> x y z. by rewrite /uncurry0 !ffunE. Qed.

Definition cap_fun n (l : lens n 2) : morfun I R n (n-2) :=
  fun T : lmodType R =>
    uncurry0 (L:=_) \o
    tsmor (curry0 (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
    curry l (T:=T).

Definition cup_fun n (l : lens n 2) : morfun I R (n-2) n :=
  fun T : lmodType R =>
    uncurry l \o
    tsmor (curryn0 (uncurry (lens_left 1 1) (id_tsquare I R 1))) _ \o
    curry0 (L:=_).

Lemma cap_is_linear n l T : linear (@cap_fun n l T).
Proof.
move=> x y z.
by rewrite /cap_fun /= curry_is_linear tsmor_is_linear uncurry0_is_linear.
Qed.

Lemma cup_is_linear n l T : linear (@cup_fun n l T).
Proof.
move=> x y z.
by rewrite /cup_fun /= curry0_is_linear tsmor_is_linear uncurry_is_linear.
Qed.

Definition cap n l : mor I R n (n-2) :=
  fun T : lmodType R => Linear (@cap_is_linear n l T).
Definition cup n l : mor I R (n-2) n :=
  fun T : lmodType R => Linear (@cup_is_linear n l T).

Lemma sum_scaler_cond A (L : lmodType R)(r : seq A)(P Q : pred A)(F : A -> L) :
  (\sum_(i <- r | P i) (Q i)%:R *: F i = \sum_(i <- r | P i && Q i) F i)%R.
Proof.
rewrite big_mkcondr /=; apply eq_bigr => i _.
case: ifP; by rewrite (scale1r,scale0r).
Qed.

Lemma transpose_cup (M : tsquare 1) :
  focus ([lens 0] : lens 2 1) (tsmor M) \v cup [lens 0; 1] =e
  focus ([lens 1] : lens 2 1) (tsmor (transpose M)) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /cup_fun !focusE /= !ffunE.
rewrite !sum_ffunE.
do ! rewrite sum_enum_indices /= addr0.
rewrite !ffunE.
rewrite !sum_ffunE.
do ! rewrite sum_enum_indices /= addr0.
rewrite !ffunE.
rewrite (_ : [lens 0; 1] = lens_id 2); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= enum_ordinalE.
rewrite !extract_lens_id.
rewrite (_ : lens_left 1 1 = [lens 0]); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= enum_ordinalE.
rewrite !extract_merge.
rewrite !extract_lothers_merge.
rewrite [in X in extract X _ == _](_ : [lens 0] = lothers [lens 1]); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE.
rewrite !(extract_lothers_merge _ [lens 1]).
rewrite (_ : lothers [lens 0] = [lens 1]); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE.
rewrite !extract_merge.
rewrite (_ : lothers (lens_id 2) = @mkLens _ _ [tuple of [::]] erefl); last first.
  apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE /=.
  rewrite !ifF//.
    apply/negbTE; rewrite negbK.
    by rewrite -topredE /= enum_ordinalE.
  apply/negbTE; rewrite negbK.
  by rewrite -topredE /= enum_ordinalE.
rewrite /=.
rewrite (_ : lothers [lens 1] = [lens 0]); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE.
rewrite (_ : [lens 0] = lothers [lens 1]); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE.
rewrite !(extract_lothers_merge _ [lens 1]).
rewrite {3}/extract /=.
rewrite {6}/extract /=.
rewrite {9}/extract /=.
rewrite {12}/extract /=.
rewrite (_ : lothers [lens 1] = [lens 0]); last first.
  by apply/val_inj/eqP; rewrite eq_ord_tuple /= /others /= enum_ordinalE.
have [vi0|vi0] := eqVneq (extract [lens 1] vi) [tuple 0%O].
  rewrite scale1r vi0 /= scale0r /= scaler0 addr0 /=.
  have [vi1|vi1] := eqVneq (extract [lens 0] vi) [tuple 0%O].
    rewrite scale1r vi1 /= scale0r scaler0 addr0.
    by congr (_ _ (v _)); exact/val_inj.
  rewrite scale0r scaler0 add0r.
  have [vi2|vi2] := eqVneq (extract [lens 0] vi) [tuple 1%:O].
    rewrite /= vi2 scale1r.
    by congr (_ _ (v _)); exact/val_inj.
  rewrite scale0r scaler0.
  exfalso.
  move: vi1 vi2.
  by case: (extract _ vi) => -[//|] [] [|[|]]// h [|//] H.
rewrite scale0r scaler0 add0r.
have [vi1|vi1] := eqVneq (extract [lens 1] vi) [tuple 1%:O].
  rewrite scale1r vi1 /=.
  have [vi2|vi2] := eqVneq (extract [lens 0] vi) [tuple 0%:O].
    rewrite scale1r vi2 /= scale0r scaler0 addr0.
    by congr (_ _ (v _)); exact/val_inj.
  rewrite !linE. (* TODO: add scaler0 to linE *)
  rewrite scaler0 add0r.
  have [vi3|vi3] := eqVneq (extract [lens 0] vi) [tuple 1%:O].
    rewrite /= scale1r vi3.
    by congr (_ _ (v _)); exact/val_inj.
  exfalso.
  move: vi2 vi3.
  by case: (extract _ vi) => -[//|] [] [|[|]]// h [|//] H.
exfalso.
move: vi0 vi1.
by case: (extract _ vi) => -[//|] [] [|[|]]// h [|//] H.
Qed.

Lemma transpose_focus (M : tsquare 1) :
  tsmor (transpose M) =e
  cap [lens 1; 2] \v focus [lens 1] (tsmor M) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /cap_fun /cup_fun !ffunE /uncurry0 /curry0 /= !ffunE sum_ffunE.
under eq_bigr do rewrite ffunE.
symmetry.
under eq_bigr do rewrite !ffunE.
rewrite sum_scaler_cond /=.
rewrite
  (reindex_onto (fun v => [tuple tnth v ord0; tnth v ord0]) (fun v : 2.-tuple _ => [tuple tnth v ord0])) /=;
  last first.
  move=> vj.
  rewrite eq_tuple /= => /eqP.
  rewrite /others /lens_left !enum_ordinalE /= -!topredE /= !enum_ordinalE /=.
  case => H1.
  apply eq_from_tnth => -[] [|[]] // Hi; rewrite (tnth_nth (tnth vj ord0)) /=;
    rewrite (tnth_nth (tnth vj ord0)) /=.
  - rewrite /=. congr tnth. exact: val_inj.
  - have {1}-> : ord0 = lshift 1 ord0 :> 'I_(1+1) by apply: val_inj.
    rewrite H1; congr tnth; exact: val_inj.
apply eq_big => vj.
  apply/andP; split.
  - rewrite eq_tuple; apply/eqP.
    rewrite /= /others /lens_left !enum_ordinalE /=.
    by rewrite -!topredE /= !enum_ordinalE.
  - apply/eqP/eq_from_tnth => j.
    by rewrite !ord1 (tnth_nth (tnth vj ord0)) /= (tnth_nth (tnth vj ord0)).
move=> _.
rewrite focusE /=.
rewrite !ffunE.
rewrite sum_enum_indices /=.
have {1 3}-> : [lens 1] = lens_comp [lens 1;2] [lens 0].
  move=> n. apply/val_inj/eq_from_tnth => i /=.
  by rewrite ord1 (tnth_nth ord0) ![RHS](tnth_nth ord0).
rewrite extract_comp extract_merge addr0.
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

End transpose.
