(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens dpower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section transpose.

Variables (R : comRingType).
Let I : finType := 'I_2.
Let dI : I := ord0.

Notation idmor n := (idmor I R n).
Notation dpsquare m := (dpmatrix I R m m).
Notation endo n := (mor I R n n).

Notation focus := (focus dI).
Notation curry := (curry dI).

Local Definition sum_enum_indices := sum_enum_indices uniq_enum2 mem_enum2.
Local Definition mem_enum_indices := mem_enum_indices mem_enum2.
Local Definition forall_indicesP := forall_indicesP mem_enum2.

Section cap_cup.
Variables (n : nat) (l : lens (2 + n) 2).

Definition cap :=
  asym_focus dI (p:=0) l (lens_empty n) (inner_prod I R 1).
Definition cup :=
  asym_focus dI (m:=0) (lens_empty n) l (inner_coprod I R 1).
End cap_cup.

Lemma extract_rev A n m (l1 l2 : lens n m) (v : n.-tuple A) :
  rev l1 = l2 -> [tuple of rev (extract l1 v)] = extract l2 v.
Proof. by move=> Hrev; apply/val_inj; rewrite /= -map_rev Hrev. Qed.

Lemma lens_left_1 n : lens_left 1 n = [lens 0].
Proof. by eq_lens. Qed.

Lemma lens_right_1 n : lens_right n 1 = [lens n].
Proof. by eq_lens; rewrite /= addnOK. Qed.

Lemma lens_comp_rev_left n (l1 l2 : lens (2+n) 2) : rev l1 = l2 ->
  lens_comp l1 (lens_left 1 1) = lens_comp l2 (lensC(lens_left 1 1)).
Proof.
move=> Hrev; apply/lens_inj => /=.
move: (lensC_left 1 1) => /= ->.
by rewrite !enum_ordinalE /= !(tnth_nth ord0) /= -Hrev nth_rev // size_tuple.
Qed.

Lemma cup_sym n (l1 l2 : lens (2+n) 2) :
  rev l1 = l2 -> cup l1 =e cup l2.
Proof.
move=> Hrev T v.
apply/ffunP => vi.
rewrite !(ffunE,dpmorE) !cast_tupleE !(big_pred1 [tuple]); try by case => -[].
rewrite !ffunE -!extract_comp.
rewrite -(lens_comp_rev_left Hrev) -(lens_comp_rev_left (l1:=l2) (l2:=l1));
  last by rewrite -Hrev revK.
rewrite [in RHS]eq_sym.
Abort.
(*
case H: (_ == _); last by rewrite !scale0r.
rewrite !scale1r !merge_empty.
do 3!f_equal.
apply/lens_inj/eq_filter => /= i.
by rewrite !mem_lensE /= -Hrev mem_rev.
Qed.
*)

Lemma transpose_cup (M : dpsquare 1) :
  focus [lens 0] (dpmor M) \v cup (n:=1) [lens 0; 1] =e
  focus [lens 1] (dpmor (dptranspose M)) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /asym_focus_fun !focusE /=.
do! rewrite !(dpmorE,ffunE,sum_ffunE,sum_enum_indices) /= !addr0 !ffunE.
rewrite !lens_left_1.
have -> : lensC [lens 0] = [lens 1] by eq_lens.
rewrite !cast_tupleE /= -!extract_comp.
have -> : lens_comp [lens 0; 1] [lens 0] = [lens 0] :> lens 3 1 by eq_lens.
have -> : lens_comp [lens 0; 1] [lens 1] = [lens 1] :> lens 3 1 by eq_lens.
rewrite !extract_merge !merge_empty /= !extract_merge_disjoint.
rewrite !scalerA -!scalerDl.
f_equal.
have := mem_enum_indices (extract [lens 0] vi).
have := mem_enum_indices (extract [lens 1] vi).
by rewrite !inE => /orP[] /eqP -> /orP[] /eqP -> /=;
   rewrite !(mulr0,addr0,add0r).
all: by rewrite disjoint_has //= /seq_lensC enum_ordinalE.
Qed.

Lemma cat_2tuple A (x y : A) : [tuple of [tuple x]++[tuple y]] =  [tuple x; y].
Proof. exact/val_inj. Qed.

Lemma straighten : cap [lens 1; 2] \v cup [lens 0; 1] =e idmor 1.
Proof.
move=> T /= v.
rewrite /asym_focus_fun.
apply/ffunP => t /=.
rewrite /inner_prod /inner_coprod /M_inner_prod /M_inner_coprod.
rewrite {1}/uncurry !ffunE /= !dpmorE sum_enum_indices /= !ffunE /=.
rewrite -!cat_2tuple !extract_lens_left.
rewrite !(extract_eq_cast (lensC_left 1 1)) !extract_lens_right /= !linE.
rewrite !dpmorE !sum_enum_indices /= !ffunE /= !addr0.
apply/eqP; move: t; apply/forall_indicesP.
rewrite /= andbT; apply/andP.
(* brute force *)
rewrite !eq_ord_tuple /= /tnth /= /tnth /= /seq_lensC.
rewrite /in_mem /mem /= !enum_ordinalE /= !linE.
split; apply/eqP/f_equal/eqP;
  by rewrite eq_ord_tuple /= /tnth /= /seq_lensC !enum_ordinalE.
Qed.

Lemma transpose_focus (M : dpsquare 1) :
  dpmor (dptranspose M) =e
  cap [lens 1; 2] \v focus [lens 1] (dpmor M) \v cup [lens 0; 1].
Proof.
rewrite -{2}(dptransposeK M).
move=> T v.
rewrite -comp_morA comp_morE comp_morE.
move: (transpose_cup (dptranspose M) v) => /= <-.
set mycup := asym_focus_fun dI ([lens] : lens (0+1) 0)
                  ([lens 0; 1] : lens (2+1) 2) (inner_coprod I R 1) v.
move: (asym_focusC dI ([lens 1; 2] : lens (2+1) 2) ([lens] : lens (0+1) 0)
                   (inner_prod I R 1) (dpmor (dptranspose M)) mycup).
rewrite !cast_lensE.
have -> : lensC [lens 1; 2] = [lens 0] by eq_lens.
move=> /= <-.
subst mycup.
move: (straighten v) => /= ->.
have <- : lens_id 1 = lensC [lens] by eq_lens.
by rewrite (focusI dI (dpmor (dptranspose M)) v).
Qed.
End transpose.
