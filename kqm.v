(* Kindergarten quantum mechanics *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens tpower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section transpose.

Variables (R : comRingType).
Let I := [finType of 'I_2].
Let dI : I := ord0.

Notation idmor n := (idmor I n).
Notation tsquare m := (tmatrix I R m m).
Notation endo n := (mor I R n n).

Notation focus := (focus dI).
Notation curry := (curry dI).

Local Definition sum_enum_indices := sum_enum_indices uniq_enum2 mem_enum2.
Local Definition mem_enum_indices := mem_enum_indices mem_enum2.
Local Definition forall_indicesP := forall_indicesP mem_enum2.

Section cap_cup.
Variables (n : nat) (l : lens (2 + n) 2).

Definition cap :=
  asym_focus dI (R:=R) (p:=0) l (lens_empty n) (inner_prod I 1).
Definition cup :=
  asym_focus dI (R:=R) (m:=0) (lens_empty n) l (inner_coprod I 1).
End cap_cup.

Lemma extract_rev A n m (l1 l2 : lens n m) (v : n.-tuple A) :
  rev l1 = l2 -> [tuple of rev (extract l1 v)] = extract l2 v.
Proof. by move=> Hrev; apply/val_inj; rewrite /= -map_rev Hrev. Qed.

Lemma lens_left_1 n : lens_left 1 n = [lens 0].
Proof. by eq_lens. Qed.

Lemma lens_right_1 n : lens_right n 1 = [lens n].
Proof. by eq_lens; rewrite /= addnOK. Qed.

Lemma lens_comp_rev_left n (l1 l2 : lens (2+n) 2) : rev l1 = l2 ->
  lens_comp l1 (lens_left 1 1) = lens_comp l2 (lothers(lens_left 1 1)).
Proof.
move=> Hrev; apply/val_inj/val_inj => /=.
move: (lothers_left 1 1) => /= ->.
by rewrite !enum_ordinalE /= !(tnth_nth ord0) /= -Hrev nth_rev // size_tuple.
Qed.

Lemma cup_sym n (l1 l2 : lens (2+n) 2) :
  rev l1 = l2 -> cup l1 =e cup l2.
Proof.
move=> Hrev T v.
apply/ffunP => vi.
rewrite !(ffunE,tsmorE) !cast_tupleE !(big_pred1 [tuple]); try by case => -[].
rewrite !ffunE -!extract_comp.
rewrite -(lens_comp_rev_left Hrev) -(lens_comp_rev_left (l1:=l2) (l2:=l1));
  last by rewrite -Hrev revK.
rewrite [in RHS]eq_sym.
case H: (_ == _); last by rewrite !scale0r.
rewrite !scale1r !merge_indices_empty.
do 3!f_equal.
apply/val_inj/val_inj/eq_filter => /= i.
by rewrite !mem_lensE !memtE -Hrev mem_rev.
Qed.

Lemma transpose_cup (M : tsquare 1) :
  focus [lens 0] (tsmor M) \v cup (n:=1) [lens 0; 1] =e
  focus [lens 1] (tsmor (transpose_tsquare M)) \v cup [lens 0; 1].
Proof.
move=> T v /=.
apply/ffunP => vi /=.
rewrite /asym_focus_fun !focusE /= /focus_fun.
do! rewrite !(tsmorE,ffunE,sum_ffunE,sum_enum_indices) /= !addr0 !ffunE.
rewrite !lens_left_1.
have -> : lothers [lens 0] = [lens 1] by eq_lens.
rewrite !cast_tupleE /= -!extract_comp.
have -> : lens_comp [lens 0; 1] [lens 0] = [lens 0] :> lens 3 1 by eq_lens.
have -> : lens_comp [lens 0; 1] [lens 1] = [lens 1] :> lens 3 1 by eq_lens.
rewrite !extract_merge !merge_indices_empty /= !extract_merge_disjoint.
rewrite !scalerA -!scalerDl.
f_equal.
have := mem_enum_indices (extract [lens 0] vi).
have := mem_enum_indices (extract [lens 1] vi).
by rewrite !inE => /orP[] /eqP -> /orP[] /eqP -> /=;
   rewrite !(mulr0,addr0,add0r).
all: by rewrite disjoint_has //= /others enum_ordinalE.
Qed.  

Lemma cat_2tuple A (x y : A) : [tuple of [tuple x]++[tuple y]] =  [tuple x; y].
Proof. exact/val_inj. Qed.

Lemma straighten : cap [lens 1; 2] \v cup [lens 0; 1] =e idmor 1.
Proof.
move=> T /= v.
rewrite /asym_focus_fun.
apply/ffunP => t /=.
rewrite /inner_prod /inner_coprod /M_inner_prod /M_inner_coprod.
rewrite {1}/uncurry !ffunE /= !tsmorE sum_enum_indices /= !ffunE /=.
rewrite -!cat_2tuple !extract_lens_left.
rewrite !(extract_eq_cast (lothers_left 1 1)) !extract_lens_right /= !linE.
rewrite !tsmorE !sum_enum_indices /= !ffunE /= !addr0.
apply/eqP; move: t; apply/forall_indicesP.
rewrite /= andbT; apply/andP.
(* brute force *)
rewrite !eq_ord_tuple /= /tnth /= /tnth /= /others.
rewrite /in_mem /mem /= !enum_ordinalE /= !linE.
split; apply/eqP/f_equal/eqP;
  by rewrite eq_ord_tuple /= /tnth /= /others !enum_ordinalE.
Qed.

Lemma transpose_focus (M : tsquare 1) :
  tsmor (transpose_tsquare M) =e
  cap [lens 1; 2] \v focus [lens 1] (tsmor M) \v cup [lens 0; 1].
Proof.
rewrite -{2}(transpose_tsquare_involutive M).
move=> T v.
rewrite -comp_morA comp_morE comp_morE.
move: (transpose_cup (transpose_tsquare M) v) => /= <-.
have NM : naturality (tsmor (transpose_tsquare M)) by apply/naturalityP; esplit.
have NIP : naturality (inner_prod I 1 (R:=R)) by apply/naturalityP; esplit.
set mycup := asym_focus_fun dI ([lens] : lens (0+1) 0)
                  ([lens 0; 1] : lens (2+1) 2) (inner_coprod I 1) v.
move: (asym_focusC dI ([lens 1; 2] : lens (2+1) 2) ([lens] : lens (0+1) 0)
                   NM NIP mycup).
rewrite !cast_lensE.
have -> : lothers [lens 1; 2] = [lens 0] by eq_lens.
move=> /= <-.
subst mycup.
move: (straighten v) => /= ->.
have <- : lens_id 1 = lothers [lens] by eq_lens.
by rewrite (focusI dI NM v).
Qed.
End transpose.
