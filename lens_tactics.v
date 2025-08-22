From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Computable Ordinal constants *)
Definition succO {n} := lift (@ord0 n).
Fixpoint addnO {n} m (p : 'I_n) : 'I_(m+n) :=
  match m as x return 'I_(x+n) with
  | 0 => p
  | m.+1 => cast_ord (esym (addSnnS m n)) (addnO m (succO p))
  end.
Lemma addnOK n m p : @addnO n m p = m + p :> nat.
Proof. elim: m n p => //= m IH n p. by rewrite IH /= addnS. Qed.

Definition INO {n} m := addnO m (@ord0 n).
Notation "n '%:O'" := (INO n) (at level 2, left associativity, format "n %:O").

Lemma succOS n m : succO m%:O = m.+1%:O :> 'I_(m.+1+n.+1).
Proof. apply/val_inj => /=. by rewrite /bump leq0n !addnOK !(addnC m). Qed.
Lemma succO0 n : succO ord0 = 1%:O :> 'I_n.+2.
Proof. exact/val_inj. Qed.
Definition succOE := (succO0,succOS).

Notation "[ 'lens' ]" := (@mkLens _ _ [tuple] erefl).
Notation "[ 'lens' x1 ; .. ; xn ]" :=
  (@mkLens _ _ [tuple of x1%:O :: .. [:: xn%:O] ..] erefl).

Fixpoint enum_ordinal n : seq 'I_n :=
  match n with
  | 0 => [::]
  | m.+1 => 0%:O :: map succO (enum_ordinal m)
  end.

Lemma enum_ordinalE n : enum 'I_n = enum_ordinal n.
Proof.
apply/(@inj_map _ _ (val : 'I_n -> nat)). exact val_inj.
rewrite val_enum_ord.
elim: n => //= n IH.
rewrite -map_comp -(@eq_map _ _ (S \o nat_of_ord (n:=n))) //.
by rewrite map_comp -IH (iotaDl 1 0 n).
Qed.

Ltac eq_lens :=
  apply/val_inj/eqP;
  rewrite ?eq_ord_tuple /= /seq_lensC /= ?enum_ordinalE /= ?(tnth_nth ord0).

Section ordinal_examples.
Eval compute in uniq [tuple 0%:O; 1%:O; 2%:O]. (* = true *)

Let lens3_23 : lens 3 2 := [lens 1; 2].
End ordinal_examples.

(* A bit of automation to avoid stalling on dependent types *)

Open Scope ring_scope.

Ltac succOE H n :=
  match n with 0%N => rewrite ?succO0 in H
  | S ?m => succOE H m; rewrite ?(@succOS _ m.+1) in H
  end.

Ltac simpl_lens x :=
  let y := fresh "y" in
  pose y := val (val x);
  rewrite /= ?(tnth_nth 0) /= in y; unfold seq_lensC in y;
  rewrite /= ?enum_ordinalE /= ?(tnth_nth 0) /= in y; succOE y 10%N;
  rewrite (_ : x = @mkLens _ _ [tuple of y] erefl); first subst y;
  last by eq_lens; rewrite /= ?enum_ordinalE.

Ltac simpl_lens_comp :=
  match goal with
  |- context [ lens_comp ?a ?b ] => simpl_lens (lens_comp a b)
  end.

Goal lensC ([lens 0; 1] : lens 4 _) = [lens 2; 3].
set x := lensC _.
simpl_lens x.
reflexivity.
Abort.

Ltac simpl_tuple x :=
  let y := fresh "y" in
  pose y := val x;
  rewrite /= ?(tnth_nth 0) /= in y; unfold seq_lensC in y;
  rewrite /= ?enum_ordinalE /= ?(tnth_nth 0) /= in y;
  rewrite (_ : x = [tuple of y]); last (by eq_lens); subst y.

Ltac simpl_extract :=
  match goal with |- context [ extract ?a ?b ] => simpl_tuple (extract a b)
  end.

Ltac simpl_merge dI :=
  match goal with |- context [ merge ?a ?b ?c] =>
    rewrite (mergeE dI); simpl_tuple (merge_nth dI a b c)
  end.
