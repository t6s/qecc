From mathcomp Require Import all_ssreflect all_algebra ssrnum.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import complex.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop f2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope R_scope with real.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Definition C := R[i].
Definition ket_type := 'cV[C]_2.
Definition bra_type := 'rV[C]_2.
Notation qubit := ket_type.

Definition ket (x : 'I_2) : ket_type := \col_(i < 2) (i == x)%:R.
Definition bra (x : 'I_2) : bra_type := \row_(i < 2) (i == x)%:R.

Notation "'|' x '⟩'" := (ket x).  (* pipe (U+007C) and rangle (U+27E9) *)
Notation "'⟨' x '¦'" := (bra x).  (* langle (U+27E8) and broken bar (U+00A6) *)
Check  | 0 ⟩.
Check  ⟨ 1 ¦.

Check  (| 0 ⟩) *m (⟨ 1 ¦).
Check  (⟨ 1 ¦) *m (| 0 ⟩).

Notation "| x1 , .. , xn ⟩" := [tuple of |x1⟩ :: .. [:: |xn⟩ ] ..] (at level 0).
