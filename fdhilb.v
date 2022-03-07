From mathcomp Require Import all_ssreflect all_algebra ssrnum.
From mathcomp Require Import boolp classical_sets Rstruct topology complex normedtype.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop f2.
(*Require Import lens.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "A ^†" (at level 8, format "A ^†").
Reserved Notation "A ・ B" (at level 7, format "A ・ B").  (* katakana middle dot (U+30FB) *)

Reserved Notation "∣ x1 , .. , xn ⟩" (at level 0). (* mid (U+2223) and rangle (U+27E9) *)
Reserved Notation "'∣' x '⟩'".  (* mid (U+2223) and rangle (U+27E9) *)
Reserved Notation "'⟨' x '¦'".  (* langle (U+27E8) and brvbar (U+00A6) *)

Declare Scope quantum_scope.

(*Delimit Scope R_scope with real.*)

Import GRing.Theory.
Import Num.Theory.
Import Order.POrderTheory.

Local Open Scope ring_scope.
Local Open Scope complex_scope.
Local Open Scope quantum_scope.


(*** Complex field ***)
Definition C := R[i].

Check [normedZmodType _ of C].
Check [normedZmodType _ of C] : normedZmodType C.
Check [normedZmodType C of C].

(*** ffun_hilbertType ***)

Module Hilbert.
Section def.
Record mixin_of (T : lmodType C) := Mixin {
 op : T -> T -> C;
(* _ : forall x, op 0 x = 0;*)
(* _ : forall x, op x 0 = 0;*)
 _ : forall x y z, op (x + y) z = op x z + op y z;
 _ : forall x y z, op x (y + z) = op x y + op x z;
 _ : forall c x y, op (c *: x) y = c^* * op x y;
 _ : forall c x y, op x (c *: y) = c * op x y;
 _ : forall x y, op x y = (op y x)^*
}.
Record class_of (T : Type) := Class {
 base: GRing.Zmodule.class_of T;
 base2: GRing.Lmodule.class_of [ringType of C] T;
 mixin: mixin_of (GRing.Lmodule.Pack _ base2)
}.
Structure t := Pack {car : Type; class : class_of car}.
End def.
Module Exports.
Notation hilbertType := t.
Coercion base2 : class_of >-> GRing.Lmodule.class_of.
Coercion car : hilbertType >-> Sortclass.
End Exports.
End Hilbert.
Export Hilbert.Exports.

(*** states as qubit tuples ***)
Section nvect.
Variable R : numDomainType.
Variable M : normedModType R.
Variable n : nat.
Variable I : finType.
Definition nvect := {ffun n.-tuple I -> M}.
      
(*** Complex conjugate transpose and complex inner product ***)
Fact admx_key : unit. Proof. by []. Qed.
Definition admx m n (A : 'M[C]_(m,n)) := \matrix[admx_key]_(i, j) (A j i)^*.
Notation "A ^†" := (admx A) : complex_scope.

Definition inner_product n (u v : 'cV[C]_n) : C :=  (u ^† *m v) 0 0.
Notation "u ・ v" := (inner_product u v) : complex_scope.

(* Definition Hermitian n (A : 'M[C]_n) := admx A = A. *)

(*** bra and ket ***)

Definition ket_type := 'cV[C]_2.
Definition bra_type := 'rV[C]_2.

Record qubit := mkQubit {
  base_ket :> ket_type ;
  norm1 : base_ket ・ base_ket == 1 }.
Canonical qubit_subType := Eval hnf in [subType for base_ket].
Canonical qubit_eqType := Eval hnf in EqType _ [eqMixin of qubit by <:].

(*
Module Qubit.
Record t := mk {
  v :> ket_type ;
  Norm1 : v ・ v == 1 }.
Definition norm1 (x : t) : (v x) ・ (v x) == 1 := Norm1 x.
Arguments norm1 : simpl never.
Module Exports.
Notation qubit := t.
Notation "q %:qubit" := (@mk q (@norm1 _)).
Canonical qubit_subType := Eval hnf in [subType for v].
Definition qubit_eqMixin := [eqMixin of qubit by <:].
Canonical qubit_eqType := Eval hnf in EqType _ qubit_eqMixin.
End Exports.
End Qubit.
Export Qubit.Exports.
Coercion Qubit.v : qubit >-> ket_type.
*)


Check [lmodType C of ket_type].

Definition ket (x : 'I_2) : ket_type := \col_(i < 2) (i == x)%:R.
Definition bra (x : 'I_2) : bra_type := \row_(i < 2) (i == x)%:R.

Notation "'∣' x '⟩'" := (ket x) : quantum_scope.
Notation "'⟨' x '¦'" := (bra x) : quantum_scope.
Check  ∣ 0 ⟩.
Check  ⟨ 1 ¦.

Check  ∣0⟩ *m ⟨1¦.
Check  ⟨1¦ *m ∣0⟩.

Notation "∣ x1 , .. , xn ⟩" := [tuple of ∣x1⟩ :: .. [:: ∣xn⟩ ] ..] : quantum_scope.

Check ∣ 0, 1, 0 ⟩ : 3.-tuple ket_type.
Fail Check ∣ 0, 1, 0 ⟩ : 3.-tuple qubit.

End nvect.


(*** Unitary transformation ***)

Module Unitary.
Section ClassDef.
Notation "u ・ v" := (inner_product u v) : complex_scope.

(* Variable (A B : Hilbert C).*)
Variable n : nat.
Local Notation A := 'cV[C]_n (only parsing).
Local Notation B := 'cV[C]_n (only parsing).
Definition axiom (f : {linear A -> B}) :=
  forall x y : A, (f x) ・ (f y) = x ・ y.
Record class_of (f : A -> B) : Prop :=
  Class {base : GRing.Linear.class_of *:%R f ;
         mixin : axiom (GRing.Linear.Pack _ base)}.
Local Coercion base : class_of >-> GRing.Linear.class_of.
Structure map (phAB : phant (A -> B)) :=
  Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phAB : phant (A -> B)) (f g: A -> B) (cF : map phAB).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fL of phant_id g (apply cF) & phant_id fL class :=
  @Pack phAB f fL.
Canonical additive := GRing.Additive.Pack phAB class.
Canonical linear := GRing.Linear.Pack phAB class.
End ClassDef.

Module Exports.
Notation unitary_for s f := (class_of s f).
Notation unitary f := (lrmorphism_for *:%R f).
Coercion base : unitary_for >-> GRing.Linear.class_of.
Coercion apply : map >-> Funclass.
Notation Unitary f_lrM := (Pack (Phant _) (Class f_lrM f_lrM)).
Notation "{ 'unitary' fAB | s }" := (map s (Phant fAB))
  (at level 0, format "{ 'unitary'  fAB  |  s }") : ring_scope.
Notation "{ 'unitary' fAB }" := {unitary fAB | *:%R}
  (at level 0, format "{ 'unitary'  fAB }") : ring_scope.
Notation "[ 'unitary' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'unitary'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'unitary' 'of' f ]" := (@clone _ _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'unitary'  'of'  f ]") : form_scope.

Coercion additive : map >-> GRing.Additive.map.
Canonical additive.
Coercion linear : map >-> GRing.Linear.map.
Canonical linear.
End Exports.

End Unitary.
Include Unitary.Exports.
