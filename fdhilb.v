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

(*** ffun_normedModType ***)

Section FinFunNormedMod.
Variable K : numDomainType.
Variable aT : finType.
Variable rT : normedModType K.
Local Notation fT := {ffun aT -> rT}.

Check [lmodType _ of fT].
Fail Check [normedZmodType _ of fT].

Implicit Types (f g : fT).

Definition ffun_norm f : K := \sum_(i in aT) `| f i |.

Lemma ler_ffun_norm_add f g : ffun_norm (f + g) <= ffun_norm f + ffun_norm g.
Proof.
rewrite /ffun_norm -big_split /=; apply ler_sum => i _.
apply/le_trans: (ler_norm_add (f i) (g i)).
by rewrite ffunE le_eqVlt eqxx.
Qed.
Lemma ffun_norm_eq0 f : ffun_norm f = 0 -> f = 0.
Proof.
rewrite /ffun_norm => /psumr_eq0P H.
apply/ffunP => i; rewrite ffunE.
by apply/normr0_eq0/H.
Qed.
Lemma ffun_norm_natmul f k : ffun_norm (f *+ k) = (ffun_norm f) *+ k.
Proof.
by rewrite /ffun_norm -sumrMnl; under eq_bigr do rewrite ffunMnE normrMn.
Qed.
Lemma ffun_normN f : ffun_norm (- f) = ffun_norm f.
Proof. by rewrite /ffun_norm; under eq_bigr do rewrite ffunE normrN. Qed.

Definition ffun_normedZmodMixin :=
  @Num.NormedMixin _ _ _ ffun_norm ler_ffun_norm_add
    ffun_norm_eq0 ffun_norm_natmul ffun_normN.

Canonical ffun_normedZmodType := NormedZmodType K fT ffun_normedZmodMixin.

Check [normedZmodType _ of fT].
Fail Check [pseudoMetricNormedZmodType _ of fT].
Fail Check [pseudoMetricType _ of fT].
Fail Check [uniformType of fT].
Fail Check [filteredType _ of fT].
Fail Check [pointedType _ of fT].

Program Definition ffun_PointedMixin : @Pointed.point_of fT
Program Definition ffun_FilteredMixin : @Filtered.nbhs_of fT


Program Definition ffun_UniformMixin : @Uniform.mixin_of fT nbhs := Uniform.Mixin _ _.

Program Definition ffun_PseudoMetricMixin : @PseudoMetric.mixin_of K fT entourage := PseudoMetric.Mixin _ _ _ _.

Lemma ffun_norm_ball :
  @ball _ [pseudoMetricType K of fT] = ball_ (fun f => `| f |).

Definition ffun_PseudoMetricNormedZmodMixin :=

Definition matrix_PseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin mx_norm_ball.
Canonical matrix_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K 'M[K]_(m.+1, n.+1) matrix_PseudoMetricNormedZmodMixin.



Fail Check [normedModType _ of fT].

Lemma ffun_normZ (l : K) f : `| l *: f | = `| l | * `| f |.
Proof.
rewrite {1 3}/Num.Def.normr /= /ffun_norm /= big_distrr /=.
by under eq_bigr do rewrite ffunE normmZ.
Qed.

Definition ffun_NormedModMixin := NormedModMixin ffun_normZ.
Canonical ffun_normedModType :=
  NormedModType K fT ffun_NormedModMixin.

End matrix_NormedModule.

Implicit Types f g : {ffun aT -> rT}.

Definition ffun_scale k f := [ffun a => k *: f a].

Fact ffun_scaleA k1 k2 f : 
  ffun_scale k1 (ffun_scale k2 f) = ffun_scale (k1 * k2) f.
Proof. by apply/ffunP=> a; rewrite !ffunE scalerA. Qed.
Fact ffun_scale1 : left_id 1 ffun_scale.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE scale1r. Qed.
Fact ffun_scale_addr k : {morph (ffun_scale k) : x y / x + y}.
Proof. by move=> f g; apply/ffunP=> a; rewrite !ffunE scalerDr. Qed.
Fact ffun_scale_addl u : {morph (ffun_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> k1 k2; apply/ffunP=> a; rewrite !ffunE scalerDl. Qed.

Definition ffun_lmodMixin := 
  LmodMixin ffun_scaleA ffun_scale1 ffun_scale_addr ffun_scale_addl.
Canonical ffun_lmodType :=
  Eval hnf in LmodType R {ffun aT -> rT} ffun_lmodMixin.

End FinFunNormedMod.


(*** states as qubit tuples ***)
Section nvect.
Variable R : numDomainType.
Variable M : normedModType R.
Variable n : nat.
Variable I : finType.
Definition nvect := {ffun n.-tuple I -> M}.
      
Check [lmodType _ of nvect].
About ffun_lmodType.


Check [normedModType _ of nvect].


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


(*** ***)


(*** Unitary transformation ***)

Module Unitary.
Section ClassDef.
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


(*** ***)
