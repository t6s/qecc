From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens itensor.
Import GRing.Theory.

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
Definition INO {n} m := addnO m (@ord0 n).
Notation "n '%:O'" := (INO n) (at level 2, left associativity, format "n %:O").

Notation "[ 'lens' x1 ; .. ; xn ]" :=
  (@mkLens _ _ [tuple of x1%:O :: .. [:: xn%:O] ..] erefl).

Section ordinal_examples.
Eval compute in uniq [tuple 0%:O; 1%:O; 2%:O]. (* = true *)

Let lens3_23 : lens 3 2 := [lens 1; 2].
End ordinal_examples.

Section gate_examples.
Require Reals.
From mathcomp Require Import Rstruct.
Import Num.Theory.
Local Open Scope ring_scope.

Let R := [comRingType of Reals.Rdefinitions.R].
Let Ro := [lmodType R of R^o].
Let I := [finType of 'I_2].

Notation "¦ x1 , .. , xn ⟩" :=
  (nvbasis _ [tuple of x1%:O :: .. [:: xn%:O] ..]) (at level 0).
Definition qnot : tsquare I R 1 :=
  ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩.

Definition cnot : tsquare I R 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦0,1⟩ +
  ket_bra ¦1,0⟩ ¦1,1⟩ + ket_bra ¦1,1⟩ ¦1,0⟩.

Definition hadamart : tsquare I R 1 :=
  1 / Num.sqrt 2%:R *:
    (ket_bra ¦0⟩ ¦0⟩ + ket_bra ¦0⟩ ¦1⟩ + ket_bra ¦1⟩ ¦0⟩ - ket_bra ¦1⟩ ¦1⟩).

Definition hadamart2 := tensor_tsquare hadamart hadamart.

Definition cnotH : tsquare I R 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦1,1⟩ +
  ket_bra ¦1,0⟩ ¦1,0⟩ + ket_bra ¦1,1⟩ ¦0,1⟩.

Definition cnotHe :=
  comp_endo (nvendo hadamart2) (comp_endo (nvendo cnot) (nvendo hadamart2)).

Fixpoint enum_indices n : seq (n.-tuple 'I_2) :=
  match n as n return seq (n.-tuple 'I_2) with
  | 0 => [:: [tuple of [::]]]
  | S m =>
    let l := enum_indices m in
    [seq [tuple of 0%:O :: val t] | t <- l] ++
    [seq [tuple of 1%:O :: val t] | t <- l]
  end.

Lemma caseI2 (x : 'I_2) : x = 0%:O \/ x = 1%:O.
Proof.
case: x => -[]. by left; apply/val_inj.
case => //. by right; apply/val_inj.
Qed.

Lemma mem_enum_indices n t : t \in enum_indices n.
Proof.
elim: n t => [|n IH] [[|i t] Hlen] //=.
rewrite mem_cat; apply/orP.
move/eqP: (Hlen) => [] /eqP Hlen'.
case: (caseI2 i) => Hi; [left | right]; apply/mapP => /=;
  exists (Tuple Hlen') => //; apply val_inj; by rewrite Hi.
Qed.

Lemma size_enum_indices n : size (enum_indices n) = (2 ^ n)%N.
Proof.
elim: n => //= n IH.
by rewrite !size_cat !size_map !IH addnn -mul2n expnS.
Qed.

Lemma uniq_enum_indices n : uniq (enum_indices n).
Proof.
rewrite /is_true -(enum_uniq (tuple_finType n I)).
apply eq_uniq.
  by rewrite -cardT card_tuple card_ord size_enum_indices.
move=> t. by rewrite mem_enum_indices mem_enum.
Qed.

Lemma sum_enum_indices n (F : n.-tuple 'I_2 -> R) :
  \sum_vi F vi = foldr +%R 0 (map F (enum_indices n)).
Proof.
rewrite foldrE big_map [RHS]big_uniq ?uniq_enum_indices //=.
apply/esym/eq_bigl => vi. exact/mem_enum_indices.
Qed.

Lemma eq_from_indicesP n (T : eqType) (v w : itensor I n T) :
  reflect (v = w) (all (fun x => v x == w x) (enum_indices n)).
Proof.
apply (iffP idP).
  move=> H; apply/ffunP => vi; apply/eqP.
  have : vi \in enum_indices _ by rewrite mem_enum_indices.
  by apply/allP: vi.
move -> ; by apply/allP.
Qed.

(* Checking equality of functions (sum of tensors) *)
Lemma cnotK : involutive (nvendo cnot Ro).
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: time (by rewrite !(linE,sum_nvbasisK,ffunE)).
(* 2.4s *)
Qed.

Lemma qnotK : involutive (nvendo qnot Ro).
Proof. (* exactly the same proof *)
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: by rewrite !(linE,sum_nvbasisK,ffunE).
Qed.

Lemma sqrt_nat_unit n : (Num.sqrt n.+1%:R : R) \is a GRing.unit.
Proof. by rewrite unitf_gt0 // -sqrtr0 ltr_sqrt ltr0Sn. Qed.

Lemma nat_unit n : (n.+1%:R : R)%R \is a GRing.unit.
Proof. by rewrite unitf_gt0 // ltr0Sn. Qed.

Lemma hadamartK : involutive (nvendo hadamart Ro).
Proof.
have Hnn n : n.+1%:R / n.+1%:R = 1 :>R by rewrite divrr // nat_unit.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: do! rewrite !(linE,subr0,ffunE,scalerDl,sum_enum_indices) /=.
all: rewrite -mulNrn !mulr1n -!scalerA !scale1r !scalerDr !scaleN1r !scalerN.
all: rewrite !scalerA -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //.
1: rewrite addrCA -addrA subrr linE -mulr2n.
2: rewrite opprK addrAC !addrA subrr linE -mulr2n.
all: by rewrite -(scaler_nat 2 (_ *: v _))%R scalerA Hnn scale1r.
Qed.

Lemma eq_tuple (T : eqType) n (t1 t2 : n.-tuple T) :
  (t1 == t2) = (val t1 == val t2).
Proof. by case: eqP => [-> // | H]; apply/esym/eqP => // /val_inj. Qed.

Lemma eq_ord_tuple m n (t1 t2 : n.-tuple 'I_m) :
  (t1 == t2) = (map val t1 == map val t2).
Proof.
case: eqP => [-> | H]; apply/esym/eqP => // /inj_map.
by move=> H'; elim H; apply/val_inj/H'/val_inj.
Qed.

Fixpoint enum_ordinal n : seq 'I_n :=
  match n as n return seq 'I_n with
  | 0 => [::]
  | m.+1 => ord0 :: map (lift ord0) (enum_ordinal m)
  end.

Lemma enum_ordinalE n : enum 'I_n = enum_ordinal n.
Proof.
apply/(@inj_map _ _ (val : 'I_n -> nat)). apply val_inj.
rewrite val_enum_ord.
elim: n => //= n IH.
rewrite -map_comp -(eq_map (f1:=S \o nat_of_ord (n:=n))) //.
by rewrite map_comp -IH (iotaDl 1 0 n).
Qed.

(* Trying to check the hadamart representation of cnot... *)
Lemma cnotH_ok : nvendo cnotH Ro =1 cnotHe Ro.
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=; apply/eqP.
all: rewrite !(linE,subr0,ffunE,scalerDl,sum_enum_indices) /=.
rewrite !(eq_ord_tuple,linE,subr0,ffunE,scalerDl) /=.
rewrite !enum_ordinalE /=.
rewrite !(linE,subr0,ffunE,scalerDl,sum_nvbasisK,sum_enum_indices) /=.
rewrite !eq_ord_tuple /=.
rewrite !enum_ordinalE /=.
rewrite 50!ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !(linE,subr0) /=.
rewrite 50!ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !(linE,subr0) /=.
rewrite 50!ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !(linE,subr0) /=.
rewrite !ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !(linE,subr0) /=.
rewrite -!scalerA !linE.
rewrite !(scalerA,addrA,scalerDr).
have Hmin1 : ((1 *- 1) = -1 :> R)%R by rewrite -mulNrn.
rewrite !Hmin1 !(mulrN,mulNr,mulr1,scaleNr,opprK).
rewrite -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr.
Abort.

(* Use linearity to extra the global factor first *)
Lemma cnotH_ok' : nvendo cnotH Ro =1 cnotHe Ro.
Proof.
move=> v /=.
rewrite /hadamart2 /hadamart.
set hadam := (_ *: (_ + _ + _ - _))%R.
rewrite (_ : tensor_tsquare _ _ = Linear (tensor_linearl hadam) hadam) //.
rewrite linearZ_LR.
set hadam' := (_ + _ + _ - _)%R.
rewrite (_ : Linear _ _ = Linear (tensor_linearr hadam') hadam) //.
rewrite linearZ_LR scalerA.
rewrite !mul1r -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr ?ler0n //=.
Abort.

(* Checking equality of matrices *)
Lemma cnotK' : mul_tsquare cnot cnot = id_tsquare _ _ _.
Proof.
apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
all: time (apply/eqP; do! rewrite !(linE,ffunE,sum_enum_indices) => //=).
(* 18s ! *)
Qed.
End gate_examples.
