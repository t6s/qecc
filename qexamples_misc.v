From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* cnot \v cnot \cnot = swap *)
(* See example from section 7.4 of  Unruh's Quantum and classical registers *)

Lemma cnot3_swap :
  mxapp [lens 0; 1] cnot \v mxapp [lens 1; 0] cnot \v mxapp [lens 0; 1] cnot
  =e (mxapp [lens 0; 1] swap : endo 2).
Proof.
apply/lift_mor_eq => v.
rewrite (decompose_scaler v) !linear_sum.
apply eq_bigr => i _.
rewrite 2!linearZ_LR; congr (_ *: _).
case: i => -[|i [|j []]] Hj //=.
rewrite [RHS]focus_dpbasis [in LHS]focus_dpbasis; simpl_extract.
rewrite {1}(mxmor_cnot i j) mxmor_swap !dpmerge_dpbasis.
do 2 simpl_merge.
rewrite focus_dpbasis mxmor_cnot addrAC addii add0r dpmerge_dpbasis.
simpl_merge.
rewrite focus_dpbasis mxmor_cnot addrCA addii addr0 dpmerge_dpbasis.
by simpl_merge.
Qed.

(* Checking equality of functions (sum of tensors) *)

Lemma cnotK : involutive (mxmor cnot Co).
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //.
all: time do 2 (rewrite !mxmorE !{1}ffunE /= !linE !sum_dpbasisK //).
(* 1.8s *)
Qed.

Lemma qnotK : involutive (mxmor qnot Co).
Proof. (* exactly the same proof *)
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: time do 2 (rewrite !mxmorE !{1}ffunE /= !linE !sum_dpbasisK //).
Qed.

(* Unitarity: matrix or endomorphism *)

Lemma qnotU : unitaryts qnot.
Proof.
apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
all: rewrite !(linE,sum_dpbasisK,ffunE).
all: apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
all: rewrite !(linE,sum_dpbasisK,ffunE).
all: time (rewrite !sum_enum_indices /= !{1}ffunE /=).
all: by rewrite !linE.
Qed.

Lemma cnotU : unitary_mor (mxmor cnot).
Proof.
move=> /= s t.
rewrite /tinner !sum_enum_indices /= !mxmorE.
rewrite !{1}ffunE /= !scale0r !scale1r !add0r !addr0 !sum_dpbasisK.
by rewrite (addrC _ (_ * _)).
Qed.

Lemma hadamardU : unitaryts hadamard.
Proof. (* Fast proof using hadamardK *)
apply/unitary_invP; last exact: hadamardK.
apply/eq_from_indicesP; do !(apply/andP; split) => //=;
  apply/eqP/eq_from_indicesP; do !(apply/andP; split); apply /eqP => //=.
all: time (rewrite !{1}ffunE /= !linE).
all: rewrite /GRing.scale /= ?mulr1 //.
by simpc.
Qed.

(* Try on a fast machine ... *)
Lemma hadamardU' : unitaryts hadamard.
Proof.
apply/eqP/eq_from_indicesP; do !(apply/andP; split) => //=;
  apply/eqP/eq_from_indicesP; do !(apply/andP; split); apply /eqP => //=.
par: time (rewrite !{1}ffunE;
     rewrite sum_enum_indices /= !{1}ffunE !eq_ord_tuple /= !linE;
     simpc => //;
     rewrite -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr ?ler0n //;
     by rewrite -mulr2n -(mulr_natl (_^-1)) divrr // nat_unit).
Qed.

(* The direct proof is fast but verbose *)
Lemma hadamardU_direct : unitary_mor (mxmor hadamard).
Proof.
move=> /= s t.
rewrite /tinner !sum_enum_indices /= !mxmorE.
time (rewrite !sum_enum_indices /= !{1}ffunE /= !linE).
rewrite /GRing.scale /= !mulr1.
rewrite mulr1n mulrN mulr1.
simpc.
rewrite !mulrDr !rmorphD !rmorphM /= !mulrDl !oppr0.
rewrite !complexr0.
rewrite !mulrA !(mulrC (_ ^*)%C) !(mulrAC _ (_ ^*)%C).
rewrite !addrA -!rmorphM !mulrN !mulNr !rmorphN /=.
rewrite -invrM ?sqrt_nat_unit // -expr2 sqr_sqrtr ?ler0n //.
rewrite opprK.
rewrite -!(addrAC _ (_ * t [tuple 0] * ((s [tuple 0])^*)%C)).
rewrite -!mulrA -mulrDl addrC !addrA.
rewrite -!(addrAC _ (_ * (t [tuple 1] * ((s [tuple 1])^*)%C))).
rewrite -mulrDl -addrA !mulNr -opprD -addrA addrK.
by rewrite -rmorphD -mulr2n -mulr_natl divrr ?nat_unit //= !mul1r addrC.
Qed.

(*
(* Trying to check the hadamart representation of cnot... *)
Lemma cnotH_ok : mxmor cnotH Co =1 cnotHe Co.
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=; apply/eqP.
all: rewrite !(linE,mxmorE,ffunE,scalerDl,sum_enum_indices) /=.
rewrite 50!(eq_ord_tuple,linE,ffunE,scalerDl) /=.
rewrite !enum_ordinalE /=.
rewrite 50!(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite 50!(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite !eq_ord_tuple /=.
rewrite !enum_ordinalE /= !mxmorE.
rewrite !ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite !sum_dpbasisK !mxmorE.
rewrite !ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite !(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite 50!(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite 50!ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite 50!(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite !(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite -!scalerA !linE.
rewrite !(scalerA,addrA,scalerDr).
(* have Hmin1 : ((1 *- 1) = -1 :> R)%R by rewrite -mulNrn. *)
rewrite !(mulrN,mulNr,mulr1,scaleNr,opprK).
rewrite -!rmorphM /= -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr.
rewrite !(addrAC _ _ (_ *: v [tuple 0%:O; 0%:O])).
rewrite -!scalerDl.
rewrite -mulr2n -!mulrSr -mulr_natl.
Abort.
*)

(* Computations on matrices *)

Definition hadamard2 := tensor_dpsquare hadamard hadamard.

Definition cnotH : dpsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦1,1⟩ +
  ket_bra ¦1,0⟩ ¦1,0⟩ + ket_bra ¦1,1⟩ ¦0,1⟩.

Definition cnotHe :=
  mxmor hadamard2 \v mxmor cnot \v mxmor hadamard2.

(* Use linearity to extra the global factor first *)
Lemma cnotH_ok' : mxmor cnotH Co =1 cnotHe Co.
Proof.
move=> v /=.
rewrite /hadamard2 /hadamard.
set hadam := (_ *: (- _ + _ + _ + _))%R.
rewrite (_ : tensor_dpsquare hadam hadam = tensor_dpsquare' hadam hadam) //.
rewrite linearZ_LR /= /tensor_dpsquare' /hadam.
set hadam' := (- _ + _ + _ + _)%R.
rewrite linearZ_LR scalerA -!rmorphM.
rewrite !mul1r -!invrM ?sqrt_nat_unit // -!expr2 sqr_sqrtr ?ler0n //=.
Abort.

(*
(* Checking equality of matrices *)
Lemma cnotK' : mults cnot cnot = idts _ _ _.
Proof.
apply/eq_from_indicesP; do! (apply/andP; split) => //=.
all: apply/eqP/eq_from_indicesP; do! (apply/andP; split) => //=.
par: time (apply/eqP; do! rewrite !(linE,ffunE,sum_enum_indices) => //=).
(* 18s ! *)
Qed.
*)
