From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* cnot \v cnot \v cnot = swap *)
(* See example from section 7.4 of  Unruh's Quantum and classical registers *)

Lemma swap_cnot : swap =e cnot \v focus [lens 1; 0] cnot \v cnot.
Proof.
apply/eq_mor_basis => -[[|i [|j []]] Ht] //.
rewrite /= swapE cnotE focus_dpbasis.
simpl_extract.
rewrite cnotE dpmerge_dpbasis.
simpl_merge.
rewrite cnotE.
by rewrite addrAC addii add0r addrCA addii addr0.
Qed.

(* Checking equality of functions (sum of tensors) *)

Lemma cnotK : involutive (cnot Co).
Proof.
move=> v; rewrite (decompose_scaler v) !linear_sum.
apply eq_bigr => /= -[] [|a [|b []]] //= Hi _.
by rewrite !linearE /= !cnotE addrA addii add0r.
Qed.

Lemma qnotK : involutive (qnot Co).
Proof. (* exactly the same proof *)
move=> v; rewrite (decompose_scaler v) !linear_sum.
apply eq_bigr => /= -[] [|a [|b []]] //= Hi _.
by rewrite !linearE /= !qnotE addrA addii add0r.
Qed.

(* Unitarity: matrix or endomorphism *)

Lemma qnotU : unitary_mor qnot.
Proof.
apply/(unitary_morP 0).
apply/eqP/eq_from_indicesP; do! (apply/andP; split => //);
  apply/eqP/eq_from_indicesP; do! (apply/andP; split => //=).
all: by rewrite !ffunE /= !sum_dpbasisKo !ffunE conjc_nat !(tnth_nth 0).
Qed.

Lemma cnotU : unitary_mor cnot.
Proof.
apply/(unitary_morP dI).
apply/eqP/eq_from_indicesP; do! (apply/andP; split => //);
  apply/eqP/eq_from_indicesP; do! (apply/andP; split => //=).
all: by rewrite !ffunE /= !sum_dpbasisKo !ffunE conjc_nat !(tnth_nth 0).
Qed.

Lemma hadamardU : dpunitary hadamard_dpmatrix.
Proof. (* Fast proof using hadamardK *)
apply/unitary_invP; last exact: hadamardK.
apply/eq_from_indicesP; do !(apply/andP; split) => //=;
  apply/eqP/eq_from_indicesP; do !(apply/andP; split); apply /eqP => //=.
all: time (rewrite !{1}ffunE /= !linE).
all: rewrite /GRing.scale /= ?mulr1 //.
by simpc.
Qed.

(* Try on a fast machine ... *)
Lemma hadamardU' : dpunitary hadamard_dpmatrix.
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
Lemma hadamardU_direct : unitary_mor hadamard.
Proof.
move=> /= s t.
rewrite /tinner !sum_enum_indices /= !dpmorE.
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
Lemma cnotH_ok : dpmor cnotH Co =1 cnotHe Co.
Proof.
move=> v; apply/eq_from_indicesP; do! (apply/andP; split) => //=; apply/eqP.
all: rewrite !(linE,dpmorE,ffunE,scalerDl,sum_enum_indices) /=.
rewrite 50!(eq_ord_tuple,linE,ffunE,scalerDl) /=.
rewrite !enum_ordinalE /=.
rewrite 50!(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite 50!(linE,ffunE,scalerDl,sum_dpbasisK,sum_enum_indices) /=.
rewrite !eq_ord_tuple /=.
rewrite !enum_ordinalE /= !dpmorE.
rewrite !ffunE /= !eq_ord_tuple /= !enum_ordinalE /= !linE /=.
rewrite !sum_dpbasisK !dpmorE.
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

Definition hadamard2 := tensor_dpsquare hadamard_dpmatrix hadamard_dpmatrix.

Definition cnotH : dpsquare 2 :=
  ket_bra ¦0,0⟩ ¦0,0⟩ + ket_bra ¦0,1⟩ ¦1,1⟩ +
  ket_bra ¦1,0⟩ ¦1,0⟩ + ket_bra ¦1,1⟩ ¦0,1⟩.

Definition cnotHe :=
  dpmor hadamard2 \v cnot \v dpmor hadamard2.

(* Use linearity to extra the global factor first *)
Lemma cnotH_ok' : dpmor cnotH Co =1 cnotHe Co.
Proof.
move=> /= v.
rewrite /hadamard2 /hadamard_dpmatrix.
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
