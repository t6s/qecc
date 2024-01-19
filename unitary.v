From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens dpower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

Section unitary.
Variable R : rcfType.
Let C := [comRingType of R[i]].
Let Co := [lmodType C of C^o].
Variable I : finType.
Variable dI : I.

Notation tsquare n := (tmatrix I C n n).
Notation idts := (idts I C).
Notation tmatrixmx := (tmatrixmx dI).
Notation mor := (mor I C).
Notation endo n := (mor n n).
Notation focus := (focus dI).
Local Notation "T '^^' n " := (dpower I n T).

Definition hadjmx n m (M : 'M[C]_(n,m)) := \matrix_(i,j) (M j i)^*.

Definition unitarymx n M := @hadjmx n n M *m M == 1%:M.

Lemma hadjmx_mul n m p (M : 'M[C]_(n,m)) (N : 'M[C]_(m,p)) :
  hadjmx (M *m N) = hadjmx N *m hadjmx M.
Proof.
apply/matrixP => i j; rewrite !mxE.
rewrite rmorph_sum; apply eq_bigr => /= k _.
by rewrite !mxE -rmorphM /= mulrC.
Qed.

Lemma unitarymx_mul n (M N : 'M[C]_n) :
  unitarymx M -> unitarymx N -> unitarymx (M *m N).
Proof.
move => /eqP UM /eqP UN; apply/eqP.
by rewrite hadjmx_mul mulmxA -(mulmxA (hadjmx N)) UM mulmx1.
Qed.

Section unitary_tmatrix.
Variable n : nat.
Variable M : tsquare n.

Definition hadjts m (N : tmatrix I C m n) : tmatrix I C n m :=
  [ffun vi => [ffun vj => (N vj vi)^*]].

Definition unitaryts := mults (hadjts M) M == idts n.

Lemma hadjtsE m (N : tmatrix I C m n) :
  tmatrixmx (hadjts N) = hadjmx (tmatrixmx N).
Proof. apply/matrixP => i j; by rewrite !mxE !ffunE. Qed.

Lemma unitarytsE : unitaryts = unitarymx (tmatrixmx M).
Proof.
case/boolP: unitaryts => /eqP Hts; apply/esym/eqP.
- by rewrite -hadjtsE -tmatrixmx_mul Hts tmatrixmx_id.
- move=> Hmx; elim Hts.
  by rewrite -mxtmatrix_id // -Hmx mxtmatrix_mul // -hadjtsE !tmatrixmxK.
Qed.

Lemma unitary_invP : hadjts M = M ->
  reflect (forall T, involutive (tsmor M T)) unitaryts.
Proof.
rewrite /unitaryts => ->.
apply: (iffP idP) => [/eqP|] Hinv.
- move=> T v.
  move: (f_equal (fun M => tsmor M T v) Hinv).
  by rewrite tsmor_comp -idmorE.
- apply/eqP.
  rewrite -[LHS]tsmorK -[RHS]tsmorK.
  apply morts_eq => T v.
  rewrite tsmor_comp -idmorE /=.
  by have /= -> := Hinv T.
Qed.
End unitary_tmatrix.

Lemma hadjts_mul n m p M N : hadjts (M *t N) = @hadjts p m N *t @hadjts m n M.
Proof.
rewrite -[LHS](tmatrixmxK dI) hadjtsE tmatrixmx_mul.
by rewrite hadjmx_mul -!hadjtsE -tmatrixmx_mul tmatrixmxK.
Qed.

Lemma unitaryts_mul n (M N : tsquare n) :
  unitaryts M -> unitaryts N -> unitaryts (mults M N).
Proof. rewrite !unitarytsE tmatrixmx_mul; exact/unitarymx_mul. Qed.

Lemma unitarymxE n (M : 'M[C]_(#|I|^n)) : unitarymx M = unitaryts (mxtmatrix M).
Proof. by rewrite unitarytsE mxtmatrixK. Qed.

Section unitary_mor.
(* One could probably replace tinner by any bilinear form *)
Definition tinner n (s t : Co ^^ n) := \sum_i (s i)^* * (t i).
Definition unitary_mor m n (f : mor m n) :=
  forall s t, tinner (f Co s) (f Co t) = tinner s t.
(* Actually this only makes sense for n >= m, since the rank must be at
   least m to be unitary *)

Lemma idmorU n : unitary_mor (idmor I C n).
Proof. done. Qed.

Lemma unitary_morP n M : reflect (@unitary_mor n n (tsmor M)) (unitaryts M).
Proof.
rewrite /unitaryts /unitary_mor.
apply/(iffP idP).
- move=> Uf s t; move/eqP: Uf.
  move/(f_equal (fun ts => mults (hadjts (curryn0 s)) (mults ts (curryn0 t)))).
  rewrite !multsA -multsA -hadjts_mul mul1ts //.
  move/(f_equal (fun M : tsquare 0 => M [tuple] [tuple])).
  rewrite !ffunE. under [RHS]eq_bigr do rewrite !ffunE.
  move=> Uf; rewrite -{}[RHS]Uf.
  apply eq_bigr => vi _; rewrite !ffunE !tsmorE.
  by congr (_^* * _); apply eq_bigr => vj _; rewrite !ffunE.
- move=> Uf; apply/eqP/ffunP => vi; apply/ffunP => vj.
  rewrite !ffunE; under eq_bigr do rewrite !ffunE.
  have := Uf (dpbasis C vi) (dpbasis C vj).
  rewrite /tinner.
  under eq_bigr do rewrite !tsmorE !sum_dpbasisKo.
  move ->.
  under eq_bigr do rewrite !ffunE.
  by rewrite sum_muleqr [LHS]conjc_nat.
Qed.

Lemma unitary_comp m n p (f : mor n p) (g : mor m n) :
  unitary_mor f -> unitary_mor g -> unitary_mor (f \v g).
Proof. move=> Hf Hg s t /=; by rewrite Hf. Qed.

Lemma unitary_focus n m (l : lens n m) (f : endo m) :
  unitary_mor f -> unitary_mor (focus l f).
Proof.
rewrite /unitary_mor /tinner => /= Uf s t.
rewrite 2!(reindex_merge _ dI l) /=.
rewrite [LHS]exchange_big [RHS]exchange_big /=.
apply eq_bigr => vj _.
pose sel s : Co ^^ m := dpmap (dpsel vj) (curry dI l s).
transitivity (\sum_i (sel s i)^* * sel t i); last first.
  apply eq_bigr => vi _; by rewrite !ffunE /dpsel !ffunE.
rewrite -Uf; apply eq_bigr => vi _.
rewrite focusE /=.
rewrite /uncurry !ffunE !extract_merge !extractC_merge.
by rewrite -!(morN f) !ffunE.
Qed.
End unitary_mor.

Section projection.
Variables (n m : nat) (l : lens n m).

Let norm p := fun s : Co ^^ p => (sqrtc (tinner s s) : Co).

Definition proj (t : Co ^^ n) : Co ^^ m :=
  dpmap (@norm _) (curry dI l t).

Lemma proj_focusE p (l' : lens n p) (f : endo p) (t : Co ^^ n) :
  [disjoint l & l'] -> unitary_mor f ->
  proj (focus l' f Co t) = proj t.
Proof.
move=> Hdisj Uf.
rewrite /proj -(lmake_compE Hdisj) focus_others // uncurryK /=.
apply/ffunP => vi.
by rewrite !ffunE /norm unitary_focus.
Qed.
End projection.
End unitary.
