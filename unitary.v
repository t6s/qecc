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
Let C : comPzRingType := R[i].
Let Co : lmodType C := C^o.
Variable I : finType.
Variable dI : I.

Notation id_dpmatrix := (id_dpmatrix I C).
Notation dpmatrixmx := (dpmatrixmx dI).
Notation mor := (mor I C).
Notation endo n := (mor n n).
Local Notation "T '^^' n " := (dpower I n T).

Definition adjointmx n m (M : 'M[C]_(n,m)) := \matrix_(i,j) (M j i)^*.

Definition unitarymx n M := @adjointmx n n M *m M == 1%:M.

Lemma adjointmx_mul n m p (M : 'M[C]_(n,m)) (N : 'M[C]_(m,p)) :
  adjointmx (M *m N) = adjointmx N *m adjointmx M.
Proof.
apply/matrixP => i j; rewrite !mxE.
rewrite rmorph_sum; apply eq_bigr => /= k _.
by rewrite !mxE -rmorphM /= mulrC.
Qed.

Lemma unitarymx_mul n (M N : 'M[C]_n) :
  unitarymx M -> unitarymx N -> unitarymx (M *m N).
Proof.
move => /eqP UM /eqP UN; apply/eqP.
by rewrite adjointmx_mul mulmxA -(mulmxA (adjointmx N)) UM mulmx1.
Qed.

Section unitary_dpmatrix.
Variable n : nat.
Variable M : 'dpM[I,C^o]_n.

Definition dpadjoint m (N : 'dpM[I,C^o]_(m,n)) : 'dpM_(n,m) :=
  [ffun vi => [ffun vj => (N vj vi)^*]].

Definition dpunitary := dpadjoint M *d M == id_dpmatrix n.

Lemma dpadjointE m (N : dpmatrix I C m n) :
  dpmatrixmx (dpadjoint N) = adjointmx (dpmatrixmx N).
Proof. apply/matrixP => i j; by rewrite !mxE !ffunE. Qed.

Lemma dpunitaryE : dpunitary = unitarymx (dpmatrixmx M).
Proof.
case/boolP: dpunitary => /eqP Hts; apply/esym/eqP.
- by rewrite -dpadjointE -dpmatrixmx_mul Hts dpmatrixmx_id.
- move=> Hmx; elim Hts.
  rewrite -mxdpmatrix_id // -Hmx mxdpmatrix_mul //.
  by rewrite -dpadjointE !dpmatrixmxK.
Qed.

Lemma unitary_invP : dpadjoint M = M ->
  reflect (forall T, involutive (dpmor M T)) dpunitary.
Proof.
rewrite /dpunitary => ->.
apply: (iffP idP) => [/eqP|] Hinv.
- move=> T v.
  move: (f_equal (fun M => dpmor M T v) Hinv).
  by rewrite dpmor_comp -idmorE.
- apply/eqP.
  rewrite -[LHS]dpmorK -[RHS]dpmorK.
  apply mordp_eq => T v.
  rewrite dpmor_comp -idmorE /=.
  by have /= -> := Hinv T.
Qed.
End unitary_dpmatrix.

Lemma dpadjoint_mul n m p M N :
  dpadjoint (M *d N) = @dpadjoint m p N *d @dpadjoint n m M.
Proof.
rewrite -[LHS](dpmatrixmxK dI) dpadjointE dpmatrixmx_mul.
by rewrite adjointmx_mul -!dpadjointE -dpmatrixmx_mul dpmatrixmxK.
Qed.

Lemma dpunitary_mul n (M N : 'dpM_n) :
  dpunitary M -> dpunitary N -> dpunitary (dpmul M N).
Proof. rewrite !dpunitaryE dpmatrixmx_mul; exact/unitarymx_mul. Qed.

Lemma unitarymxE n (M : 'M[C]_(#|I|^n)) :
  unitarymx M = dpunitary (mxdpmatrix M).
Proof. by rewrite dpunitaryE mxdpmatrixK. Qed.

Section unitary_mor.
(* One could probably replace tinner by any bilinear form *)
Definition tinner n (s t : Co ^^ n) := \sum_i (s i)^* * (t i).
Definition unitary_mor m n (f : mor m n) :=
  forall s t, tinner (f Co s) (f Co t) = tinner s t.
(* Actually this only makes sense for n >= m, since the rank must be at
   least m to be unitary *)

Lemma idmorU n : unitary_mor (idmor I C n).
Proof. done. Qed.

Lemma unitary_morP n M :
  reflect (@unitary_mor n n (dpmor M)) (dpunitary M).
Proof.
rewrite /dpunitary /unitary_mor.
apply/(iffP idP).
- move=> Uf s t; move/eqP: Uf.
  move/(f_equal
          (fun ts => dpmul (dpadjoint (curry0 _ s)) (dpmul ts (curry0 _ t)))).
  rewrite !dpmulA -[LHS]dpmulA -dpadjoint_mul mul1dp //.
  move/(f_equal (fun M : 'dpM_0 => M [tuple] [tuple])).
  rewrite !ffunE.
  under [RHS]eq_bigr do rewrite !ffunE.
  move=> Uf; rewrite -{}[RHS]Uf.
  apply eq_bigr => vi _; rewrite !ffunE !dpmorE.
  by congr (_^* * _); apply eq_bigr => vj _; rewrite !ffunE.
- move=> Uf; apply/eqP/ffunP => vi; apply/ffunP => vj.
  rewrite !ffunE; under eq_bigr do rewrite !ffunE.
  have := Uf (dpbasis C vj) (dpbasis C vi).
  rewrite /tinner.
  under eq_bigr do rewrite !dpmorE !sum_dpbasisKo.
  move ->.
  under eq_bigr do rewrite !ffunE.
  by rewrite sum_muleqr [LHS]conjc_nat eq_sym.
Qed.

Lemma unitary_comp m n p (f : mor n p) (g : mor m n) :
  unitary_mor f -> unitary_mor g -> unitary_mor (f \v g).
Proof. move=> Hf Hg s t /=; by rewrite Hf. Qed.

Lemma unitary_focus n m (l : lens n m) (f : endo m) :
  unitary_mor f -> unitary_mor (focus l f).
Proof.
rewrite /unitary_mor /tinner => /= Uf s t.
rewrite 2!(reindex_merge _ l) /=.
rewrite [LHS]exchange_big [RHS]exchange_big /=.
apply eq_bigr => vj _.
pose sel s : Co ^^ m := dpmap (dpsel vj) (curry l s).
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
  dpmap (@norm _) (curry l t).

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
