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
Let C : comRingType := R[i].
Let Co : lmodType C := C^o.
Variable I : finType.
Variable dI : I.

Notation dpsquare n := (dpmatrix I C n n).
Notation idts := (idts I C).
Notation dpmatrixmx := (dpmatrixmx dI).
Notation mor := (mor I C).
Notation endo n := (mor n n).
Notation focus := (focus dI).
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
Variable M : dpsquare n.

Definition dpmxadjoint m (N : dpmatrix I C m n) : dpmatrix I C n m :=
  [ffun vi => [ffun vj => (N vj vi)^*]].

Definition dpmxunitary := dpmul (dpmxadjoint M) M == idts n.

Lemma dpmxadjointE m (N : dpmatrix I C m n) :
  dpmatrixmx (dpmxadjoint N) = adjointmx (dpmatrixmx N).
Proof. apply/matrixP => i j; by rewrite !mxE !ffunE. Qed.

Lemma dpmxunitaryE : dpmxunitary = unitarymx (dpmatrixmx M).
Proof.
case/boolP: dpmxunitary => /eqP Hts; apply/esym/eqP.
- by rewrite -dpmxadjointE -dpmatrixmx_mul Hts dpmatrixmx_id.
- move=> Hmx; elim Hts.
  rewrite -mxdpmatrix_id // -Hmx mxdpmatrix_mul //.
  by rewrite -dpmxadjointE !dpmatrixmxK.
Qed.

Lemma unitary_invP : dpmxadjoint M = M ->
  reflect (forall T, involutive (mxmor M T)) dpmxunitary.
Proof.
rewrite /dpmxunitary => ->.
apply: (iffP idP) => [/eqP|] Hinv.
- move=> T v.
  move: (f_equal (fun M => mxmor M T v) Hinv).
  by rewrite mxmor_comp -idmorE.
- apply/eqP.
  rewrite -[LHS]mxmorK -[RHS]mxmorK.
  apply mormx_eq => T v.
  rewrite mxmor_comp -idmorE /=.
  by have /= -> := Hinv T.
Qed.
End unitary_dpmatrix.

Lemma dpmxadjoint_mul n m p M N :
  dpmxadjoint (M *t N) = @dpmxadjoint m p N *t @dpmxadjoint n m M.
Proof.
rewrite -[LHS](dpmatrixmxK dI) dpmxadjointE dpmatrixmx_mul.
by rewrite adjointmx_mul -!dpmxadjointE -dpmatrixmx_mul dpmatrixmxK.
Qed.

Lemma dpmxunitary_mul n (M N : dpsquare n) :
  dpmxunitary M -> dpmxunitary N -> dpmxunitary (dpmul M N).
Proof. rewrite !dpmxunitaryE dpmatrixmx_mul; exact/unitarymx_mul. Qed.

Lemma unitarymxE n (M : 'M[C]_(#|I|^n)) :
  unitarymx M = dpmxunitary (mxdpmatrix M).
Proof. by rewrite dpmxunitaryE mxdpmatrixK. Qed.

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
  reflect (@unitary_mor n n (mxmor M)) (dpmxunitary M).
Proof.
rewrite /dpmxunitary /unitary_mor.
apply/(iffP idP).
- move=> Uf s t; move/eqP: Uf.
  move/(f_equal
          (fun ts => dpmul (dpmxadjoint (curry0 _ s)) (dpmul ts (curry0 _ t)))).
  rewrite !dpmulA -dpmulA -dpmxadjoint_mul mul1dp //.
  move/(f_equal (fun M : dpsquare 0 => M [tuple] [tuple])).
  rewrite !ffunE. under [RHS]eq_bigr do rewrite !ffunE.
  move=> Uf; rewrite -{}[RHS]Uf.
  apply eq_bigr => vi _; rewrite !ffunE !mxmorE.
  by congr (_^* * _); apply eq_bigr => vj _; rewrite !ffunE.
- move=> Uf; apply/eqP/ffunP => vi; apply/ffunP => vj.
  rewrite !ffunE; under eq_bigr do rewrite !ffunE.
  have := Uf (dpbasis C vj) (dpbasis C vi).
  rewrite /tinner.
  under eq_bigr do rewrite !mxmorE !sum_dpbasisKo.
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
