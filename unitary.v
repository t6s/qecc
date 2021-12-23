From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens tpower.

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

Section unitary_endo.
Definition tinner n (s t : tpower I n Co) := \sum_i (s i)^* * (t i).
Definition unitary_endo n (f : endo n) :=
  forall s t, tinner (f Co s) (f Co t) = tinner s t.

Lemma unitary_endoP n M : reflect (@unitary_endo n (tsmor M)) (unitaryts M).
Proof.
rewrite /unitaryts /unitary_endo.
apply/(iffP idP).
- move=> Uf s t; move/eqP: Uf.
  move/(f_equal (fun ts => mults (hadjts (curryn0 s)) (mults ts (curryn0 t)))).
  rewrite !multsA -multsA -hadjts_mul mul1ts //.
  move/(f_equal (fun M : tsquare 0 => M [tuple] [tuple])).
  rewrite !ffunE. under eq_bigr do rewrite !ffunE.
  under [RHS]eq_bigr do (rewrite !ffunE; simpc).
  move=> Uf; rewrite -[RHS]Uf.
  apply eq_bigr => vi _; rewrite !ffunE.
  rewrite /GRing.scale /=.
  by congr (_^* * _); apply eq_bigr => vj _; rewrite !ffunE.
- move=> Uf; apply/eqP/ffunP => vi; apply/ffunP => vj.
  rewrite !ffunE; under eq_bigr do rewrite !ffunE.
  have := Uf (tpbasis C vi) (tpbasis C vj).
  rewrite /tinner.
  under eq_bigr do rewrite !ffunE !sum_tpbasisKo.
  move ->.
  under eq_bigr do rewrite !ffunE.
  rewrite (bigD1 vi) //= big1 ?addr0.
    by rewrite eqxx eq_sym /=; simpc.
  by move=> i Hi; rewrite eq_sym (negbTE Hi) conjc0 mul0r.
Qed.

Lemma unitary_focus n m (l : lens n m) (f : endo m) :
  naturality f -> unitary_endo f -> unitary_endo (focus l f).
Proof.
rewrite /unitary_endo /tinner => /= Nf Uf s t.
rewrite 2!(reindex_merge_indices _ dI l) /=.
rewrite [LHS]exchange_big [RHS]exchange_big /=.
apply eq_bigr => vj _.
pose sel s : tpower I m Co := map_tpower (tpsel C vj) (curry dI l s).
move/(_ (sel s) (sel t)) in Uf.
transitivity (\sum_i (sel s i)^* * sel t i); last first.
  by apply eq_bigr => vi _; rewrite !ffunE /= !ffunE.
rewrite -Uf; apply eq_bigr => vi _.
rewrite focusE /= /focus_fun.
rewrite /uncurry !ffunE !extract_merge !extract_lothers_merge.
by rewrite -!Nf !ffunE.
Qed.
End unitary_endo.  
End unitary.
