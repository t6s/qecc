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
Definition tpinner n (s t : tpower I n Co) := \sum_i (s i)^* * (t i).
Definition unitary_endo n (f : endo n) :=
  forall s t, tpinner (f Co s) (f Co t) = tpinner s t.

Lemma unitary_endoP n f :
  naturality f -> reflect (@unitary_endo n f) (unitaryts (morts f)).
Proof.
rewrite /unitaryts /unitary_endo => Nf.
apply/(iffP idP) => Uf.
- case/naturalityP: Nf => M Nf s t.
  move/eqP: Uf; rewrite (morts_eq Nf) tsmorK.
  move/(f_equal (fun ts => mults (hadjts (curryn0 s)) (mults ts (curryn0 t)))).
  rewrite !multsA -multsA -hadjts_mul.
  rewrite (_ : idts _ *t curryn0 t = curryn0 t); last by
    rewrite -[LHS](tmatrixmxK dI) tmatrixmx_mul tmatrixmx_id mul1mx tmatrixmxK.
  move/(f_equal (fun M : tsquare 0 => M [tuple] [tuple])).
  rewrite !ffunE. under eq_bigr do rewrite !ffunE.
  under [RHS]eq_bigr do (rewrite !ffunE; simpc).
  move=> Uf.
  transitivity (\sum_i ((s i)^*)%C * t i) => //.
  rewrite -Uf.
  apply eq_bigr => vi _; rewrite !Nf !ffunE.
  rewrite /GRing.scale /=.
  by congr (_^* * _); apply eq_bigr => vj _; rewrite !ffunE.
- case/naturalityP: Nf => M Nf.
  rewrite (morts_eq Nf) tsmorK.
  apply/eqP/ffunP => vi; apply/ffunP => vj.
  rewrite !ffunE.
  under eq_bigr do rewrite !ffunE.
  move: Uf.
  move/(_ (tpbasis C vi) (tpbasis C vj)).
  rewrite !Nf /tpinner.
  under eq_bigr do rewrite !ffunE !sum_tpbasisKo.
  move ->.
  under eq_bigr do rewrite !ffunE.
  rewrite (bigD1 vi) //= big1 ?addr0.
    rewrite eqxx /=. simpc. by rewrite eq_sym.
  move=> i Hi. by rewrite eq_sym (negbTE Hi) conjc0 mul0r.
Qed.

Lemma scalerb_if (x : C) (b : bool) :
  x *: b%:R = if b then (x : C^o) else 0.
Proof. rewrite /GRing.scale /=; by case: b; rewrite (mulr1, mulr0). Qed.

Lemma morts_focus n m (l : lens n m) (M : tsquare m) vi vj :
  morts (focus l (tsmor M)) vi vj =
  if extract (lothers l) vi == extract (lothers l) vj
  then M (extract l vi) (extract l vj) else 0.
Proof.
rewrite !ffunE focusE !ffunE sum_ffunE.
rewrite (bigD1 (extract l vj)) //= big1.
  rewrite !ffunE addr0 scalerb_if.
  symmetry.
  case: ifP => /eqP Hm.
     by rewrite Hm merge_indices_extract eqxx.
  case: ifP => // /eqP/(f_equal (extract (lothers l))).
  by rewrite extract_lothers_merge => /esym.
move=> i Hi.
rewrite !ffunE scalerb_if.
case: ifP => // /eqP/(f_equal (extract l)).
rewrite extract_merge => Hm; by rewrite Hm eqxx in Hi.
Qed.

Lemma unitary_focus n m (l : lens n m) (f : endo m) :
  naturality f -> unitary_endo f -> unitary_endo (focus l f).
Proof.
move=> Nf /(unitary_endoP Nf) => Uf.
apply/unitary_endoP; first exact: focus_naturality.
move: Nf Uf; rewrite /unitaryts => /naturalityP [M] Nf /eqP.
rewrite (morts_eq Nf) (morts_eq (focus_eq dI l Nf)) tsmorK => Uf {Nf f}.
apply/eqP/ffunP => vi; apply/ffunP => vj.
move: Uf => /(f_equal (fun f : tsquare m => f (extract l vi))).
move/(f_equal (fun f : tpower I m C^o => f (extract l vj))).
rewrite !ffunE.
under eq_bigr do rewrite !ffunE.
move => Uf.
under eq_bigr do rewrite ffunE.
rewrite (reindex_merge_indices _ dI l) /=.
case/boolP: (extract (lothers l) vi == extract (lothers l) vj) => Hij;
  last first.
  case vij: (_ == _).
    by rewrite (eqP vij) eqxx in Hij.
  rewrite big1 // => i _.
  rewrite big1 // => j _.
  rewrite !morts_focus extract_lothers_merge extract_merge.
  case: ifP => /eqP Hovi; last by rewrite conjc0 mul0r.
  case: ifP => /eqP Hovj; last by rewrite mulr0.
  by rewrite -Hovi Hovj eqxx in Hij.
transitivity (\sum_i ((M i (extract l vi))^*)%C * M i (extract l vj)).
  apply eq_bigr => i _.
  under eq_bigr do rewrite !morts_focus extract_lothers_merge extract_merge.
  rewrite (bigD1 (extract (lothers l) vi)) //= big1; last first.
    by move=> j /negbTE -> ; rewrite conjc0 mul0r.
  by rewrite Hij eqxx addr0.
rewrite Uf.
rewrite -[in RHS](merge_indices_extract dI l vi).
rewrite -[in RHS](merge_indices_extract dI l vj) -(eqP Hij).
by rewrite (inj_eq (@merge_indices_inj _ dI _ _ _ _)).
Qed.
End unitary_endo.  
End unitary.
