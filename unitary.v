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
Variable I : finType.
Variable dI : I.
Hypothesis HcardI : (#|I| > 0)%N.

Notation tsquare n := (tmatrix I C n n).
Notation idts := (idts I C).
Notation tsquaremx := (tsquaremx HcardI).
Notation mor := (mor I C).
Notation endo n := (mor n n).
Notation focus := (focus dI).

Section unitary_def.
Variable n : nat.
Variable M : 'M[C]_n.

Definition hadjmx : 'M[C]_n := \matrix_(i,j) (M j i)^*.

Definition unitarymx := hadjmx *m M == 1%:M.
End unitary_def.

Lemma hadjmx_mul n : {morph @hadjmx n : M N / M *m N >-> N *m M}.
Proof.
move=> M N; apply/matrixP => i j; rewrite !mxE.
rewrite rmorph_sum; apply eq_bigr => /= k _.
by rewrite !mxE -rmorphM /= mulrC.
Qed.

Lemma unitarymx_mul n (M N : 'M[C]_n) :
  unitarymx M -> unitarymx N -> unitarymx (M *m N).
Proof.
move => /eqP UM /eqP UN; apply/eqP.
by rewrite hadjmx_mul mulmxA -(mulmxA (hadjmx N)) UM mulmx1.
Qed.

Section unitary_tsquare.
Variable n : nat.
Variable M : tsquare n.

Definition hadjts : tsquare n := [ffun vi => [ffun vj => (M vj vi)^*]].

Definition unitaryts := mults hadjts M == idts n.

Lemma hadjtsE : tsquaremx hadjts = hadjmx (tsquaremx M).
Proof. apply/matrixP => i j; by rewrite !mxE !ffunE. Qed.

Lemma unitarytsE : unitaryts = unitarymx (tsquaremx M).
Proof.
case/boolP: unitaryts => /eqP Hts; apply/esym/eqP.
- by rewrite -hadjtsE -tsquaremx_mul Hts tsquaremx_id.
- move=> Hmx; elim Hts.
  by rewrite -mxtsquare_id // -Hmx mxtsquare_mul // -hadjtsE !tsquaremxK.
Qed.
End unitary_tsquare.

Lemma unitaryts_mul n (M N : tsquare n) :
  unitaryts M -> unitaryts N -> unitaryts (mults M N).
Proof. rewrite !unitarytsE tsquaremx_mul; exact/unitarymx_mul. Qed.

Lemma unitarymxE n (M : 'M[C]_(#|I|^n)) : unitarymx M = unitaryts (mxtsquare M).
Proof. by rewrite unitarytsE mxtsquareK. Qed.

Section unitary_endo.
Definition unitary_endo n (f : endo n) := unitaryts (morts f).

Lemma scalerb_if (x : C) (b : bool) :
  x *: b%:R = if b then x%:A else 0 :> C^o.
Proof. rewrite -mulr_algl; by case: b; rewrite (mulr1, mulr0). Qed.

Lemma morts_focus n m (l : lens n m) (M : tsquare m) vi vj :
  morts (focus l (tsmor M)) vi vj =
  if extract (lothers l) vi == extract (lothers l) vj
  then (M (extract l vi) (extract l vj))%:A else 0.
Proof.
rewrite !ffunE focusE !ffunE sum_ffunE.
rewrite (bigD1 (extract l vj)) //= big1.
  rewrite !ffunE addr0 scalerb_if.
  symmetry.
  case: ifP => [/eqP -> | /eqP Hm].
     by rewrite merge_indices_extract eqxx.
  case: ifP => // /eqP/(f_equal (extract (lothers l))).
  by rewrite extract_lothers_merge => /esym.
move=> i Hi.
rewrite !ffunE.
case Hm: (_ == _).
  move/eqP/(f_equal (extract l)): Hm.
  rewrite extract_merge => Hm.
  by rewrite Hm eqxx in Hi.
by rewrite scaler0.
Qed.

Lemma unitary_focus n m (l : lens n m) (f : endo m) :
  naturality f -> unitary_endo f -> unitary_endo (focus l f).
Proof.
rewrite /unitary_endo /unitaryts => /naturalityP [M] Nf /eqP Uf.
apply/eqP/ffunP => vi; apply/ffunP => vj.
move: Uf => /(f_equal (fun f : tsquare m => f (extract l vi))).
move/(f_equal (fun f : tpower I m C^o => f (extract l vj))) => Uf.
rewrite !ffunE.
under eq_bigr do rewrite ffunE.
rewrite (reindex (fun v : m.-tuple I * (n-m).-tuple I =>
                    merge_indices dI l (fst v) (snd v))) /=; last first.
  exists (fun v => (extract l v, extract (lothers l) v)) => // v _.
    by rewrite extract_merge extract_lothers_merge; case: v.
  by rewrite /= merge_indices_extract.
rewrite -[LHS](pair_bigA _
    (fun i j => ((morts (focus l f) (merge_indices dI l i j) vi)^*)%C *
                  morts (focus l f) (merge_indices dI l i j) vj)) /=.
move: Uf.
rewrite !ffunE.
under eq_bigr do rewrite !ffunE !Nf !ffunE !sum_tpbasisKo.
move=> Uf.
case/boolP: (extract (lothers l) vi == extract (lothers l) vj) => /eqP Hij;
  last first.
  case vij: (_ == _).
    by elim Hij; rewrite (eqP vij).
  rewrite big1 // => i _.
  rewrite big1 // => j _.
  rewrite !ffunE !(focus_eq dI l Nf).
  have := morts_focus l M (merge_indices dI l i j) vi.
  have := morts_focus l M (merge_indices dI l i j) vj.
  rewrite !ffunE => -> ->.
  rewrite extract_lothers_merge extract_merge.
  case: ifP => /eqP Hovi.
    case: ifP => /eqP Hovj.
      elim Hij; by rewrite -Hovi Hovj.
    by rewrite mulr0.
  by rewrite conjc0 mul0r.
transitivity (\sum_i ((M i (extract l vi))^*)%C * M i (extract l vj)).
  apply eq_bigr => i _.
  under eq_bigr => vk _.
    rewrite !ffunE !(focus_eq dI l Nf).
    have := morts_focus l M (merge_indices dI l i vk) vi.
    have := morts_focus l M (merge_indices dI l i vk) vj.
    rewrite !ffunE => -> ->.
    rewrite extract_lothers_merge extract_merge.
    over.
  rewrite /=.
  rewrite (bigD1 (extract (lothers l) vi)) //= big1; last first.
    move=> j Hj.
    by rewrite (negbTE Hj) conjc0 mul0r.
  rewrite Hij !eqxx addr0.
  by rewrite /GRing.scale /= !mulr1.
rewrite Uf.
rewrite -[in RHS](merge_indices_extract dI l vi).
rewrite -[in RHS](merge_indices_extract dI l vj) -Hij.
by rewrite (inj_eq (@merge_indices_inj _ dI _ _ _ _)).
Qed.
End unitary_endo.  
End unitary.
