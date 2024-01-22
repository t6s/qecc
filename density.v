From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens dpower unitary.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

Section scalerv.
Variables (R : comRingType) (T : lmodType R) (v : T).
Definition scalerv (x : R ^o) := x *: v.
Lemma scalerv_is_linear : linear scalerv.
Proof. by move=> x y z; rewrite /scalerv !linearE/= scalerA mulrC scalerDl. Qed.
Canonical scalerv_lin := Linear scalerv_is_linear.
End scalerv.

Section density.
Variable R : rcfType.
Let C := [comRingType of R[i]].
Let Co := [lmodType C of C^o].
Variable I : finType.
Variable dI : I.

(* Type of density matrices over C *)
Notation dpsquare n := (dpmatrix I C n n).
Notation idts := (idts I C).
Notation dpmatrixmx := (dpmatrixmx dI).
Notation mor := (mor I C).
Notation endo n := (mor n n).
Notation focus := (focus dI).
Notation "T '^^' n " := (dpower I n T).
(* Generalized version of density matrices *)
Definition dsquare (T : lmodType C) n := [lmodType C of T ^^ n ^^ n].

Definition conjCo : Co -> Co := conjc.

Definition densitymx n (v : Co ^^ n) : dpsquare n :=
  dpmap (scalerv (dpmap conjCo v)) v.

Definition hconj_mor m n (f : mor m n) : mor m n :=
  mxmor (dpmap (dpmap conjCo) (mormx f)).

(* WIP: application of a morphism to a density matrix *)
Definition applyU (T : lmodType C) m n (f : mor m n) (M : dsquare T m)
  : dsquare T n := dpmap (hconj_mor f _) (f _ M).

Lemma applyU_densitymx m n (f : mor m n) (v : Co ^^ m) :
  applyU f (densitymx v) = densitymx (f _ v).
Proof.
apply/ffunP => vi.
rewrite !ffunE /densitymx -morN /hconj_mor !ffunE /= !linearE.
congr (_ *: _).
apply/ffunP => vj.
rewrite mxmorE /mormx.
under eq_bigr do rewrite !ffunE.
rewrite [in RHS](decompose_scaler v) /conjCo.
rewrite !linear_sum !ffunE sum_ffunE linear_sum /=.
apply eq_bigr => w _.
rewrite [in LHS]/GRing.scale /= -rmorphM /=.
by rewrite linearE mulrC ffunE.
Qed.

Lemma focus_hconj_mor n m (l : lens n m) (f : endo m) :
  focus l (hconj_mor f) =e hconj_mor (focus l f).
Proof.
move=> /= T x.
apply/ffunP => /= v.
rewrite focusE !ffunE !mxmorE sum_ffunE (reindex_merge _ dI l) /=.
apply eq_bigr => vi _.
rewrite !ffunE /= /conjCo.
under eq_bigr do rewrite !ffunE focusE !ffunE /= curry_dpbasis.
under eq_bigr do rewrite -morN /= !ffunE extract_merge extractC_merge.
set flv := f _ _ _; clearbody flv.
rewrite (bigD1 (extract (lensC l) v)) //= eqxx scale1r big1 ?addr0 // => vj Hj.
by rewrite (negbTE Hj) scale0r conjc0 scale0r.
Qed.

(* The adjoint morphism (going through matrix representation) *)
Definition hadj_mor m n (f : mor m n) : mor n m :=
  mxmor (hadjts (mormx f)).

(* Focus and adjunction commute *)
Lemma focus_hadj_mor n m (l : lens n m) (f : endo m) :
  focus l (hadj_mor f) =e hadj_mor (focus l f).
Proof.
move=> /= T x.
apply/ffunP => /= v.
rewrite focusE !ffunE !mxmorE sum_ffunE (reindex_merge _ dI l) /=.
apply eq_bigr => vi _.
rewrite !ffunE /=.
under eq_bigr do rewrite !ffunE focusE !ffunE /= extract_merge extractC_merge.
under eq_bigr do rewrite curry_dpbasis -morN /= !ffunE.
set flv := f _ _; clearbody flv.
rewrite (bigD1 (extract (lensC l) v)) //= eqxx scale1r big1 ?addr0 // => vj Hj.
by rewrite eq_sym (negbTE Hj) scale0r conjc0 scale0r.
Qed.

Section dptranspose.
Variables (T : lmodType C) (m n : nat).
Definition dptranspose (M : T ^^ n ^^ m) : T ^^ m ^^ n :=
  [ffun vi => [ffun vj => M vj vi]].
Lemma dptranspose_is_linear : linear dptranspose.
Proof. by move=> x y z; apply/ffunP=> vi; apply/ffunP=> vj; rewrite !ffunE. Qed.
Canonical dptranspose_lin := Linear dptranspose_is_linear.
End dptranspose.

Lemma dptransposeK T m n : cancel (@dptranspose T m n) (@dptranspose T _ _).
Proof. by move=> x; apply/ffunP=> v; apply/ffunP=> w; rewrite !ffunE. Qed.

Section curryds.
Variables (T : lmodType C) (n m : nat) (l : lens n m).

Definition curryds : dsquare T n -> dsquare (dsquare T (n-m)) m :=
  dpmap (@dptranspose _ (n-m) m) \o dpmap (dpmap (curry dI l)) \o curry dI l.
Canonical curryds_lin := [linear of curryds].

Lemma currydsE M :
  curryds M =
  [ffun v : m.-tuple I =>
   [ffun v' : m.-tuple I =>
    [ffun w : (n-m).-tuple I =>
     [ffun w' : (n-m).-tuple I => M (merge dI l v w) (merge dI l v' w')]]]].
Proof.
apply/ffunP=> v; apply/ffunP=> v'; apply/ffunP=> w; apply/ffunP=> w'.
by rewrite !ffunE.
Qed.

Definition uncurryds : dsquare (dsquare T (n-m)) m -> dsquare T n :=
  uncurry l \o dpmap (dpmap (uncurry l)) \o dpmap (@dptranspose _ m (n-m)).
Canonical uncurryds_lin := [linear of uncurryds].

Definition uncurrydsE M :
  uncurryds M =
  [ffun v : n.-tuple I =>
   [ffun w : n.-tuple I =>
    M (extract l v) (extract l w) (extract (lensC l) v) (extract (lensC l) w)]].
Proof. by apply/ffunP=> v; apply/ffunP=> w; rewrite !ffunE. Qed.

Lemma uncurrydsK : cancel uncurryds curryds.
Proof.
move=> M; apply/ffunP=> v; apply/ffunP=> w; apply/ffunP=> v'; apply/ffunP=> w'.
by rewrite !ffunE !extract_merge !extractC_merge.
Qed.

Lemma currydsK : cancel curryds uncurryds.
Proof.
move=> M; apply/ffunP=> v; apply/ffunP=> w; by rewrite !ffunE !merge_extract.
Qed.
End curryds.

Lemma eq_dpmap (T1 T2 : lmodType C) m (f g : T1 -> T2) :
  f =1 g -> @dpmap I m T1 T2 f =1 dpmap g.
Proof. by move=> fg X; apply/ffunP => v; rewrite !ffunE fg. Qed.

Lemma dpmap_compose (T1 T2 T3 : lmodType C) m (f : T1 -> T2) (g : T2 -> T3) X :
  @dpmap I m _ _ (g \o f) X = dpmap g (dpmap f X).
Proof. by apply/ffunP=> v; rewrite !ffunE. Qed.

Lemma dpmap_dptranspose (T : lmodType C) m n p (f : mor m p) X :
  dpmap (f T) (@dptranspose T m n X) = dptranspose (f _ X).
Proof.
apply/ffunP=> v; apply/ffunP=> w /=.
rewrite ffunE.
move/naturalityP: (morN f) => [M Hf].
rewrite !Hf !ffunE !mxmorE sum_ffunE.
apply eq_bigr => vj _.
by rewrite !ffunE.
Qed.

Lemma dptranspose_dpmap (T : lmodType C) m n p (f : mor m p) X :
  @dptranspose T n p (dpmap (f T) X) = f _ (dptranspose X).
Proof. by rewrite -[in LHS](dptransposeK X) dpmap_dptranspose dptransposeK. Qed.

Lemma uncurry_dpmap (T : lmodType C) n m p q  (l : lens n m) (f : mor p q)
      (X : T ^^ p ^^ (n-m) ^^ m) :
  uncurry l (dpmap (dpmap (f T)) X) = dpmap (f T) (uncurry l X).
Proof. by apply/ffunP=> v; rewrite !ffunE. Qed.

Lemma dpmap_id T m (X : T ^^ m) : dpmap id X = X.
Proof. by apply/ffunP => v; rewrite ffunE. Qed.

(* Application of adjunction commutes with focus *)
Lemma applyU_focus (T : lmodType C) n m (l : lens n m) (f : endo m)
      (M : dsquare T n) :
  applyU (focus l f) M = uncurryds l (applyU f (curryds l M)).
Proof.
rewrite /applyU /curryds /uncurryds.
rewrite -(eq_dpmap (@focus_hconj_mor _ _ l f T)).
rewrite -2!morN.
set fc := hconj_mor f.
rewrite /= -(dpmap_compose (fc _)).
rewrite -(eq_dpmap (dpmap_dptranspose fc)).
rewrite (dpmap_compose (dptranspose (n:=n-m)) (dpmap (fc _))).
rewrite -(dpmap_compose (dptranspose (n:=m))).
rewrite (eq_dpmap (@dptransposeK _ (n-m) m)) dpmap_id.
rewrite -dpmap_compose -(eq_dpmap (dpmap_compose _ (uncurry l))).
rewrite -dpmap_compose -(eq_dpmap (dpmap_compose (curry dI l) _)).
rewrite -[X in uncurry l (dpmap (dpmap X) _)](focusE dI l fc _).
by rewrite uncurry_dpmap (focusE _ _ f).
Qed.

End density.
