From mathcomp Require Import all_ssreflect all_algebra complex.
From HB Require Import structures.
Require Import lens dpower unitary.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

Section density.
Variable R : rcfType.
Let C : comRingType := R[i].
Let Co : lmodType C := C^o.
Variable I : finType.

(* Type of density matrices over C *)
Notation dpsquare n := 'dpM[I, C^o]_n.
Notation mor := (mor I C).
Notation endo n := (mor n n).
Notation "T '^^' n " := (dpower I n T).

Definition conjCo : Co -> Co := conjc.

(* Density matrix of a pure quantum state *)
Definition pure_density n (v : Co ^^ n) : dpsquare n :=
  dpmap (scalerv (dpmap conjCo v)) v.

(* Complex conjugate vector space functor *)
Definition conj_mor m n (f : mor m n) : mor m n :=
  dpmor (dpmap (dpmap conjCo) (mordp f)).

(* WIP: application of a morphism to a density matrix *)
(* U rho U^dagger *)
Definition applyU (T : lmodType C) m n (f : mor m n) :
  'dpM[T]_m -> 'dpM[T]_n := dpmap (conj_mor f _) \o f _.

Lemma dpmap_conjCo m n (f : mor m n) v :
  dpmap conjCo (f Co v) = conj_mor f Co (dpmap conjCo v).
Proof.
(* Does mathcomp 2.0 improve the type printed for v ? *)
apply/ffunP => vj.
rewrite dpmorE.
under eq_bigr do rewrite !ffunE /= -/Co.
rewrite [in LHS](decompose_scaler v) /conjCo.
rewrite !linear_sum !ffunE sum_ffunE linear_sum /=.
apply eq_bigr => w _.
rewrite [in RHS]/GRing.scale /= -rmorphM /=.
by rewrite linearE mulrC ffunE.
Qed.

Lemma applyU_pure m n (f : mor m n) (v : Co ^^ m) :
  applyU f (pure_density v) = pure_density (f _ v).
Proof.
apply/ffunP => vi.
by rewrite !ffunE /pure_density -morN !ffunE /= !linearE dpmap_conjCo.
Qed.

Lemma focus_conj_mor n m (l : lens n m) (f : endo m) :
  focus l (conj_mor f) =e conj_mor (focus l f).
Proof.
move=> /= T x.
apply/ffunP => /= v.
rewrite focusE !ffunE !dpmorE sum_ffunE (reindex_merge _ l) /=.
apply eq_bigr => vi _.
rewrite !ffunE /= /conjCo -/Co.
under eq_bigr do rewrite !ffunE focusE !ffunE /= curry_dpbasis.
under eq_bigr do rewrite -morN /= !ffunE extract_merge extractC_merge -/Co.
set flv := f _ _ _; clearbody flv.
rewrite (bigD1 (extract (lensC l) v)) //= eqxx scale1r big1 ?addr0 // => vj Hj.
by rewrite (negbTE Hj) scale0r conjc0 scale0r.
Qed.

(* The adjoint morphism (going through matrix representation) *)
Definition adjoint_mor m n (f : mor m n) : mor n m :=
  dpmor (dpadjoint (mordp f)).

(* Focus and adjunction commute *)
Lemma focus_adjoint_mor n m (l : lens n m) (f : endo m) :
  focus l (adjoint_mor f) =e adjoint_mor (focus l f).
Proof.
move=> /= T x.
apply/ffunP => /= v.
rewrite focusE !ffunE !dpmorE sum_ffunE (reindex_merge _ l) /=.
apply eq_bigr => vi _.
rewrite !ffunE -/Co.
under eq_bigr do rewrite !ffunE focusE !ffunE /= extract_merge extractC_merge.
under eq_bigr do rewrite curry_dpbasis -morN /= !ffunE -/Co.
set flv := f _ _; clearbody flv.
rewrite (bigD1 (extract (lensC l) v)) //= eqxx scale1r big1 ?addr0 // => vj Hj.
by rewrite eq_sym (negbTE Hj) scale0r conjc0 scale0r.
Qed.

Section curryds.
Variables (T : lmodType C) (n m : nat) (l : lens n m).

Definition curryds : 'dpM[T]_n -> 'dpM['dpM[T]_(n-m)]_m :=
  dpmap (@dptranspose _ _ _ (n-m) m) \o dpmap (dpmap (curry l))
  \o curry (I:=I) l.

Lemma currydsE M :
  curryds M =
  [ffun v : m.-tuple I =>
   [ffun v' : m.-tuple I =>
    [ffun w : (n-m).-tuple I =>
     [ffun w' : (n-m).-tuple I => M (merge l v w) (merge l v' w')]]]].
Proof.
apply/ffunP=> v; apply/ffunP=> v'; apply/ffunP=> w; apply/ffunP=> w'.
by rewrite !ffunE.
Qed.

Definition uncurryds : 'dpM['dpM[I,T]_(n-m)]_m -> 'dpM[T]_n :=
  uncurry l \o dpmap (dpmap (uncurry l)) \o dpmap (@dptranspose _ _ _ m (n-m)).

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

Definition focusds f M := uncurryds (f (curryds M)).
End curryds.

Lemma eq_dpmap (T1 T2 : lmodType C) m (f g : T1 -> T2) :
  f =1 g -> @dpmap I m T1 T2 f =1 dpmap g.
Proof. by move=> fg X; apply/ffunP => v; rewrite !ffunE fg. Qed.

Lemma dpmap_compose (T1 T2 T3 : lmodType C) m (f : T1 -> T2) (g : T2 -> T3) X :
  @dpmap I m _ _ (g \o f) X = dpmap g (dpmap f X).
Proof. by apply/ffunP=> v; rewrite !ffunE. Qed.

Lemma dpmap_dptranspose (T : lmodType C) m n p (f : mor m p) X :
  dpmap (f T) (@dptranspose _ _ T m n X) = dptranspose (f _ X).
Proof.
apply/ffunP=> v; apply/ffunP=> w /=.
rewrite ffunE.
move/naturalityP: (morN f) => [M Hf].
rewrite !Hf !ffunE !dpmorE sum_ffunE.
apply eq_bigr => vj _.
by rewrite !ffunE.
Qed.

Lemma dptranspose_dpmap (T : lmodType C) m n p (f : mor m p) X :
  @dptranspose _ _ T n p (dpmap (f T) X) = f _ (dptranspose X).
Proof. by rewrite -[in LHS](dptransposeK X) dpmap_dptranspose dptransposeK. Qed.

Lemma uncurry_dpmap (T : lmodType C) n m p q  (l : lens n m) (f : mor p q)
      (X : T ^^ p ^^ (n-m) ^^ m) :
  uncurry l (dpmap (dpmap (f T)) X) = dpmap (f T) (uncurry l X).
Proof. by apply/ffunP=> v; rewrite !ffunE. Qed.

Lemma dpmap_id T m (X : T ^^ m) : dpmap id X = X.
Proof. by apply/ffunP => v; rewrite ffunE. Qed.

(* Application of adjunction commutes with focus *)
Lemma applyU_focus (T : lmodType C) n m (l : lens n m) (f : endo m) M :
  applyU (T:=T) (focus l f) M = focusds l (applyU f) M.
Proof.
rewrite /focusds /applyU /curryds /uncurryds /=.
rewrite -(eq_dpmap (@focus_conj_mor _ _ l f T)) -2!morN.
set fc := conj_mor f.
rewrite /= -(dpmap_compose (fc _)) -(eq_dpmap (dpmap_dptranspose fc)).
rewrite (dpmap_compose (dptranspose (n:=n-m))).
rewrite -(dpmap_compose (dptranspose (n:=m))).
rewrite (eq_dpmap (@dptransposeK _ _ _ (n-m) m)) dpmap_id.
rewrite -dpmap_compose -(eq_dpmap (dpmap_compose _ _)).
rewrite -dpmap_compose -(eq_dpmap (dpmap_compose _ _)).
by rewrite -(focusE l fc _) uncurry_dpmap (focusE _ f).
Qed.

End density.
