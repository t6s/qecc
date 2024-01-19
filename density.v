From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import lens dpower unitary.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

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
Definition scalerv (T : lmodType C) (v : T) (x : Co) := x *: v.
Lemma scalerv_is_linear T v : linear (@scalerv T v).
Proof. by move=> x y z; rewrite /scalerv !linearE/= scalerA mulrC scalerDl. Qed.
Canonical scalerv_lin T v := Linear (@scalerv_is_linear T v).

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

(* The adjoint morphism (going through matrix representation) *)
Definition hadj_mor m n (f : mor m n) : mor n m :=
  mxmor (hadjts (mormx f)).

(* Focus and adjunction commute *)
Lemma focus_hadj_mor n m (l : lens n m) (f : endo m) :
  focus l (hadj_mor f) =e hadj_mor (focus l f).
Proof.
move=> /= T x.
apply/ffunP => /= v.
rewrite focusE !ffunE !mxmorE /=.
rewrite sum_ffunE /=.
rewrite (reindex_merge _ dI l) /=.
apply eq_bigr => vi _.
rewrite !ffunE /=.
under eq_bigr do rewrite !ffunE focusE !ffunE /= extract_merge extractC_merge.
under eq_bigr do rewrite curry_dpbasis -morN /=.
set flv := f _ _.
clearbody flv.
under eq_bigr do rewrite !ffunE.
rewrite (bigD1 (extract (lensC l) v)) //= eqxx scale1r.
rewrite big1 ?addr0 // => vj Hj.
by rewrite eq_sym (negbTE Hj) scale0r conjc0 scale0r.
Qed.

Section curryds.
Variables (T : lmodType C) (n m : nat) (l : lens n m).

Definition curryds (M : dsquare T n) : dsquare (dsquare T (n-m)) m :=
  [ffun v : m.-tuple I =>
   [ffun v' : m.-tuple I =>
    [ffun w : (n-m).-tuple I =>
     [ffun w' : (n-m).-tuple I => M (merge dI l v w) (merge dI l v' w')]]]].

Definition uncurryds (M : dsquare (dsquare T (n-m)) m) : dsquare T n :=
  [ffun v : n.-tuple I =>
   [ffun w : n.-tuple I =>
    M (extract l v) (extract l w) (extract (lensC l) v) (extract (lensC l) w)]].

Lemma uncurrydsK : cancel uncurryds curryds.
Proof.
move=> M; apply/ffunP=> v; apply/ffunP=> w; apply/ffunP=> v'; apply/ffunP=> w'.
by rewrite !ffunE !extract_merge !extractC_merge.
Qed.

Lemma currydsK : cancel curryds uncurryds.
Proof.
move=> M; apply/ffunP=> v; apply/ffunP=> w; by rewrite !ffunE !merge_extract.
Qed.

Lemma curryds_is_linear : linear curryds.
Proof. move=> x y z; do 4 apply/ffunP => ?; by rewrite !ffunE. Qed.
Canonical curryds_lin := Linear curryds_is_linear.

Lemma uncurryds_is_linear : linear uncurryds.
Proof. move=> x y z; do 2 apply/ffunP => ?; by rewrite !ffunE. Qed.
Canonical uncurryds_lin := Linear uncurryds_is_linear.
End curryds.

(* Application of adjunction commutes with focus *)
Lemma focusds_applyU (T : lmodType C) n m (l : lens n m) (f : endo m)
      (M : dsquare T n) :
  applyU (focus l f) M = uncurryds l (applyU f (curryds l M)).
Proof.
Abort.

End density.
