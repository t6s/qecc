From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "f \v g" (at level 50, format "f  \v  g").
Reserved Notation "f =e g" (at level 70).
Reserved Notation "M1 '*t' M2" (at level 50).

(* Reduce a linear form *)
Definition linE :=
  (mulr0,mul0r,mulr1,mul1r,addr0,add0r,subr0,oppr0,scale0r,scale1r).

Section tensor_space.
Variables (I : finType) (dI : I) (R : comRingType).
Local Notation merge := (merge dI).

Definition dpower n T := {ffun n.-tuple I -> T}.
Definition morfun m n := forall T : lmodType R, dpower m T -> dpower n T.
Definition morlin m n :=
  forall T : lmodType R, {linear dpower m T -> dpower n T}.
Definition tmatrix m n := dpower m (dpower n R^o).
Notation tsquare n := (tmatrix n n).
Notation endofun n := (morfun n n).
Notation endolin n := (morlin n n).

(* Actually, need the property (naturality)
 forall (f : endo m) (T1 T2 : lmodType R) (h : {linear T1 -> T2}),
   map h \o f T1 = f T2 \o map h
which is equivalent to the fact f = nvendo M for a square matrix M : tsquare m.
*)
Definition dpmap m T1 T2 (f : T1 -> T2) (nv : dpower m T1)
  : dpower m T2 := [ffun v : m.-tuple I => f (nv v)].

Definition naturality m n (f : morlin m n) :=
  forall (T1 T2 : lmodType R) (h : {linear T1 -> T2}) (v : dpower m T1),
    dpmap h (f T1 v) = f T2 (dpmap h v).

Structure mor m n := Mor { morf :> morlin m n ; morN : naturality morf}.
Notation endo n := (mor n n).
Definition appmorlin m n (f : morlin m n) := fun T => f T.
Coercion appmorlin : morlin >-> Funclass.

Lemma dpmap_linear m (T1 T2 : lmodType R) (f : {linear T1 -> T2}) :
  linear (dpmap (m:=m) f).
Proof. move=> x y z /=; apply/ffunP => vi; by rewrite !ffunE !linearE. Qed.
Canonical dpmap_lin m T1 T2 f := Linear (@dpmap_linear m T1 T2 f).

Lemma dpmap_comp m (T1 T2 T3 : lmodType R) (f : T2 -> T3) (g : T1 -> T2) :
  dpmap (m:=m) (f \o g) =1 dpmap f \o dpmap g.
Proof. by move=> v; apply/ffunP => vi; rewrite !ffunE. Qed.

Lemma dpmap_scale n (x : R^o) (v : dpower n R^o) :
  dpmap ( *:%R^~ x) v = x *: v.
Proof. apply/ffunP => i; by rewrite !ffunE [LHS]mulrC. Qed.

Definition dpcast n m T (H : n = m) (v : dpower n T) : dpower m T :=
  [ffun vi => v (cast_tuple (esym H) vi)].

Lemma dpcastE T n v (H : n = n) : dpcast (T:=T) H v = v.
Proof. by apply/ffunP => vi; rewrite !ffunE cast_tupleE. Qed.

Lemma dpcastK T n m (H : n = m) (t : dpower n T) :
  dpcast (esym H) (dpcast H t) = t.
Proof. by apply/ffunP => v; rewrite !ffunE; f_equal; apply/val_inj. Qed.

Lemma dpcast_linear (T : lmodType R) n m (H : n = m) : linear (dpcast (T:=T) H).
Proof. move=> x y z /=; apply/ffunP => vi; by rewrite !ffunE. Qed.

Lemma map_dpcastE T m n (H : n = n) v :
  dpmap (m:=m) (dpcast (T:=T) H) v = v.
Proof. by apply/ffunP => w /=; rewrite !ffunE dpcastE. Qed.

Definition morlin_dpcast n m (H : n = m) : morlin n m :=
  fun T : lmodType R => Linear (dpcast_linear (T:=T) H).
Canonical morlin_dpcast.

Lemma dpcastN m n (H : n = m) : naturality (morlin_dpcast H).
Proof. move=> T1 T2 h v; apply/ffunP => vi; by rewrite !ffunE. Qed.
Definition mor_dpcast n m (H : n = m) := Mor (dpcastN H).

Definition eq_mor m n (f1 f2 : mor m n) := forall T, f1 T =1 f2 T.
Notation "f1 =e f2" := (eq_mor f1 f2).

Definition tsmor_fun m n (M : tmatrix n m) : morfun m n :=
  fun T v =>
    [ffun vi : n.-tuple I => \sum_(vj : m.-tuple I) (M vi vj : R) *: v vj].

Lemma tsmor_is_linear m n M T : linear (@tsmor_fun m n M T).
Proof.
move=> /= x y z; apply/ffunP => /= vi; rewrite !ffunE.
rewrite scaler_sumr -big_split; apply eq_bigr => /= vj _.
by rewrite !ffunE scalerDr !scalerA mulrC.
Qed.

Definition tsmorfun m n (M : tmatrix n m) : morlin m n :=
  fun T => Linear (@tsmor_is_linear m n M T).
Definition tsmorlin m n (M : tmatrix n m) : morlin m n :=
  locked (tsmorfun M).

Lemma tsmorN m n M : naturality (@tsmorlin m n M).
Proof.
move=> T1 T2 h /= v; apply/ffunP => /= vi.
rewrite /tsmorlin -lock !ffunE linear_sum; apply eq_bigr => vj _.
by rewrite linearZ_LR !ffunE.
Qed.

Definition tsmor m n (M : tmatrix n m) : mor m n :=
  Mor (tsmorN M).

Lemma tsmorE m n (M : tmatrix n m) T v vi :
  tsmor M T v vi = \sum_(vj : m.-tuple I) (M vi vj : R) *: v vj.
Proof. by rewrite /tsmor /tsmorlin /= -lock !ffunE. Qed.

Definition dpbasis m (vi : m.-tuple I) : dpower m R^o :=
  [ffun vj => (vi == vj)%:R].

Definition morts m n (f : morlin m n) : tmatrix n m :=
  [ffun vi => [ffun vj => f _ (dpbasis vj) vi]].

Lemma morts_eq m n (f g : mor m n) : f =e g -> morts f = morts g.
Proof. by move=> fg; apply/ffunP=>vi; apply/ffunP=>vj; rewrite !ffunE fg. Qed.

Lemma sum_muleqr (A : finType) (S : comRingType) (F : A -> S) (v : A) :
  \sum_a F a * (v == a)%:R = F v.
Proof.
rewrite (bigD1 v) //= big1 ?(addr0,eqxx,mulr1) // => a av.
by rewrite eq_sym (negbTE av) mulr0.
Qed.

Lemma sum_dpbasisKo n (vi : n.-tuple I) (F : dpower n R) :
  (\sum_vj (F vj *: dpbasis vi vj) = F vi).
Proof. under eq_bigr do rewrite !ffunE. by rewrite sum_muleqr. Qed.

Lemma tsmorK m n : cancel (@tsmor m n) (@morts m n).
Proof.
move=> M; apply/ffunP => vi; apply/ffunP=> vj.
by rewrite !ffunE !tsmorE sum_dpbasisKo.
Qed.

Lemma dpbasisC m (vi vj : m.-tuple I) : dpbasis vi vj = dpbasis vj vi.
Proof. by rewrite !ffunE eq_sym. Qed.

Lemma sum_dpbasisK n (T : lmodType R) (vi : n.-tuple I) (F : dpower n T) :
  (\sum_vj (dpbasis vi vj *: F vj) = F vi).
Proof.
rewrite (bigD1 vi) //= !ffunE eqxx big1 ?(addr0,scale1r) //.
move=> vk; rewrite !ffunE eq_sym => /negbTE ->; by rewrite scale0r.
Qed.

Lemma decompose_dpower m (T : lmodType R) (v : dpower m T) :
  v = (\sum_i dpmap ( *:%R^~ (v i)) (dpbasis i)).
Proof.
apply/ffunP => vi; rewrite sum_ffunE -[LHS]sum_dpbasisK /=.
by apply eq_bigr => vj _; rewrite [RHS]ffunE dpbasisC.
Qed.

Lemma mortsK n m (f : mor m n) : tsmor (morts f) =e f.
Proof.
move=> T v.
rewrite [in RHS](decompose_dpower v) linear_sum.
apply/ffunP => /= vi; rewrite tsmorE !ffunE sum_ffunE /=.
apply eq_bigr => /= vj _; rewrite !ffunE.
set h : R^o -> T := *:%R^~ _.
have hlin : linear h by move=> x y z; rewrite /h scalerDl !scalerA.
by rewrite -(morN f (Linear hlin) (dpbasis vj)) ffunE.
Qed.

Lemma naturalityP m n (f : morlin m n) :
  naturality f <-> exists M, forall T, f T =1 tsmor M T.
Proof.
split.
- move=> Nf. by exists (morts f) => v T; rewrite (mortsK (Mor Nf)).
- case=> M Nf T1 T2 h v. by rewrite !Nf tsmorN.
Qed.

Let Ro := [lmodType R of R^o].
Lemma lift_mor_eq m n (f g : mor m n) :
  f Ro =1 g Ro -> f =e g.
Proof.
move=> fg T v.
rewrite (decompose_dpower v) !linear_sum.
apply eq_bigr => i _.
set scl := *:%R^~ _.
have Hlin : linear ( scl : Ro -> T).
  by move=> x y z /=; rewrite /scl !scalerDl scalerA.
by rewrite -(morN f (Linear Hlin)) -(morN g (Linear Hlin)) fg.
Qed.

Lemma decompose_scaler n (v : dpower n Ro) :
  v = \sum_i v i *: dpbasis i.
Proof.
apply/ffunP => vi; rewrite !sum_ffunE.
rewrite -[LHS]sum_dpbasisKo.
by apply eq_bigr => vj _; rewrite [RHS]ffunE dpbasisC.
Qed.

Definition ket_bra m (ket : dpower m R^o) (bra : dpower m R^o) : tsquare m :=
  [ffun vi => ket vi *: bra].

Definition mults m n p (M1 : tmatrix n m) (M2 : tmatrix m p) : tmatrix n p :=
  [ffun vi => [ffun vj => \sum_vk M1 vi vk * M2 vk vj]].

Notation "M1 '*t' M2" := (mults M1 M2).

Lemma multsA m n p q (M1 : tmatrix n m) (M2 : tmatrix m p) (M3 : tmatrix p q) :
  (M1 *t M2) *t M3 = M1 *t (M2 *t M3).
Proof.
apply/ffunP => vi; apply/ffunP => vj; rewrite !ffunE.
under eq_bigr do rewrite !ffunE big_distrl /=.
rewrite exchange_big /=; apply eq_bigr => vk _.
by rewrite !ffunE big_distrr /=; apply eq_bigr => vl _; rewrite mulrA.
Qed.

Definition idts m : tsquare m := [ffun vi => dpbasis vi].
Definition idmorlin n : morlin n n := fun T => GRing.idfun_linear _.
Lemma idmorN n : naturality (idmorlin n).
Proof. done. Qed.
Definition idmor n := Mor (@idmorN n).

Lemma idmorE n : idmor n =e tsmor (idts n).
Proof.
move=> T v; apply/ffunP => vi.
rewrite /idmor tsmorE.
under eq_bigr do rewrite ffunE; by rewrite sum_dpbasisK.
Qed.

Lemma mor_dpcastE n (H : n = n) : mor_dpcast H =e idmor n.
Proof. by move=> T v; rewrite /mor_dpcast /= dpcastE. Qed.

Definition transpose_tsquare m (M : tsquare m) : tsquare m :=
  [ffun vi => [ffun vj => M vj vi]].
Lemma transpose_tsquare_involutive m : involutive (@transpose_tsquare m).
Proof. move=> M. apply/ffunP => vi. apply/ffunP => vj. by rewrite !ffunE. Qed.

(* Tensor product of tsquare matrices *)
Section tensor_tsquare.
Variables m n : nat.

Definition tensor_tsquare (M1 : tsquare m) (M2 : tsquare n) : tsquare (m + n) :=
  [ffun vi => [ffun vj =>
     M1 (extract (lens_left m n) vi) (extract (lens_left m n) vj) *
     M2 (extract (lens_right m n) vi) (extract (lens_right m n) vj)]].

Lemma tensor_linearl (M2 : tsquare n) : linear (tensor_tsquare ^~ M2).
Proof.
move=> x M M'. apply/ffunP => vi. apply/ffunP => vj.
by rewrite !ffunE /= mulrDl scalerA.
Qed.

Lemma tensor_linearr (M1 : tsquare m) : linear (tensor_tsquare M1).
Proof.
move=> x M M'. apply/ffunP => vi. apply/ffunP => vj.
by rewrite !ffunE /= mulrDr !scalerA (mulrC x) -scalerA.
Qed.
End tensor_tsquare.

Section curry.
Variables (T : lmodType R) (n m : nat) (l : lens n m).

Definition curry (st : dpower n T) : dpower m (dpower (n-m) T) :=
  [ffun v : m.-tuple I =>
   [ffun w : (n-m).-tuple I => st (merge l v w)]].

Definition uncurry (st : dpower m (dpower (n-m) T)) : dpower n T :=
  [ffun v : n.-tuple I => st (extract l v) (extract (lensC l) v)].

Lemma uncurryK : cancel uncurry curry.
Proof.
move=> v; apply/ffunP => v1; apply/ffunP => v2.
by rewrite !ffunE extract_merge extractC_merge.
Qed.

Lemma curryK : cancel curry uncurry.
Proof. move=> v; apply/ffunP => w; by rewrite !ffunE merge_extract. Qed.

Lemma curry_is_linear : linear curry.
Proof. move=>x y z; apply/ffunP=>vi; apply/ffunP =>vj; by rewrite !ffunE. Qed.
Canonical curry_lin := Linear curry_is_linear.

Lemma uncurry_is_linear : linear uncurry.
Proof. move => x y z; apply/ffunP=> vi; by rewrite !ffunE. Qed.
Canonical uncurry_lin := Linear uncurry_is_linear.

(* Special cases of curry/uncurry *)
Definition curry0 (v : T) : dpower 0 T := [ffun _ => v].
Definition curryn0 : dpower n T -> dpower n (dpower 0 T) :=
  dpmap curry0.
Definition uncurry0 (v : dpower 0 T) : T := v [tuple].

Lemma curryn0E :
  curryn0 = fun v => [ffun vi => [ffun _ => v vi]].
Proof. reflexivity. Qed.

Lemma curry0_is_linear : linear curry0.
Proof. move=> x y z. apply/ffunP => vi. by rewrite !ffunE. Qed.
Lemma curryn0_is_linear : linear curryn0.
Proof. move=> x y z. apply/ffunP=> vi. apply/ffunP=> vj. by rewrite !ffunE. Qed.
Lemma uncurry0_is_linear : linear uncurry0.
Proof. move=> x y z. by rewrite /uncurry0 !ffunE. Qed.
Canonical curry0_lin := Linear curry0_is_linear.
Canonical curryn0_lin := Linear curryn0_is_linear.
Canonical uncurry0_lin := Linear uncurry0_is_linear.
End curry.


Section inner_prod_coprod.
Variable n : nat.
Let cast_uncurry T := dpmap (m:=n) (dpcast (T:=T) (esym (addKn n n))).
Definition M_inner_prod (M : tsquare n) :=
  tsmor (curry0 (uncurry (lens_left n n) (cast_uncurry M))).
Definition M_inner_coprod (M : tsquare n) :=
  tsmor (curryn0 (uncurry (lens_left n n) (cast_uncurry M))).
Definition inner_prod : mor (n+n) 0 := M_inner_prod (idts _).
Definition inner_coprod : mor 0 (n+n) := M_inner_coprod (idts _).
End inner_prod_coprod.

Section dpaux.
Variables (k : nat) (T : lmodType R).

Definition dpall (v : T) : dpower k T := [ffun => v].
Lemma dpall_linear : linear dpall.
Proof. move=> a x y; apply/ffunP => i; by rewrite !ffunE. Qed.
Canonical dpall_lin := Linear dpall_linear.

Definition dpsum (v : dpower k T) : T := \sum_i v i.
Lemma dpsum_linear : linear dpsum.
Proof.
rewrite/dpsum => a x y /=. rewrite scaler_sumr -big_split /=.
apply eq_bigr=> i _; by rewrite !ffunE.
Qed.
Canonical dpsum_lin := Linear dpsum_linear.

Variable vi : k.-tuple I.
Definition dpsingle (v : T) : dpower k T :=
  [ffun vj => (vi == vj)%:R *: v].
Lemma dpsingle_linear : linear dpsingle.
Proof. move=> a x y; apply/ffunP => i; by rewrite !ffunE /= linearP. Qed.
Canonical dpsingle_lin := Linear dpsingle_linear.

Definition dpsel (v : dpower k T) := v vi.
Lemma dpsel_is_linear : linear dpsel.
Proof. by move=> x y z; rewrite /dpsel !ffunE. Qed.
Canonical dpsel_lin := Linear dpsel_is_linear.
End dpaux.

Lemma dp_single_basis n (vi : n.-tuple I) : dpsingle vi (1:R^o) = dpbasis vi.
Proof. apply/ffunP => vj. by rewrite !ffunE [LHS]mulr1. Qed.

Section partial_trace.
Variables (n m : nat) (l : lens n m) (f : endo n).

Definition ptracefun (T : lmodType R) (v : dpower m T) : dpower m T :=
  \sum_(vi : (n-m).-tuple I)
    (dpmap (dpsel vi) \o curry l \o f T
       \o uncurry l \o dpmap (dpsingle vi)) v.
(* dpfilter l vi \o f T \o dpmerge l vi ? *)
(* Hopf algebra ? *)

Lemma ptrace_is_linear T : linear (@ptracefun T).
Proof.
move=> a x y; rewrite /ptracefun !linear_sum -big_split /=.
apply eq_bigr => vi _; by rewrite !linearP.
Qed.

Definition ptracelin : morlin m m := fun T => Linear (@ptrace_is_linear T).

Lemma uncurry_dpsingle_naturality vi :
 naturality (fun T => [linear of uncurry (T:=T) l \o dpmap (dpsingle vi)]).
Proof. by move=> T1 T2 h v; apply/ffunP => i; rewrite !ffunE linearE. Qed.

Lemma dpsel_curry_naturality vi :
  naturality (fun T => [linear of dpmap (dpsel vi) \o curry (T:=T) l]).
Proof. by move=> T1 T2 h v; apply/ffunP => i; rewrite /dpsel !ffunE. Qed.

Lemma ptrace_naturality : naturality ptracelin.
Proof.
move=> T1 T2 h v.
rewrite /= /ptracefun linear_sum.
apply eq_bigr => vi _ /=.
move: (dpsel_curry_naturality vi h) => /= ->.
rewrite (morN f).
by move: (uncurry_dpsingle_naturality vi h v) => ->.
Qed.

Definition ptrace : endo m := Mor ptrace_naturality.

Definition antifocus T := [linear of curry l \o f T \o uncurry l].
(* Lemma antifocus_naturality :
  naturality f -> naturality antifocus. *)
End partial_trace.

Lemma ptrace_comp n m p (l1 : lens n m) (l2 : lens m p) (f : endo n) :
  ptrace (lens_comp l1 l2) f =e ptrace l2 (ptrace l1 f).
Proof.
move=> T /= v.
apply/ffunP => /= vi.
rewrite /ptracefun !sum_ffunE /ptracefun.
rewrite [LHS](reindex_merge _ dI (lensC_notin_l l1 l2)) exchange_big /=.
rewrite (reindex_inj (@extract_inj _ (lens_perm (lensC_in_l l1 l2)) _)).
rewrite (reindex _
    (onW_bij _ (cast_tuple_bij _ (esym (cast_lensC_notin_l' l1 l2))))) /=.
apply eq_bigr => /= vj _.
rewrite !linear_sum sum_ffunE.
apply eq_bigr => /= vk _.
rewrite /dpsel !ffunE.
f_equal; last by rewrite merge_lensC_notin_l; apply: merge_comp.
f_equal.
apply/ffunP => vh.
rewrite !ffunE -!extract_comp scalerA -natrM mulnb.
congr ((_ : bool)%:R *: _).
rewrite -[extract (lensC _) vh](merge_extract dI (lensC_notin_l l1 l2)).
rewrite merge_inj_eq -extract_comp lensC_notin_l_comp -extract_comp.
congr andb.
rewrite -(inj_eq (f:=cast_tuple (cast_lensC_notin_l' l1 l2))); last first.
  move=> x y /(f_equal val) => H; exact/val_inj.
rewrite (_ : cast_tuple _ _ = vj); last by apply val_inj.
rewrite -[in LHS]
         (inj_eq (extract_inj (l:=lens_perm (lensC_in_l l1 l2)) (T:=I))).
congr (_ == _).
rewrite cast_tuple_extract -extract_comp cast_lens_comp.
by rewrite -lensC_in_l_comp lens_compA lensC_lensC_notin_l_perm.
Qed.

Section focus.
Variables (n m : nat) (l : lens n m).
Section focuslin.
Variable tr : endo m.
Definition focus_fun : endofun n :=
  fun T (v : dpower n T) => uncurry l (tr _ (curry l v)).

Lemma focus_is_linear T : linear (@focus_fun T).
Proof.
move=> x y z.
apply/ffunP => vi; rewrite !ffunE.
have -> : curry l (T := T) = Linear (curry_is_linear l (T:=T)) by [].
by rewrite !linearP !ffunE.
Qed.

Definition focuslin : morlin n n :=
  fun T => Linear (@focus_is_linear T).
End focuslin.

Lemma focusN f : naturality (focuslin f).
Proof.
case/naturalityP: (morN f) => M NM.
apply/naturalityP.
exists (morts (focuslin (tsmor M))).
move=> T /= v; apply/ffunP => /= vi.
rewrite tsmorE !ffunE NM tsmorE sum_ffunE.
under [RHS]eq_bigr do rewrite !ffunE tsmorE sum_ffunE scaler_suml.
rewrite exchange_big /=; apply eq_bigr => vj _.
rewrite [in LHS](decompose_dpower v) !ffunE sum_ffunE scaler_sumr.
by apply eq_bigr => i _; rewrite !ffunE !scalerA.
Qed.

Definition focus f := locked (Mor (focusN f)).

Lemma focusE f T : focus f T = @focus_fun f T :> (dpower _ _ -> _).
Proof. by rewrite /focus -lock. Qed.

Lemma curry_dpbasis (vi : n.-tuple I) :
  curry l (dpbasis vi) =
  dpmap (dpsingle (extract (lensC l) vi)) (dpbasis (extract l vi)).
Proof.
apply/ffunP => vj; apply/ffunP => vk; rewrite !ffunE.
case/boolP: (vi == _) => /eqP Hvi.
  by rewrite Hvi extractC_merge extract_merge !eqxx /= scale1r.
case/boolP: (_ == vk) => /eqP Hvk; last by rewrite scale0r.
case/boolP: (_ == vj) => /eqP Hvj; last by rewrite scaler0.
by elim Hvi; rewrite -Hvk -Hvj merge_extract.
Qed.

Definition dpmerge vi : {linear dpower m R^o -> dpower n R^o} :=
  locked [linear of uncurry l \o dpmap (dpsingle (extract (lensC l) vi))].

Lemma dpmergeE vi v :
  dpmerge vi v = uncurry l (dpmap (dpsingle (extract (lensC l) vi)) v).
Proof. by rewrite /dpmerge -lock. Qed.

Lemma focus_dpbasis f (vi : n.-tuple I) :
  focus f Ro (dpbasis vi) = dpmerge vi (f Ro (dpbasis (extract l vi))).
Proof.
apply/ffunP => v.
by rewrite focusE !ffunE curry_dpbasis -(morN f) dpmergeE !ffunE.
Qed.

Lemma dpmerge_dpbasis (vi : n.-tuple I) (vj : m.-tuple I) :
  dpmerge vi (dpbasis vj) = dpbasis (merge l vj (extract (lensC l) vi)).
Proof.
apply/ffunP => vk.
rewrite dpmergeE !ffunE.
case/boolP: (_ == vk) => /eqP Hvk.
  by rewrite -Hvk extractC_merge extract_merge !eqxx scale1r.
case/boolP: (_ == extract _ _) => /eqP Hvi; last by rewrite scale0r.
case/boolP: (_ == _) => /eqP Hvj; last by rewrite scaler0.
elim Hvk; by rewrite Hvi Hvj merge_extract.
Qed.

Lemma focus_dpbasis_id (f : endo m) v :
  f _ (dpbasis (extract l v)) = dpbasis (extract l v) ->
  focus f _ (dpbasis v) = dpbasis v.
Proof.
move=> Htr.
by rewrite focus_dpbasis // Htr dpmerge_dpbasis merge_extract.
Qed.
End focus.

Section asym_focus.
Variables (n m p : nat) (l : lens (m+n) m) (l' : lens (p+n) p) (tr : mor m p).

Lemma addKn_any : (m + n - m = p + n - p)%N.
Proof. by rewrite !addKn. Qed.

Definition asym_focus_fun : morfun (m + n) (p + n) :=
  fun T (v : dpower (m + n) T) =>
    uncurry l' (dpmap (dpcast addKn_any) (tr _ (curry l v))).

Lemma asym_focus_is_linear T : linear (@asym_focus_fun T).
Proof.
move=> x y z.
apply/ffunP => vi. rewrite !ffunE.
have -> : curry l (T := T) = Linear (curry_is_linear l (T:=T)) by [].
by rewrite !linearP !ffunE.
Qed.

Definition asym_focuslin : morlin (m + n) (p + n) :=
  fun T => Linear (@asym_focus_is_linear T).
End asym_focus.

Lemma asym_focusN n m p l l' tr :
  naturality (@asym_focuslin n m p l l' tr).
Proof.
case/naturalityP: (morN tr) => M /= NM; apply/naturalityP.
exists (morts (asym_focuslin l l' (tsmor M))).
move=> T /= v; apply/ffunP => /= vi; rewrite tsmorE !ffunE NM tsmorE sum_ffunE.
under [RHS]eq_bigr do rewrite !ffunE tsmorE sum_ffunE scaler_suml.
rewrite exchange_big /=; apply eq_bigr => vj _.
rewrite [in LHS](decompose_dpower v) !ffunE sum_ffunE scaler_sumr.
by apply eq_bigr => i _; rewrite !ffunE !scalerA.
Qed.

Definition asym_focus n m p l l' tr := Mor (@asym_focusN n m p l l' tr).

Lemma asym_focus_sym (m n : nat) (l : lens (m+n) m) (f : mor m m) :
  asym_focus l l f =e focus l f.
Proof.
move=> T v /=; rewrite /= /asym_focus_fun /=.
by rewrite map_dpcastE focusE.
Qed.

Section focus_props.
Variables (n m p : nat) (l : lens n m).

(* Identity *)
Lemma focusI tr : focus (lens_id n) tr =e tr.
Proof.
case/naturalityP: (morN tr) => [f Hf] T v.
rewrite /= focusE.
apply/ffunP => /= vi.
rewrite /focus_fun !{}Hf {tr} !ffunE !tsmorE sum_ffunE.
apply eq_bigr => vj _; rewrite !ffunE extract_lens_id.
congr (_ *: v _).
apply eq_from_tnth => i; by rewrite tnth_mktuple index_lens_id -tnth_nth.
Qed.

(* Equality *)
Lemma focus_eq (f1 f2 : endo m) : f1 =e f2 -> focus l f1 =e focus l f2.
Proof. move=> Heq T v /=; by rewrite 2!focusE /= /focus_fun Heq. Qed.

(* Identity morphism *)
Lemma focus_idmor : focus l (idmor m) =e idmor n.
Proof. by move=> T v; rewrite /= focusE /= /focus_fun /= curryK. Qed.

(* Vertical composition of morphisms *)
Section comp_mor.
Variables (r q s : nat) (tr : mor q s) (tr' : mor r q).
Definition comp_morlin : morlin r s :=
  fun A => GRing.comp_linear (tr A) (tr' A).

Lemma comp_morN : naturality comp_morlin.
Proof. move=> T1 T2 f v; by rewrite (morN tr) (morN tr'). Qed.

Definition comp_mor := Mor comp_morN.
End comp_mor.
Notation "f \v g" := (comp_mor f g).

Definition cast_mor m2 n2 m1 n1 (Hm : m1 = m2) (Hn : n1 = n2) (f : mor m1 n1)
  : mor m2 n2 :=
  mor_dpcast Hn \v f \v mor_dpcast (esym Hm).

Section comp_mor_facts.
Variables (q : nat) (f : mor m n) (g : mor n p) (h : mor p q).

Lemma comp_morA : h \v (g \v f) =e (h \v g) \v f.
Proof. by []. Qed.

Lemma comp_morE T v : (g \v f) T v = g T (f T v).
Proof. by []. Qed.
End comp_mor_facts.

Lemma focus_comp r q (tr tr' : endo q) (lq : lens r q) :
  focus lq (tr \v tr') =e focus lq tr \v focus lq tr'.
Proof.
move=> T v; apply/ffunP => /= vi.
by rewrite !focusE /focus_fun /= uncurryK.
Qed.

Lemma tsmor_comp (M : tmatrix n m)  (N : tmatrix m p) :
  tsmor (mults M N) =e tsmor M \v tsmor N.
Proof.
move=> T v; apply/ffunP => vi; rewrite !tsmorE.
under eq_bigr do rewrite !ffunE !scaler_suml.
rewrite exchange_big /=.
apply eq_bigr => vk _; rewrite tsmorE !(scaler_suml,scaler_sumr).
by apply eq_bigr => vj _; rewrite scalerA.
Qed.

(* Horizontal composition of endomorphisms *)
Lemma focusC (l' : lens n p) tr tr' :
  [disjoint l & l'] ->
  focus l tr \v focus l' tr' =e focus l' tr' \v focus l tr.
Proof.
case/naturalityP: (morN tr) (morN tr') => f Hf /naturalityP [f' Hf'].
move => Hdisj T v /=; rewrite !focusE.
apply/ffunP => /= vi.
rewrite /focus_fun !{}Hf !{}Hf' {tr tr'} !ffunE !tsmorE !sum_ffunE.
under eq_bigr do rewrite !ffunE tsmorE !sum_ffunE scaler_sumr.
rewrite exchange_big; apply eq_bigr => /= vj _.
rewrite !ffunE tsmorE !sum_ffunE scaler_sumr; apply eq_bigr => /= vk _.
rewrite !ffunE !scalerA [in RHS]mulrC.
congr (f _ vk * f' _ vj *: v _).
- by rewrite extract_merge_disjoint // disjoint_sym.
- by rewrite extract_merge_disjoint.
- by rewrite !merge_extractC inject_disjointC.
Qed.

Lemma focus_tensor (M : tsquare m) (M' : tsquare n) :
  focus (lens_left m n) (tsmor M) \v focus (lens_right m n) (tsmor M') =e
  tsmor (tensor_tsquare M M').
Proof.
move=> T v; apply/ffunP => /= vi.
rewrite focusE !(ffunE,tsmorE) !sum_ffunE.
under eq_bigr do rewrite !focusE !(ffunE,tsmorE) !sum_ffunE scaler_sumr.
rewrite reindex_left_right.
apply eq_bigr => /= vj _; rewrite !ffunE !merge_extractC.
rewrite extract_inject; last by rewrite disjoint_sym lens_left_right_disjoint.
by rewrite scalerA inject_all // lens_left_right_disjoint.
Qed.

(* Associativity of actions of lenses *)
Lemma focusM (l' : lens m p) tr :
  focus (lens_comp l l') tr =e focus l (focus l' tr).
Proof.
case/naturalityP: (morN tr) => f Hf T v.
rewrite /= !focusE /focus_fun /= !Hf.
rewrite /= !focusE /focus_fun /= !Hf {tr Hf}.
apply/ffunP => /= vi.
rewrite !ffunE !tsmorE (extract_lensC_comp dI) -!extract_comp.
rewrite -[in RHS]lensC_in_l_comp -(lensC_notin_l_comp l l') !sum_ffunE.
apply eq_bigr => /= vj _; rewrite !ffunE.
congr (_ *: v _).
exact: merge_comp.
Qed.

(* Variant for disjoint lenses, used in unitary.v *)
Variable T : lmodType R.
Lemma focus_others (l' : lens (n-m) p) (f : endo p) (t : dpower n T) :
  focus (lens_comp (lensC l) l') f T t =
  uncurry l (dpmap (m:=m) (focus l' f T) (curry l t)).
  (* parametricity prevents writing it this way:
     focus l (fun _ => Linear (dpmap_linear (focus l' f T))) T t. *)
Proof.
case/naturalityP: (morN f) => M Hf; apply/ffunP => vi.
rewrite /= !focusE !ffunE /= -!extract_comp !Hf !tsmorE /= !sum_ffunE.
apply eq_bigr => vj _; by rewrite !ffunE merge_comp_others.
Qed.
End focus_props.
Notation "f \v g" := (comp_mor f g).
Notation tsapp l M := (focus l (tsmor M)).

(* Too complicated
Lemma asym_focusC n m p n' m' p' (l1 : lens (m+n) m) (l2 : lens (p+n) p)
      (l3 : lens (m'+n') m') (l4 : lens (p'+n') p') (tr : mor m p)
      (tr' : mor m' p') :
  [disjoint map val l2 & map val l3] -> p + n = m' + n' ->
  asym_focus l3 l4 tr' \v asym_focus l1 l2 tr \v =e ???
*)

Lemma asym_focusC n m p (l1 : lens (m+n) m) (l2 : lens (p+n) p)
      (g : mor m p) (f : endo n) :
  focus (cast_lens (addKn _ _) (lensC l2)) f \v asym_focus l1 l2 g =e
  asym_focus l1 l2 g \v focus (cast_lens (addKn _ _) (lensC l1)) f.
Proof.
case/naturalityP: (morN f) (morN g) => Mf Hf /naturalityP [Mg Hg] T v /=.
rewrite !focusE /=.
apply/ffunP => /= vi.
rewrite /focus_fun /asym_focus_fun !{}Hf {f} !{}Hg {g}.
rewrite !ffunE !tsmorE !sum_ffunE.
under eq_bigr do rewrite !ffunE tsmorE !sum_ffunE scaler_sumr.
rewrite exchange_big; apply eq_bigr => /= vj _.
rewrite !ffunE tsmorE !sum_ffunE scaler_sumr; apply eq_bigr => /= vk _.
rewrite !ffunE !scalerA [in RHS]mulrC.
congr (Mf _ vk * Mg _ vj *: v _).
- apply val_inj => /=.
  set w := cast_tuple _ _.
  by move/(f_equal val): (extractC_merge dI l1 vj w) => /= ->.
- rewrite extract_merge_disjoint //.
  apply/pred0P => /= i.
  rewrite simpl_predE /= andbC /=.
  case Hi: (i \in l2) => //=.
  by rewrite mem_lensE /= mem_lensC Hi.
- rewrite !merge_extractC.
  apply eq_from_tnth => i /=.
  rewrite !tnth_mktuple /=.
  case/boolP: (i \in l1) => Hil1. 
    rewrite !nth_lens_index.
    rewrite nth_default // memNindex ?(mem_lensC,Hil1) //.
    by rewrite (eqP (size_lensC l1)) size_tuple addKn.
  rewrite !nth_lens_out //.
  move/negbF: Hil1.
  rewrite -mem_lensC => /negbFE.
  have -> : seq_lensC l1 = cast_lens (addKn _ _) (lensC l1) by [].
  move=> Hil1.
  rewrite !nth_lens_index (tnth_nth dI).
  congr nth.
  have -> : seq_lensC l2 = cast_lens (addKn _ _) (lensC l2) by [].
  transitivity (map_tuple (tnth (inject (cast_lens (addKn p n) (lensC l2))
                           vi vk)) (cast_lens (addKn p n) (lensC l2))) => //.
  apply f_equal, eq_from_tnth => j.
  rewrite tnth_map /= tnth_mktuple nth_lens_index ?mem_tnth // => H.
  rewrite -(nth_lens_index H dI) nthK /=.
  + by rewrite -?tnth_nth.
  + by rewrite uniq_lensC.
  + by rewrite (eqP (size_lensC _)) addKn inE.
Qed.

Lemma focus_tensor' n m p (l : lens n m) (l' : lens n p) (H : [disjoint l & l'])
      (M : tsquare m) (M' : tsquare p) :
  tsapp l M \v tsapp l' M' =e tsapp (lens_cat H) (tensor_tsquare M M').
Proof.
rewrite {1}(lens_comp_right H) {1}(lens_comp_left H) => T v /=.
rewrite focusM (focusM _ _ (tsmor M')).
have /= <- := focus_comp _ _ _ v.
move: T v; exact/focus_eq/focus_tensor.
Qed.

(*
Section narrow.
Variables (n m : nat) (l : lens n m).
Definition narrow_in (T : lmodType R) (st : dpower m T) : dpower n T :=
  [ffun v : n.-tuple I => st (extract l v)].
Definition narrow_out (T : lmodType R) (st : dpower n T) : dpower m T :=
  [ffun v : m.-tuple I => st (inject l [tuple of nseq n dI] v)].
Definition narrow (f : endofun n) : endofun m :=
  fun T (v : dpower m T) => narrow_out (f T (narrow_in v)).
End narrow.
Lemma narrow_focus n m p (l : lens n m) (l' : lens n p)
      (H : [disjoint l & l']) f (T : lmodType R) v :
  narrow (lensC l) (focus l' f) v =
  focus (lmake_comp H) f T v.
Proof.
apply/ffunP => vi.
rewrite /narrow !focusE /= !ffunE.
Abort.
*)
End tensor_space.

Notation "f1 =e f2" := (eq_mor f1 f2).
Notation "f \v g" := (comp_mor f g).
Notation "M1 '*t' M2" := (mults M1 M2).
Notation tsapp l M := (focus l (tsmor M)).

(* Conversion between dpower and vector space *)

Section index_of_vec_bij.
Local Open Scope nat_scope.
Variable I : finType.
Variable dI : I.
Let vsz m := #|I| ^ m.

Fixpoint index_of_vec_rec (v : seq I) : nat :=
  match v with
  | nil => 0
  | i :: v' => enum_rank i + #|I| * index_of_vec_rec v'
  end.

Lemma index_of_vec_ltn m (v : seq I) :
  size v = m -> index_of_vec_rec v < vsz m.
Proof.
rewrite /vsz.
elim: v m => [|i v IH []] //= m.
  move <-; by rewrite expn0.
case=> Hm; rewrite expnS.
case: enum_rank => j /= Hj.
have : #|I| ^ m > 0.
  rewrite -(expn0 #|I|) leq_pexp2l //.
  by case: #|I| Hj.
move CI: (#|I| ^ m) => [|sz] // _.
by rewrite mulnS -addSn leq_add // leq_mul // -ltnS -CI IH.
Qed.

Definition index_of_vec m (v : m.-tuple I) : 'I_(vsz m).
exists (index_of_vec_rec (rev v)).
abstract (by rewrite index_of_vec_ltn // size_rev size_tuple).
Defined.

Lemma card_inh : #|I| > 0.
Proof. by rewrite -cardsT card_gt0; apply/set0Pn; exists dI; rewrite inE. Qed.

Fixpoint vec_of_index_rec (m i : nat) : seq I :=
  match m with
  | 0 => nil
  | m.+1 =>
    enum_val (Ordinal (ltn_pmod i card_inh)) :: vec_of_index_rec m (i %/ #|I|)
  end.

Lemma vec_of_index_size m i : size (vec_of_index_rec m i) = m.
Proof. by elim: m i => // m IH [|i] /=; rewrite IH. Qed.

Definition vec_of_index m (i : 'I_(vsz m)) : m.-tuple I.
exists (rev (vec_of_index_rec m i)).
abstract (by case: i => i /= _; rewrite size_rev vec_of_index_size).
Defined.

Lemma vec_of_index_recK m i :
  i < vsz m -> index_of_vec_rec (vec_of_index_rec m i) = i.
Proof.
rewrite /vsz.
elim: m i => [|m IH /= i Hi]; first by case; rewrite expn0 // ltnS.
rewrite enum_valK IH /=; first by rewrite addnC mulnC -divn_eq.
rewrite -(ltn_pmul2r card_inh) (leq_ltn_trans (leq_trunc_div _ _)) //.
by rewrite mulnC -expnS.
Qed.

Lemma vec_of_indexK m : cancel (@vec_of_index m) (@index_of_vec m).
Proof.
rewrite /index_of_vec /vec_of_index /= => -[i] Hi.
apply val_inj; by rewrite /= revK vec_of_index_recK.
Qed.

Lemma index_of_vecK m : cancel (@index_of_vec m) (@vec_of_index m).
Proof.
rewrite /index_of_vec /vec_of_index => -[t Ht].
apply/val_inj => /=.
rewrite -[RHS]revK; congr rev.
move/eqP: Ht; rewrite -size_rev.
elim: (rev t) m => {t} [|i t IH] m <- //=.
congr (_ :: _).
  rewrite (_ : Ordinal _ = enum_rank i) ?enum_rankK //.
  apply val_inj => /=.
  by rewrite addnC mulnC modnMDl modn_small.
rewrite divnDr.
  by rewrite divn_small // add0n mulKn ?card_inh // IH.
exact/dvdn_mulr/dvdnn.
Qed.

Lemma index_of_vec_bij m : bijective (@index_of_vec m).
Proof.
exists (@vec_of_index m); [exact: index_of_vecK | exact: vec_of_indexK].
Qed.

Lemma vec_of_index_bij m : bijective (@vec_of_index m).
Proof.
exists (@index_of_vec m); [exact: vec_of_indexK | exact: index_of_vecK].
Qed.
End index_of_vec_bij.

(* dpower n R^o forms a vector space of size #|I|^m *)
Section vector.
Variable (I : finType) (R : comRingType) (dI : I).
Let vsz m := (#|I| ^ m)%N.
Let tmatrix := tmatrix I R.

Section mxtmatrix.
Variables m n : nat.
Definition mxtmatrix (M : 'M[R]_(vsz m,vsz n)) : tmatrix m n :=
  [ffun vi => [ffun vj => M (index_of_vec vi) (index_of_vec vj)]].

Definition tmatrixmx (M : tmatrix m n) : 'M[R]_(vsz m,vsz n) :=
  \matrix_(i,j) M (vec_of_index dI i) (vec_of_index dI j).

Lemma tmatrixmxK : cancel tmatrixmx mxtmatrix.
Proof.
move=> v; apply/ffunP => vi; apply/ffunP => vj.
by rewrite !ffunE mxE !index_of_vecK.
Qed.

Lemma mxtmatrixK : cancel mxtmatrix tmatrixmx.
Proof.
move=> v; apply/matrixP => i j; by rewrite mxE !ffunE !vec_of_indexK.
Qed.
End mxtmatrix.

Lemma tmatrixmx_mul m n p (M1 : tmatrix m n) (M2 : tmatrix n p) :
  tmatrixmx (M1 *t M2) = tmatrixmx M1 *m tmatrixmx M2.
Proof.
apply/matrixP => i j; rewrite !mxE !ffunE.
rewrite (reindex (@index_of_vec I n)) /=.
  apply eq_bigr => vi _; by rewrite !mxE index_of_vecK.
exists (@vec_of_index _ dI n) => x y; by rewrite (vec_of_indexK,index_of_vecK).
Qed.

Lemma mxtmatrix_mul m n p (M1 : 'M_(vsz m,vsz n)) (M2 : 'M_(vsz n,vsz p)) :
  mxtmatrix (M1 *m M2) = mxtmatrix M1 *t mxtmatrix M2.
Proof.
apply/ffunP => vi; apply/ffunP => vj; rewrite !ffunE !mxE.
rewrite (reindex (@index_of_vec I n)) /=.
  apply eq_bigr => vk _; by rewrite !ffunE.
exists (@vec_of_index _ dI n) => x y; by rewrite (vec_of_indexK,index_of_vecK).
Qed.

Lemma tmatrixmx_id m : tmatrixmx (idts I R m) = (1%:M).
Proof.
apply/matrixP => i j; rewrite !mxE !ffunE.
by rewrite (inj_eq (bij_inj (vec_of_index_bij dI m))).
Qed.

Lemma mxtmatrix_id m : mxtmatrix (1%:M) = idts I R m.
Proof.
apply/ffunP => vi; apply/ffunP => vj; rewrite !ffunE mxE.
by rewrite (inj_eq (bij_inj (index_of_vec_bij dI m))).
Qed.

Lemma mul1ts m n (M : tmatrix  m n) : idts I R m *t M = M.
Proof.
by rewrite -[LHS]tmatrixmxK tmatrixmx_mul tmatrixmx_id mul1mx tmatrixmxK.
Qed.
Lemma mults1 m n (M : tmatrix  m n) : M *t idts I R n = M.
Proof.
by rewrite -[LHS]tmatrixmxK tmatrixmx_mul tmatrixmx_id mulmx1 tmatrixmxK.
Qed.

Definition vec_dpower m (X : 'rV[R]_(vsz m)) : dpower I m R^o :=
  [ffun vi => X ord0 (index_of_vec vi)].

Definition dpower_vec m (X : dpower I m R^o) : 'rV[R]_(vsz m) :=
  \row_i X (vec_of_index dI i).

Definition mxmor m n (M : 'M_(vsz m,vsz n)) := tsmor (mxtmatrix M).

Lemma dpower_vector m : Vector.axiom (vsz m) (dpower I m R^o).
Proof.
exists (@dpower_vec m).
- move=> x /= y z. apply/rowP => i. by rewrite !(ffunE,mxE).
- exists (@vec_dpower m).
  + move=> v. apply/ffunP => vi. by rewrite !(ffunE,mxE) index_of_vecK.
  + move=> X. apply/rowP => i. by rewrite !(ffunE,mxE) vec_of_indexK.
Qed.
End vector.

(* Helper lemmas for computation *)
Section enum_indices.
Variable I : finType.
Variable enumI : seq I.
Hypothesis uniq_enumI : uniq enumI.
Hypothesis mem_enumI : forall i, i \in enumI.

Fixpoint enum_indices m : seq (m.-tuple I) :=
  match m with
  | 0 => [:: [tuple of [::]]]
  | S m =>
    allpairs (fun x (t : m.-tuple _) => [tuple of x :: val t])
             enumI (enum_indices m)
  end.

Lemma mem_enum_indices m t : t \in enum_indices m.
Proof.
elim: m t => [|m IH] [[|i t] Hlen] //=.
apply/flatten_mapP.
exists i => //.
case/eqP: (Hlen) => /eqP Hlen'.
apply/mapP; exists (Tuple Hlen') => //; exact/val_inj.
Qed.

Lemma size_enum_indices m : size (enum_indices m) = (size enumI ^ m)%N.
Proof. elim: m => //= m IH; by rewrite size_allpairs IH expnS. Qed.

Lemma uniq_enum_indices m : uniq (enum_indices m).
Proof.
rewrite /is_true -(enum_uniq (tuple_finType m I)).
apply eq_uniq.
  rewrite -cardT card_tuple size_enum_indices; congr expn.
  move/card_uniqP: uniq_enumI => <-.
  apply eq_card => i; by rewrite mem_enumI.
move=> t. by rewrite mem_enum_indices mem_enum.
Qed.

Lemma forall_indicesP n (P : pred (n.-tuple I)) :
  reflect (forall v, P v) (all P (enum_indices n)).
Proof.
apply (iffP idP).
  move=> H vi.
  have : vi \in enum_indices _ by rewrite mem_enum_indices.
  by apply/allP: vi.
move=> H; by apply/allP.
Qed.

Lemma eq_from_indicesP n (T : eqType) (v w : dpower I n T) :
  reflect (v = w) (all (fun x => v x == w x) (enum_indices n)).
Proof.
apply/(iffP (forall_indicesP _)) => [H | -> //].
apply/ffunP => vi; exact/eqP.
Qed.

Lemma sum_enum_indices (L : zmodType) m (F : m.-tuple I -> L) :
  (\sum_vi F vi = foldr +%R 0 (map F (enum_indices m))).
Proof.
rewrite foldrE big_map [RHS]big_uniq ?uniq_enum_indices //=.
apply/esym/eq_bigl => vi. exact/mem_enum_indices.
Qed.
End enum_indices.

Section enum2.
Let I := [finType of 'I_2].

Definition enum2 : seq I := [:: 0; 1].
Lemma uniq_enum2 : uniq enum2. Proof. by []. Qed.
Lemma mem_enum2 i : i \in enum2.
Proof. by rewrite !inE; case: i => -[|[]]. Qed.
End enum2.
