From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Reserved Notation "f \v g" (at level 50, format "f  \v  g").
Reserved Notation "f =e g" (at level 70).

Section tensor_space.
Variables (I : finType) (dI : I) (R : comRingType).
Local Notation merge_indices := (merge_indices dI).

Definition tpower n T := {ffun n.-tuple I -> T}.
Definition morfun m n := forall T : lmodType R, tpower m T -> tpower n T.
Definition mor m n :=
  forall T : lmodType R, {linear tpower m T -> tpower n T}%R.
Definition tmatrix m n := tpower m (tpower n R^o).
Notation tsquare n := (tmatrix n n).
Notation endo n := (mor n n).
Notation endofun n := (morfun n n).

Definition tpcast n m T (H : n = m) (v : tpower n T) : tpower m T :=
  [ffun vi => v (cast_tuple vi (esym H))].

(* Actually, need the property (naturality)
 forall (f : endo m) (T1 T2 : lmodType R) (h : {linear T1 -> T2}),
   map h \o f T1 = f T2 \o map h
which is equivalent to the fact f = nvendo M for a square matrix M : tsquare m.
*)
Definition map_tpower m T1 T2 (f : T1 -> T2) (nv : tpower m T1)
  : tpower m T2 := [ffun v : m.-tuple I => f (nv v)].

Definition naturality m n (f : mor m n) :=
  forall (T1 T2 : lmodType R) (h : {linear T1 -> T2}%R) (v : tpower m T1),
    map_tpower h (f T1 v) = f T2 (map_tpower h v).

Definition eq_mor m n (f1 f2 : mor m n) := forall T : lmodType R, f1 T =1 f2 T.
Notation "f1 =e f2" := (eq_mor f1 f2).

Definition tsmor_fun m n (M : tmatrix n m) : morfun m n :=
  fun T v =>
    [ffun vi : n.-tuple I => \sum_(vj : m.-tuple I) (M vi vj : R) *: v vj]%R.

Lemma tsmor_is_linear m n M T : linear (@tsmor_fun m n M T).
Proof.
move=> /= x y z; apply/ffunP => /= vi; rewrite !ffunE.
rewrite scaler_sumr -big_split; apply eq_bigr => /= vj _.
by rewrite !ffunE scalerDr !scalerA mulrC.
Qed.

Definition tsmor m n (M : tmatrix n m) : mor m n :=
  fun T => Linear (@tsmor_is_linear m n M T).

Definition tpbasis m (vi : m.-tuple I) : tpower m R^o :=
  [ffun vj => (vi == vj)%:R]%R.

Definition morts m n (f : mor m n) : tmatrix n m :=
  [ffun vi => [ffun vj => f _ (tpbasis vj) vi]].

Lemma tpbasisC m (vi vj : m.-tuple I) : tpbasis vi vj = tpbasis vj vi.
Proof. by rewrite !ffunE eq_sym. Qed.

Lemma sum_tpbasisK n (T : lmodType R) (vi : n.-tuple I) (F : tpower n T) :
  (\sum_vj (tpbasis vi vj *: F vj) = F vi)%R.
Proof.
rewrite (bigD1 vi) //= !ffunE eqxx big1 ?(addr0,scale1r) //.
move=> vk; rewrite !ffunE eq_sym => /negbTE ->; by rewrite scale0r.
Qed.

Lemma sum_tpbasisKo n (vi : n.-tuple I) (F : tpower n R) :
  (\sum_vj (F vj *: tpbasis vi vj) = F vi)%R.
Proof.
rewrite (bigD1 vi) //= !ffunE eqxx big1 ?addr0 /GRing.scale /= ?mulr1 //.
move=> vk; rewrite !ffunE eq_sym => /negbTE ->; by rewrite mulr0.
Qed.

Lemma decompose_tpower m (T : lmodType R) (v : tpower m T) :
  v = (\sum_i map_tpower ( *:%R^~ (v i)) (tpbasis i))%R.
Proof.
apply/ffunP => vi; rewrite sum_ffunE -[LHS]sum_tpbasisK /=.
by apply eq_bigr => vj _; rewrite [RHS]ffunE tpbasisC.
Qed.

Lemma naturalityP m n (f : mor m n) :
  naturality f <-> exists M, f =e tsmor M.
Proof.
split => [Hf | [M] HM].
- exists (morts f) => T /= v.
  rewrite [in LHS](decompose_tpower v) linear_sum.
  apply/ffunP => /= vi; rewrite !ffunE sum_ffunE /=.
  apply eq_bigr => /= vj _; rewrite !ffunE.
  set h : R^o -> T := *:%R^~ _.
  have hlin : linear h by move=> x y z; rewrite /h scalerDl !scalerA.
  by rewrite -(Hf _ _ (Linear hlin) (tpbasis vj)) ffunE.
- move=> T1 T2 h /= v; apply/ffunP => /= vi.
  rewrite !HM !ffunE linear_sum; apply eq_bigr => vj _.
  by rewrite linearZ_LR !ffunE.
Qed.

Definition ket_bra m (ket : tpower m R^o) (bra : tpower m R^o) : tsquare m :=
  [ffun vi => ket vi *: bra]%R.

Definition mults m (M1 M2 : tsquare m) : tsquare m :=
  [ffun vi => [ffun vj => \sum_vk M1 vi vk * M2 vk vj]]%R.

Definition idts m : tsquare m := [ffun vi => tpbasis vi].
Definition idmor n : endo n := fun T => GRing.idfun_linear _.

Lemma idmorE n : idmor n =e tsmor (idts n).
Proof.
move=> T v; apply/ffunP => vi.
rewrite /idmor ffunE (bigD1 vi) //= big1 !ffunE ?(eqxx,scale1r,addr0) //.
move=> i /negbTE Hi; by rewrite ffunE eq_sym Hi scale0r.
Qed.

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
     M2 (extract (lens_right m n) vi) (extract (lens_right m n) vj)]]%R.

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

Definition curry (st : tpower n T) : tpower m (tpower (n-m) T) :=
  [ffun v : m.-tuple I =>
   [ffun w : (n-m).-tuple I => st (merge_indices l v w)]].

Definition uncurry (st : tpower m (tpower (n-m) T)) : tpower n T :=
  [ffun v : n.-tuple I => st (extract l v) (extract (lothers l) v)].

Lemma uncurryK : cancel uncurry curry.
Proof.
move=> v; apply/ffunP => v1; apply/ffunP => v2.
by rewrite !ffunE extract_merge extract_lothers_merge.
Qed.

Lemma curryK : cancel curry uncurry.
Proof. move=> v; apply/ffunP => w; by rewrite !ffunE merge_indices_extract. Qed.

Lemma curry_is_linear : linear curry.
Proof. move=>x y z; apply/ffunP=>vi; apply/ffunP =>vj; by rewrite !ffunE. Qed.

Lemma uncurry_is_linear : linear uncurry.
Proof. move => x y z; apply/ffunP=> vi; by rewrite !ffunE. Qed.

(* Special cases of curry/uncurry *)
Definition curry0 (v : T) : tpower 0 T := [ffun _ => v].
Definition curryn0 : tpower n T -> tpower n (tpower 0 T) :=
  map_tpower curry0.
Definition uncurry0 (v : tpower 0 T) : T := v [tuple].

Lemma curryn0E :
  curryn0 = fun v => [ffun vi => [ffun _ => v vi]].
Proof. reflexivity. Qed.

Lemma curry0_is_linear : linear curry0.
Proof. move=> x y z. apply/ffunP => vi. by rewrite !ffunE. Qed.
Lemma curryn0_is_linear : linear curryn0.
Proof. move=> x y z. apply/ffunP=> vi. apply/ffunP=> vj. by rewrite !ffunE. Qed.
Lemma uncurry0_is_linear : linear uncurry0.
Proof. move=> x y z. by rewrite /uncurry0 !ffunE. Qed.
End curry.

Section inner_prod_coprod.
Variable n : nat.
Let cast_uncurry T := map_tpower (m:=n) (tpcast (T:=T) (esym (addKn n n))).
Definition M_inner_prod (M : tsquare n) :=
  tsmor (curry0 (uncurry (lens_left n n) (cast_uncurry M))).
Definition M_inner_coprod (M : tsquare n) :=
  tsmor (curryn0 (uncurry (lens_left n n) (cast_uncurry M))).
Definition inner_prod : mor (n+n) 0 := M_inner_prod (idts _).
Definition inner_coprod : mor 0 (n+n) := M_inner_coprod (idts _).
End inner_prod_coprod.

Section focus.
Variables (n m : nat) (l : lens n m) (tr : endo m).
Definition focus_fun : endofun n :=
  fun T (v : tpower n T) => uncurry l (tr _ (curry l v)).

Lemma focus_is_linear T : linear (@focus_fun T).
Proof.
move=> x y z.
apply/ffunP => vi; rewrite !ffunE.
have -> : curry l (T := T) = Linear (curry_is_linear l (T:=T)) by [].
by rewrite !linearP !ffunE.
Qed.

Definition focus : endo n := locked (fun T => Linear (@focus_is_linear T)).

Lemma focusE : focus = fun T => Linear (@focus_is_linear T).
Proof. by rewrite /focus; unlock. Qed.
End focus.

Lemma focus_naturality n m l tr : naturality tr -> naturality (@focus n m l tr).
Proof.
case/naturalityP => M /= NM; apply/naturalityP.
exists (morts (focus l (tsmor M))).
move=> T /= v; apply/ffunP => /= vi; rewrite !focusE !ffunE NM !ffunE sum_ffunE.
under [RHS]eq_bigr do rewrite !ffunE sum_ffunE scaler_suml.
rewrite exchange_big /=; apply eq_bigr => vj _.
rewrite [in LHS](decompose_tpower v) !ffunE sum_ffunE scaler_sumr.
by apply eq_bigr => i _; rewrite !ffunE !scalerA.
Qed.

Section asym_focus.
Variables (n m p : nat) (l : lens (m+n) m) (l' : lens (p+n) p) (tr : mor m p).

Lemma addKn_any : m + n - m = p + n - p.
Proof. by rewrite !addKn. Qed.

Definition asym_focus_fun : morfun (m + n) (p + n) :=
  fun T (v : tpower (m + n) T) =>
    uncurry l' (map_tpower (tpcast addKn_any) (tr _ (curry l v))).

Lemma asym_focus_is_linear T : linear (@asym_focus_fun T).
Proof.
move=> x y z.
apply/ffunP => vi. rewrite !ffunE.
have -> : curry l (T := T) = Linear (curry_is_linear l (T:=T)) by [].
by rewrite !linearP !ffunE.
Qed.

Definition asym_focus : mor (m + n) (p + n) :=
  fun T => Linear (@asym_focus_is_linear T).
End asym_focus.

Lemma asym_focus_naturality n m p l l' tr :
  naturality tr -> naturality (@asym_focus n m p l l' tr).
Proof.
case/naturalityP => M /= NM; apply/naturalityP.
exists (morts (asym_focus l l' (tsmor M))).
move=> T /= v; apply/ffunP => /= vi; rewrite !ffunE NM !ffunE sum_ffunE.
under [RHS]eq_bigr do rewrite !ffunE sum_ffunE scaler_suml.
rewrite exchange_big /=; apply eq_bigr => vj _.
rewrite [in LHS](decompose_tpower v) !ffunE sum_ffunE scaler_sumr.
by apply eq_bigr => i _; rewrite !ffunE !scalerA.
Qed.

Section focus_props.
Variables (n m p : nat) (l : lens n m).

(* Identity *)
Lemma focusI tr : naturality tr -> focus (lens_id n) tr =e tr.
Proof.
rewrite focusE => /naturalityP [f Hf] /= T v.
apply/ffunP => /= vi.
rewrite /focus_fun !{}Hf {tr} !ffunE sum_ffunE.
apply eq_bigr => vj _; rewrite !ffunE extract_lens_id.
congr (_ *: v _)%R.
apply eq_from_tnth => i; by rewrite tnth_mktuple index_lens_id -tnth_nth.
Qed.

(* Equality *)
Lemma focus_eq (f1 f2 : endo m) : f1 =e f2 -> focus l f1 =e focus l f2.
Proof. move=> Heq T v /=; by rewrite 2!focusE /= /focus_fun Heq. Qed.

(* Vertical composition of morphisms *)
Section comp_mor.
Variables (r q s : nat) (tr : mor q s) (tr' : mor r q).
Definition comp_mor : mor r s := fun A => GRing.comp_linear (tr A) (tr' A).

Lemma comp_naturality : naturality tr -> naturality tr' -> naturality comp_mor.
Proof. move=> N1 N2 T1 T2 f v; by rewrite N1 N2. Qed.
End comp_mor.
Notation "f \v g" := (comp_mor f g).

Lemma focus_comp r q (tr tr' : endo q) (lq : lens r q) :
  focus lq (tr \v tr') =e focus lq tr \v focus lq tr'.
Proof.
move=> T v; apply/ffunP => /= vi.
by rewrite !focusE /focus_fun /= uncurryK.
Qed.

Lemma tsmor_comp (M N : tsquare n) : tsmor (mults M N) =e tsmor M \v tsmor N.
Proof.
move=> T v; apply/ffunP => vi; rewrite !ffunE.
under eq_bigr do rewrite !ffunE !scaler_suml.
rewrite exchange_big /=.
apply eq_bigr => vk _; rewrite !ffunE !(scaler_suml,scaler_sumr).
by apply eq_bigr => vj _; rewrite scalerA.
Qed.

(* Horizontal composition of endomorphisms *)
Lemma focusC (l' : lens n p) tr tr' :
  [disjoint l & l'] -> naturality tr -> naturality tr' ->
  focus l tr \v focus l' tr' =e focus l' tr' \v focus l tr.
Proof.
rewrite !focusE => Hdisj /naturalityP [f Hf] /naturalityP [f' Hf'] T v /=.
apply/ffunP => /= vi.
rewrite /focus_fun !{}Hf !{}Hf' {tr tr'} !ffunE !sum_ffunE.
under eq_bigr do rewrite !ffunE !sum_ffunE scaler_sumr.
rewrite exchange_big; apply eq_bigr => /= vj _.
rewrite !ffunE !sum_ffunE scaler_sumr; apply eq_bigr => /= vk _.
rewrite !ffunE !scalerA [in RHS]mulrC.
congr (f _ vk * f' _ vj *: v _)%R.
- by rewrite extract_merge_disjoint // disjoint_sym.
- by rewrite extract_merge_disjoint.
- by rewrite !merge_indices_extract_others inject_disjointC.
Qed.

Lemma focus_tensor (M : tsquare m) (M' : tsquare n) :
  focus (lens_left m n) (tsmor M) \v focus (lens_right m n) (tsmor M') =e
  tsmor (tensor_tsquare M M').
Proof.
move=> T v; apply/ffunP => /= vi.
rewrite focusE !ffunE !sum_ffunE.
under eq_bigr do rewrite !focusE !ffunE !sum_ffunE scaler_sumr.
rewrite pair_bigA /=.
rewrite [LHS](reindex (fun v : (m+n).-tuple I =>
         (extract (lens_left m n) v, extract (lens_right m n) v))); last first.
  exists (fun v : m.-tuple I * n.-tuple I => [tuple of v.1 ++ v.2]) => /= vj _. 
    rewrite -[RHS]extract_lens_id -(lens_left_right m n).
    by apply/val_inj; rewrite /= map_cat.
  case: vj => vl vr /=; congr pair; apply eq_from_tnth => i;
    by rewrite tnth_map tnth_mktuple (tnth_lshift,tnth_rshift).
apply eq_bigr => /= vj _; rewrite !ffunE !merge_indices_extract_others.
rewrite extract_inject; last by rewrite disjoint_sym lens_left_right_disjoint.
by rewrite scalerA inject_all // lens_left_right_disjoint.
Qed.

(* Associativity of actions of lenses *)
Lemma focusM (l' : lens m p) tr : naturality tr ->
  focus (lens_comp l l') tr =e focus l (focus l' tr).
Proof.
case/naturalityP => f Hf T v.
rewrite !focusE /focus_fun /= !{}Hf {tr}.
apply/ffunP => /= vi.
rewrite !ffunE (extract_lothers_comp dI) -!extract_comp.
rewrite -[in RHS]lothers_in_l_comp -(lothers_notin_l_comp l l') !sum_ffunE.
apply eq_bigr => /= vj _; rewrite !ffunE.
congr (_ *: v _)%R.
exact: merge_indices_comp.
Qed.
End focus_props.
Notation "f \v g" := (comp_mor f g).
Notation tsapp l M := (focus l (tsmor M)).

Lemma focus_tensor' n m p (l : lens n m) (l' : lens n p) (H : [disjoint l & l'])
      (M : tsquare m) (M' : tsquare p) :
  tsapp l M \v tsapp l' M' =e tsapp (lens_cat H) (tensor_tsquare M M').
Proof.
rewrite {1}(lens_comp_right H) {1}(lens_comp_left H) => T v /=.
rewrite focusM; last by apply/naturalityP; eexists.
rewrite -> focusM; last by apply/naturalityP; eexists.
have /= <- := focus_comp _ _ _ v.
move: T v; exact/focus_eq/focus_tensor.
Qed.
End tensor_space.

Notation "f1 =e f2" := (eq_mor f1 f2).
Notation "f \v g" := (comp_mor f g).
Notation tsapp l M := (focus l (tsmor M)).

(* Conversion between tpower and vector space *)

Section index_of_vec_bij.
Variable I : finType.
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

Hypothesis H : #|I| > 0.
Fixpoint vec_of_index_rec (m i : nat) : seq I :=
  match m with
  | 0 => nil
  | m.+1 =>
    enum_val (Ordinal (ltn_pmod i H)) :: vec_of_index_rec m (i %/ #|I|)
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
by rewrite -(ltn_pmul2r H) (leq_ltn_trans (leq_trunc_div _ _)) // mulnC -expnS.
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
  by rewrite divn_small // add0n mulKn // IH.
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

(* tpower n R^o forms a vector space of size #|I|^m *)
Section vector.
Variable (I : finType) (R : comRingType).
Hypothesis H : #|I| > 0.
Variable m : nat.
Let vsz := #|I| ^ m.
Let tsquare n := tmatrix I R n n.

Definition mxtsquare (M : 'M[R]_vsz) : tsquare m :=
  [ffun vi => [ffun vj => M (index_of_vec vi) (index_of_vec vj)]].

Definition tsquaremx (M : tsquare m) : 'M[R]_vsz :=
  \matrix_(i,j) M (vec_of_index H i) (vec_of_index H j).

Lemma tsquaremxK : cancel tsquaremx mxtsquare.
Proof.
move=> v; apply/ffunP => vi; apply/ffunP => vj.
by rewrite !ffunE mxE !index_of_vecK.
Qed.

Lemma mxtsquareK : cancel mxtsquare tsquaremx.
Proof.
move=> v; apply/matrixP => i j; by rewrite mxE !ffunE !vec_of_indexK.
Qed.

Lemma tsquaremx_mul : {morph tsquaremx : M1 M2 / mults M1 M2 >-> M1 *m M2}%R.
Proof.
move=> M1 M2; apply/matrixP => i j; rewrite !mxE !ffunE.
rewrite (reindex (@index_of_vec I m)) /=.
  apply eq_bigr => vi _; by rewrite !mxE index_of_vecK.
exists (@vec_of_index _ H m) => x y; by rewrite (vec_of_indexK,index_of_vecK).
Qed.

Lemma mxtsquare_mul : {morph mxtsquare : M1 M2 / M1 *m M2 >-> mults M1 M2}%R.
Proof.
move=> M1 M2; apply/ffunP => vi; apply/ffunP => vj; rewrite !ffunE !mxE.
rewrite (reindex (@index_of_vec I m)) /=.
  apply eq_bigr => vk _; by rewrite !ffunE.
exists (@vec_of_index _ H m) => x y; by rewrite (vec_of_indexK,index_of_vecK).
Qed.

Lemma tsquaremx_id : tsquaremx (idts I R m) = (1%:M)%R.
Proof.
apply/matrixP => i j; rewrite !mxE !ffunE.
by rewrite (inj_eq (bij_inj (vec_of_index_bij H m))).
Qed.

Lemma mxtsquare_id : mxtsquare (1%:M)%R = idts I R m.
Proof.
apply/ffunP => vi; apply/ffunP => vj; rewrite !ffunE mxE.
by rewrite (inj_eq (bij_inj (index_of_vec_bij H m))).
Qed.

Definition vec_tpower (X : 'rV[R]_vsz) : tpower I m R^o :=
  [ffun vi => X ord0 (index_of_vec vi)].

Definition tpower_vec (X : tpower I m R^o) : 'rV[R]_vsz :=
  \row_i X (vec_of_index H i).

Definition mxendo (M : 'M[R]_vsz) := tsmor (mxtsquare M).

Lemma tpower_vector : Vector.axiom vsz (tpower I m R^o).
Proof.
exists tpower_vec.
- move=> x /= y z. apply/rowP => i. by rewrite !(ffunE,mxE).
- exists vec_tpower.
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

Lemma eq_from_indicesP n (T : eqType) (v w : tpower I n T) :
  reflect (v = w) (all (fun x => v x == w x) (enum_indices n)).
Proof.
apply (iffP idP).
  move=> H; apply/ffunP => vi; apply/eqP.
  have : vi \in enum_indices _ by rewrite mem_enum_indices.
  by apply/allP: vi.
move -> ; by apply/allP.
Qed.

Lemma sum_enum_indices (CR : comRingType) (L : lmodType CR)
      m (F : m.-tuple I -> L) :
  (\sum_vi F vi = foldr +%R 0 (map F (enum_indices m)))%R.
Proof.
rewrite foldrE big_map [RHS]big_uniq ?uniq_enum_indices //=.
apply/esym/eq_bigl => vi. exact/mem_enum_indices.
Qed.
End enum_indices.
