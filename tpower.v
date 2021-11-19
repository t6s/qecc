From mathcomp Require Import all_ssreflect all_algebra.
Require Import lens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "T ^(x) n" (at level 29, format "T  ^(x)  n").
Reserved Notation "T `^ I ^(x) n" (at level 29, I, n at next level,
  format "T  `^  I  ^(x)  n").

Import GRing.Theory.

Section tensor_space.
Variables (I : finType) (dI : I) (R : comRingType).
Local Notation merge_indices := (merge_indices dI).

Definition tpower n T := {ffun n.-tuple I -> T}.

Local Notation "T ^(x) n" := (tpower n T) (at level 29, format "T  ^(x)  n").

Definition endofun m := forall T : lmodType R, T ^(x) m -> T ^(x) m.
Definition endo m :=
  forall T : lmodType R, {linear T ^(x) m -> T ^(x) m}%R.
Definition tsquare m := (R^o ^(x) m) ^(x) m.

(* Actually, need the property (naturality)
 forall (f : endo m) (T1 T2 : lmodType R) (h : {linear T1 -> T2}),
   map h \o f T1 = f T2 \o map h
which is equivalent to the fact f = nvendo M for a square matrix M : tsquare m.
*)
Definition map_tpower m T1 T2 (f : T1 -> T2) (nv : T1 ^(x) m) : T2 ^(x) m :=
  [ffun v : m.-tuple I => f (nv v)].

Definition naturality m (f : endo m) :=
  forall (T1 T2 : lmodType R) (h : {linear T1 -> T2}%R) (v : T1 ^(x) m),
    map_tpower h (f T1 v) = f T2 (map_tpower h v).

Definition nvendo_fun m (M : tsquare m) : endofun m :=
  fun T v =>
    [ffun vi : m.-tuple I => \sum_(vj : m.-tuple I) (M vi vj : R) *: v vj]%R.

Lemma nvendo_is_linear m M T : linear (@nvendo_fun m M T).
Proof.
move=> /= x y z; apply/ffunP => /= vi; rewrite !ffunE.
rewrite scaler_sumr -big_split; apply eq_bigr => /= vj _.
by rewrite !ffunE scalerDr !scalerA mulrC.
Qed.

Definition nvendo m (M : tsquare m) : endo m :=
  fun T => Linear (@nvendo_is_linear m M T).

Definition nvbasis m (vi : m.-tuple I) : R^o ^(x) m:=
  [ffun vj => (vi == vj)%:R]%R.

Definition endons m (f : endo m) : tsquare m :=
  [ffun vi => [ffun vj => f _ (nvbasis vj) vi]].

Lemma nvbasisC m (vi vj : m.-tuple I) : nvbasis vi vj = nvbasis vj vi.
Proof. by rewrite !ffunE eq_sym. Qed.

Lemma sum_nvbasisK n (T : lmodType R) (vi : n.-tuple I) (F : T ^(x) n) :
  (\sum_vj (nvbasis vi vj *: F vj) = F vi)%R.
Proof.
rewrite (bigD1 vi) //= !ffunE eqxx big1 ?(addr0,scale1r) //.
move=> vk; rewrite !ffunE eq_sym => /negbTE ->; by rewrite scale0r.
Qed.

Lemma decompose_tpower m (T : lmodType R) (v : T ^(x) m) :
  v = (\sum_i map_tpower ( *:%R^~ (v i)) (nvbasis i))%R.
Proof.
apply/ffunP => vi; rewrite sum_ffunE -[LHS]sum_nvbasisK /=.
by apply eq_bigr => vj _; rewrite [RHS]ffunE nvbasisC.
Qed.

Lemma naturalityP m (f : endo m) :
  naturality f <-> exists M, forall T, f T =1 nvendo M T.
Proof.
split => [Hf | [M] HM].
- exists (endons f) => T /= v.
  rewrite [in LHS](decompose_tpower v) linear_sum.
  apply/ffunP => /= vi; rewrite !ffunE sum_ffunE /=.
  apply eq_bigr => /= vj _; rewrite !ffunE.
  set h : R^o -> T := *:%R^~ _.
  have hlin : linear h by move=> x y z; rewrite /h scalerDl !scalerA.
  by rewrite -(Hf _ _ (Linear hlin) (nvbasis vj)) ffunE.
- move=> T1 T2 h /= v; apply/ffunP => /= vi.
  rewrite !HM !ffunE linear_sum; apply eq_bigr => vj _.
  by rewrite linearZ_LR !ffunE.
Qed.

Definition ket_bra m (ket : R^o ^(x) m) (bra : R^o ^(x) m) : tsquare m :=
  [ffun vi => ket vi *: bra]%R.

Definition mul_tsquare m (M1 M2 : tsquare m) : tsquare m :=
  [ffun vi => [ffun vj => \sum_vk M1 vi vk * M2 vk vj]]%R.

Definition id_tsquare m : tsquare m := [ffun vi => nvbasis vi].

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

Definition curry (st : T ^(x) n) : (T ^(x) (n - m)) ^(x) m:=
  [ffun v : m.-tuple I =>
   [ffun w : (n-m).-tuple I => st (merge_indices l v w)]].

Definition uncurry (st : (T ^(x) (n - m)) ^(x) m) : T ^(x) n :=
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
End curry.

Section focus.
Definition focus_fun n m (l : lens n m) (tr : endo m) : endofun n :=
  fun T (v : T ^(x) n) => uncurry l (tr _ (curry l v)).

Lemma focus_is_linear n m l tr T : linear (@focus_fun n m l tr T).
Proof.
move=> x y z.
apply/ffunP => vi; rewrite !ffunE.
have -> : curry l (T := T) = Linear (curry_is_linear l (T:=T)) by [].
by rewrite !linearP !ffunE.
Qed.

Definition focus n m l tr : endo n :=
  fun T => Linear (@focus_is_linear n m l tr T).

Lemma focus_naturality n m l tr : naturality tr -> naturality (@focus n m l tr).
Proof.
case/naturalityP => M /= NM; apply/naturalityP.
exists (endons (focus l (nvendo M))).
move=> T /= v; apply/ffunP => /= vi; rewrite !ffunE NM !ffunE sum_ffunE.
under [RHS]eq_bigr do rewrite !ffunE sum_ffunE scaler_suml.
rewrite exchange_big /=; apply eq_bigr => vj _.
rewrite [in LHS](decompose_tpower v) !ffunE sum_ffunE scaler_sumr.
by apply eq_bigr => i _; rewrite !ffunE !scalerA.
Qed.

Variables (T : lmodType R) (n m p : nat) (l : lens n m).

(* Identity *)
Lemma focusI tr : naturality tr -> focus (lens_id n) tr T =1 tr T.
Proof.
rewrite /focus => /naturalityP [f Hf] /= v.
apply/ffunP => /= vi.
rewrite /focus_fun !{}Hf {tr} !ffunE sum_ffunE.
apply eq_bigr => vj _; rewrite !ffunE extract_lens_id.
congr (_ *: v _)%R.
apply eq_from_tnth => i; by rewrite tnth_mktuple index_lens_id -tnth_nth.
Qed.

(* horizontal composition of endomorphisms *)
Lemma focusC (l' : lens n p) tr tr' (v : T ^(x) n) :
  [disjoint l & l'] -> naturality tr -> naturality tr' ->
  focus l tr _ (focus l' tr' _ v) =
  focus l' tr' _ (focus l tr _ v).
Proof.
rewrite /focus => Hdisj /naturalityP [f Hf] /naturalityP [f' Hf'].
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

Lemma focus_tensor (M : tsquare m) (M' : tsquare n) (v : T ^(x) (m + n)) :
  focus (lens_left m n) (nvendo M) _ (focus (lens_right m n) (nvendo M') _ v) =
  nvendo (tensor_tsquare M M') _ v.
Proof.
apply/ffunP => /= vi.
rewrite /focus_fun !ffunE !sum_ffunE.
under eq_bigr do rewrite !ffunE !sum_ffunE scaler_sumr.
rewrite pair_bigA /=.
rewrite [LHS](reindex (fun v : (m+n).-tuple I =>
         (extract (lens_left m n) v, extract (lens_right m n) v))); last first.
  exists (fun v : m.-tuple I * n.-tuple I => [tuple of v.1 ++ v.2]) => /= vj _. 
    apply eq_from_tnth => i /=.
    rewrite (tnth_nth (tnth vj i)) /= -map_cat.
    move: (lens_left_right m n) => /(f_equal val) /(f_equal val) /= ->.
    by rewrite map_tnth_enum -tnth_nth.
  case: vj => vl vr /=; congr pair; apply eq_from_tnth => i.
    rewrite tnth_map tnth_mktuple.
    by rewrite (tnth_nth (tnth vl i)) /= nth_cat size_tuple ltn_ord -tnth_nth.
  rewrite tnth_map tnth_mktuple.
  rewrite (tnth_nth (tnth vr i)) /= nth_cat size_tuple ltnNge leq_addr /=.
  by rewrite addKn -tnth_nth.
apply eq_bigr => /= vj _; rewrite !ffunE !merge_indices_extract_others.
rewrite extract_inject; last by rewrite disjoint_sym lens_left_right_disjoint.
by rewrite scalerA inject_all // lens_left_right_disjoint.
Qed.

(* vertical composition of endomorphisms *)
Section comp_endo.
Variables tr tr' : endo m.
Definition comp_endo : endo m := fun A => GRing.comp_linear (tr A) (tr' A).

Lemma comp_naturality : naturality tr -> naturality tr' -> naturality comp_endo.
Proof. move=> N1 N2 T1 T2 f v; by rewrite N1 N2. Qed.

Lemma focus_comp (v : T ^(x) n) :
  focus l comp_endo _ v = focus l tr _ (focus l tr' _ v).
Proof. apply/ffunP => /= vi; by rewrite /focus_fun /= uncurryK. Qed.
End comp_endo.

(* associativity of actions of lenses *)
Lemma focusM (l' : lens m p) tr (v : T ^(x) n) : naturality tr ->
  focus (lens_comp l l') tr _ v = focus l (focus l' tr) _ v.
Proof.
case/naturalityP => f Hf.
rewrite /focus /focus_fun /= !{}Hf {tr}.
apply/ffunP => /= vi.
rewrite !ffunE (extract_lothers_comp dI) -!extract_comp.
rewrite -[in RHS]lothers_in_l_comp -(lothers_notin_l_comp l l') !sum_ffunE.
apply eq_bigr => /= vj _; rewrite !ffunE.
congr (_ *: v _)%R.
exact: merge_indices_comp.
Qed.
End focus.
End tensor_space.

Notation "T `^ I ^(x) n" := (tpower I n T).

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
End index_of_vec_bij.

(* tpower n R^o forms a vector space of size #|I|^m *)
Section vector.
Variable (I : finType) (R : comRingType).
Let vsz m := #|I| ^ m.
Let tsquare := tsquare I R.

Definition mxtsquare m (M : 'M[R]_(vsz m,vsz m)) : tsquare m :=
  [ffun vi => [ffun vj => M (index_of_vec vi) (index_of_vec vj)]].

Definition mxendo m (M : 'M[R]_(vsz m,vsz m)) := nvendo (mxtsquare M).

Definition vec_tpower m (X : 'rV[R]_(vsz m)) : R^o `^ I ^(x) m :=
  [ffun vi => X ord0 (index_of_vec vi)].

Definition tpower_vec H m (X : R^o `^ I ^(x) m) : 'rV[R]_(vsz m) :=
  \row_i X (vec_of_index H i).

Lemma tpower_vector (H : #|I| > 0) n : Vector.axiom (vsz n) (R^o `^ I ^(x) n).
Proof.
exists (@tpower_vec H n).
- move=> x /= y z. apply/rowP => i. by rewrite !(ffunE,mxE).
- exists (@vec_tpower n).
  + move=> v. apply/ffunP => vi. by rewrite !(ffunE,mxE) index_of_vecK.
  + move=> X. apply/rowP => i. by rewrite !(ffunE,mxE) vec_of_indexK.
Qed.
End vector.
