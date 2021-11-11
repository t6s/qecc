From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Utility lemmas *)

Lemma addnLR m n p : m + n = p -> n = p - m.
Proof. move/(f_equal (subn^~ m)); by rewrite addKn. Qed.

Lemma ltn_ordK q (i : 'I_q) : Ordinal (ltn_ord i) = i.
Proof. by apply val_inj. Qed.

Section tnth.
Lemma nth_tnth T (n i : nat) x0 (v : n.-tuple T) (H : i < n) :
  nth x0 v i = tnth v (Ordinal H).
Proof. by rewrite (tnth_nth x0). Qed.

Variables (A : eqType) (n : nat).
Lemma tnth_inj (t : n.-tuple A) : reflect (injective (tnth t)) (uniq t).
Proof.
apply: (iffP idP).
- move=> /uniqP Hu i j.
  rewrite (tnth_nth (tnth t i)) (tnth_nth (tnth t i) t j).
  move/(Hu (tnth t i) i j)/val_inj => -> //; by rewrite inE size_tuple.
- case: t => -[|a t] // Hlen Hinj.
  apply/(uniqP a) => i j.
  rewrite !inE !size_tuple => Hi Hj.
  by rewrite !nth_tnth => /Hinj [].
Qed.

Lemma index_tuple (t : n.-tuple A) i : (index i t < n) <-> (i \in t).
Proof. by rewrite -index_mem size_tuple. Qed.
End tnth.

Section sorted.
Definition ord_ltn {r} : rel 'I_r := relpre val ltn.

Lemma sorted_enum r : sorted ord_ltn (enum 'I_r).
Proof.
rewrite -sorted_map val_enum_ord.
rewrite (_ : 0 = r - r); last by rewrite subnn.
set q := {2 3}r.
have : q <= r by [].
elim: q => // -[] //= q IH Hq.
rewrite subnS prednK.
   by rewrite IH (ltnW,andbT).
by rewrite ltn_subRL addn0.
Qed.

Variables (A : Type) (le : rel A) (le_trans : transitive le).

Lemma sorted_tnth q (lq : q.-tuple A) (a b : 'I_q) :
  sorted le lq -> ord_ltn a b -> le (tnth lq a) (tnth lq b).
Proof.
move=> Hsort ab.
have := @sorted_ltn_nth _ le le_trans (tnth lq a) lq Hsort a b.
rewrite !inE !size_tuple !ltn_ord -!tnth_nth; exact.
Qed.

Lemma sorted_comp q (lq : q.-tuple A) (lr : seq 'I_q) :
  sorted le lq -> sorted ord_ltn lr -> sorted le (map (tnth lq) lr).
Proof.
move=> Hlq /=.
elim: lr => // a [|b lr] IH //= /andP[ab] Hsort.
rewrite sorted_tnth //=; exact: IH.
Qed.

Lemma sorted_skip (a b : A) s :
  le a b -> path le b s -> path le a s.
Proof. by case: s => //= c s ab /andP[] /(le_trans ab) ->. Qed.

Lemma sorted_filter (c : pred A) s :
  sorted le s -> sorted le (filter c s).
Proof.
rewrite {1}/sorted.
case: s => // a s.
elim: s a => // [|b s IH] a /=; first by case: ifP.
case/andP => ab Hb.
case: ifP => ca; last exact: IH.
case: ifP => cb /=.
  move: (IH b Hb); by rewrite /= cb ab.
move: (IH a); rewrite /= ca; apply; exact/(sorted_skip ab).
Qed.
End sorted.

Section lens.
Variables (T : Type) (n m : nat).

Record lens := mkLens {lens_t :> m.-tuple 'I_n ; lens_uniq : uniq lens_t}.
Canonical lens_subType := Eval hnf in [subType for lens_t].
Canonical lens_predType := PredType (fun x : lens => pred_of_seq x).

Definition endo1 := m.-tuple T -> m.-tuple T.

Variables (l : lens) (f : endo1).

Definition extract (t : n.-tuple T) := [tuple of map (tnth t) l].

Lemma lens_leq : m <= n.
Proof.
rewrite -(size_enum_ord n) -(size_tuple l) uniq_leq_size // ?lens_uniq //.
move=> i _; by rewrite mem_enum.
Qed.

Lemma tnth_lensK i : index (tnth l i) l = i.
Proof.
by rewrite (tnth_nth (tnth l i)) index_uniq // (lens_uniq,size_tuple).
Qed.

Section lens_index.
Variables (i : 'I_n) (H : i \in l).

Definition lens_index : 'I_m.
by exists (Ordinal (proj2 (index_tuple l i) H)).
Defined.

Definition make_lens_index : index i l = lens_index. Proof. by []. Qed.

Lemma lens_indexK : tnth l lens_index = i.
Proof. by rewrite (tnth_nth i) nth_index. Qed.
End lens_index.

(* Focusing on subvector *)
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (tnth t i) t' (index i l) | i < n].
Definition focus1 (t : n.-tuple T) := inject t (f (extract t)).

Lemma focus1_out t i : i \notin l -> tnth (focus1 t) i = tnth t i.
Proof.
move=> Hi; by rewrite tnth_mktuple nth_default // memNindex ?size_tuple.
Qed.

Lemma focus1_in t : extract (focus1 t) = f (extract t).
Proof.
apply eq_from_tnth => i.
rewrite !tnth_map !tnth_ord_tuple [RHS](tnth_nth (tnth t (tnth l i))).
case: l => /= s Hu.
by rewrite index_uniq // size_tuple.
Qed.

Lemma nth_lens_index i (H : i \in l) dI (t : m.-tuple T) :
  nth dI t (index i l) = tnth t (lens_index H).
Proof. by rewrite make_lens_index -tnth_nth. Qed.

Lemma nth_lens_out dI (t : m.-tuple T) i :
  i \notin l -> nth dI t (index i l) = dI.
Proof. by move=> Hi; rewrite nth_default // memNindex // !size_tuple. Qed.

Lemma nth_extract_index dI t i :
  i \in l -> nth dI (extract t) (index i l) = tnth t i.
Proof. move=> H; by rewrite nth_lens_index tnth_map lens_indexK. Qed.

Lemma inject_extract t : inject t (extract t) = t.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple.
case/boolP: (i \in l) => [/nth_extract_index | /nth_lens_out]; exact.
Qed.
End lens.

(* Composition of lenses *)
Section lens_comp.
Variables (n m p : nat) (l1 : lens n m) (l2 : lens m p).

Definition lens_comp : lens n p.
exists (extract l2 l1).
by (rewrite map_inj_uniq ?lens_uniq // => i j /tnth_inj-> //; exact: lens_uniq).
Defined.

Lemma tnth_comp i : tnth lens_comp i = tnth l1 (tnth l2 i).
Proof. by rewrite tnth_map. Qed.

Variable (T : eqType).

Lemma extract_comp (t : n.-tuple T) :
  extract lens_comp t = extract l2 (extract l1 t).
Proof. apply eq_from_tnth => i; by rewrite !tnth_map. Qed.

(* Composition for subvectors *)

Lemma index_lens_comp i (H : index i l1 < m) :
  index i lens_comp = index (Ordinal H) l2.
Proof.
rewrite /=.
move: l1 l2 H => [l1' Hl1'] [l2' Hl2'] /= H.
set k := Ordinal H.
have/index_tuple/nth_index := H.
move/(_ i) => /= <-.
rewrite nth_tnth index_map ?map_tnth_enum //; by apply/tnth_inj.
Qed.

Lemma inject_comp (t : n.-tuple T) t' :
  inject l1 t (inject l2 (extract l1 t) t') = inject lens_comp t t'.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple.
case/boolP: (i \in l1) => Hl1.
  have/index_tuple Hl1' := Hl1.
  rewrite (index_lens_comp Hl1') nth_tnth.
  by rewrite !tnth_map tnth_ord_tuple (tnth_nth i) nth_index.
rewrite !nth_lens_out //.
apply: contra Hl1 => /mapP [j Hj] ->; by rewrite mem_tnth.
Qed.

Lemma focus1A (f : p.-tuple T -> p.-tuple T) :
  focus1 l1 (focus1 l2 f) =1 focus1 lens_comp f.
Proof. move=> t; by rewrite /focus1 inject_comp extract_comp. Qed.

(* Commutativity of subvector operations *)

Section disjoint_lenses.
Variables (q r : nat) (l : lens n q) (l' : lens n r) (t : n.-tuple T).
Hypothesis Hdisj : [disjoint l & l'].

Lemma extract_inject t' : extract l (inject l' t t') = extract l t.
Proof.
apply eq_from_tnth => i; rewrite !tnth_map tnth_ord_tuple.
by rewrite nth_lens_out // (disjointFr Hdisj) // mem_tnth.
Qed.

Lemma inject_disjointC vj vk :
  inject l' (inject l t vk) vj = inject l (inject l' t vj) vk.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_map !tnth_ord_tuple.
case/boolP: (i \in l) => Hil.
  rewrite [RHS]nth_lens_index.
  have Hil' : i \notin l' by rewrite (disjointFr Hdisj) // mem_tnth.
  by rewrite nth_lens_out // nth_lens_index.
rewrite [RHS]nth_lens_out //.
case/boolP: (i \in l') => Hil'.
  by rewrite !nth_lens_index.
by rewrite !nth_lens_out.
Qed.

Lemma focus1_commu_in (f : endo1 T q) (g : endo1 T r) i : i \in l ->
  tnth (focus1 l f (focus1 l' g t)) i = tnth (focus1 l' g (focus1 l f t)) i.
Proof.
move=> Hl; have Hl' : i \notin l' by rewrite (disjointFr Hdisj).
rewrite (focus1_out _ _ Hl') /focus1 extract_inject // !tnth_mktuple.
apply set_nth_default; by rewrite size_tuple index_tuple.
Qed.
End disjoint_lenses.

Lemma focus1C l3 (f : endo1 T m) (g : endo1 T p) :
  [disjoint l1 & l3] ->
  focus1 l1 f \o focus1 l3 g =1 focus1 l3 g \o focus1 l1 f.
Proof.
move=> Hdisj t /=.
apply eq_from_tnth => i.
case/boolP: (i \in l1) => Hl1; first exact: focus1_commu_in.
case/boolP: (i \in l3) => Hl3.
  by rewrite [RHS]focus1_commu_in // disjoint_sym.
by rewrite !focus1_out.
Qed.
End lens_comp.

(* Composition of lenses *)
Section lens_cat.
Variables (n m p : nat) (l1 : lens n m) (l2 : lens n p).
Hypothesis Hdisj : [disjoint l1 & l2].

Definition lens_cat : lens n (m+p).
exists [tuple of l1 ++ l2].
abstract
  (case: l1 l2 Hdisj => l1' Hl1 [l2' Hl2] /= Hdisj';
   rewrite cat_uniq Hl1 Hl2 andbT /=;
   by apply/hasPn => /= i /(disjointFl Hdisj') ->).
Defined.

Variable (T : eqType).

Lemma extract_cat (t : n.-tuple T) :
  extract lens_cat t = [tuple of extract l1 t ++ extract l2 t].
Proof. apply val_inj => /=. by rewrite map_cat. Qed.
End lens_cat.

From mathcomp Require Import all_algebra.
Import GRing.Theory.

Section tensor_space.
Variable (I : finType) (dI : I).

Definition nvect n T := {ffun n.-tuple I -> T}.

Section merge_lens.
Variables (n m : nat) (l : lens n m).

Lemma cards_filter (A : finType) (p : pred A) :
  #|[set a : A | p a]| = size [seq a <- enum A | p a].
Proof.
rewrite cardsE /= cardE -filter_predI.
congr size; apply eq_filter => /= i. 
by rewrite !inE andbT -topredE.
Qed.

Definition others := [seq i <- enum 'I_n | i \notin l].
Lemma size_others : size others == n - m.
Proof.
move/cardsC/addnLR: [set i in l].
rewrite [LHS]cards_filter.
rewrite (_ : filter _ _ = others); last by apply eq_filter => i; rewrite !inE.
move/card_uniqP: (lens_uniq l).
by rewrite size_tuple cardT size_enum_ord cardsE => -> ->.
Qed.

Definition lothers : lens n (n-m).
exists (Tuple size_others).
abstract (by rewrite filter_uniq // enum_uniq).
Defined.

Lemma mem_lothers i : (i \in lothers) = (i \notin l).
Proof. by rewrite mem_filter mem_enum andbT. Qed.

Definition merge_indices (v : m.-tuple I) (w : (n-m).-tuple I) :=
  [tuple nth (nth dI w (index i lothers)) v (index i l) | i < n].

Lemma merge_indices_extract (v : n.-tuple I) :
  merge_indices (extract l v) (extract lothers v) = v.
Proof.
apply eq_from_tnth => i; rewrite tnth_mktuple.
case/boolP: (i \in l) => Hi; first by rewrite nth_extract_index.
by rewrite nth_lens_out // nth_extract_index // mem_lothers.
Qed.

Lemma extract_merge v1 v2 : extract l (merge_indices v1 v2) = v1.
Proof.
apply eq_from_tnth => i.
by rewrite !tnth_map tnth_ord_tuple tnth_lensK -tnth_nth.
Qed.

Lemma extract_lothers_merge v1 v2 : extract lothers (merge_indices v1 v2) = v2.
Proof.
apply eq_from_tnth => i; rewrite !tnth_map tnth_ord_tuple nth_lens_out //.
  by rewrite tnth_lensK -tnth_nth.
move: (mem_tnth i lothers); by rewrite mem_lothers.
Qed.

Lemma merge_indices_extract_others v1 v2 :
  merge_indices v2 (extract lothers v1) = inject l v1 v2.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_map !tnth_ord_tuple.
case/boolP: (i \in l) => Hil.
  by rewrite !nth_lens_index.
rewrite nth_lens_out // [RHS]nth_lens_out //.
rewrite -mem_lothers in Hil.
by rewrite nth_lens_index tnth_map lens_indexK.
Qed.

Lemma extract_merge_disjoint p (l' : lens n p) vi vj :
  [disjoint l & l'] ->
  extract l' (merge_indices vj (extract lothers vi)) = extract l' vi.
Proof.
move=> Hdisj; apply eq_from_tnth => i.
rewrite !tnth_map tnth_ord_tuple.
have Hilo : tnth l' i \in lothers.
  by rewrite mem_lothers (disjointFl Hdisj) // mem_tnth.
rewrite nth_lens_out ?nth_lens_index //.
- by rewrite tnth_map lens_indexK.
- by rewrite -mem_lothers.
Qed.

Variables T : Type.

Definition curry (st : nvect n T) : nvect m (nvect (n-m) T) :=
  [ffun v : m.-tuple I =>
   [ffun w : (n-m).-tuple I => st (merge_indices v w)]].

Definition uncurry (st : nvect m (nvect (n-m) T)) : nvect n T :=
  [ffun v : n.-tuple I => st (extract l v) (extract lothers v)].

Lemma curryK : cancel uncurry curry.
Proof.
move=> v; apply/ffunP => v1; apply/ffunP => v2.
by rewrite !ffunE extract_merge extract_lothers_merge.
Qed.

Lemma uncurryK : cancel curry uncurry.
Proof.
move=> v; apply/ffunP => w.
by rewrite !ffunE merge_indices_extract.
Qed.
End merge_lens.

Let vsz m := #|I| ^ m.

Section index_of_vec_bij.
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
  move <-. by rewrite expn0.
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
elim: m i => [|m IH] /=.
  by case; rewrite expn0 // ltnS.
move=> i Hi.
rewrite enum_valK IH /=.
  by rewrite addnC mulnC -divn_eq.
rewrite -(ltn_pmul2r H).
apply (leq_ltn_trans (leq_trunc_div _ _)).
by rewrite mulnC -expnS.
Qed.

Lemma vec_of_indexK m : cancel (@vec_of_index m) (@index_of_vec m).
Proof.
rewrite /index_of_vec /vec_of_index /= => -[i] Hi.
apply val_inj => /=.
by rewrite revK vec_of_index_recK.
Qed.

Lemma index_of_vecK m : cancel (@index_of_vec m) (@vec_of_index m).
Proof.
rewrite /index_of_vec /vec_of_index => -[t Ht].
apply/val_inj => /=.
rewrite -[RHS]revK.
congr rev.
move/eqP: Ht; rewrite -size_rev.
elim: (rev t) m => {t} [|i t IH] m <- //=.
congr (_ :: _).
  rewrite (_ : Ordinal _ = enum_rank i) ?enum_rankK //.
  apply val_inj => /=.
  by rewrite addnC mulnC modnMDl modn_small.
rewrite divnDr.
  by rewrite divn_small // add0n mulKn // IH.
apply/dvdn_mulr/dvdnn.
Qed.

Lemma index_of_vec_bij m : bijective (@index_of_vec m).
Proof.
exists (@vec_of_index m); [exact: index_of_vecK | exact: vec_of_indexK].
Qed.
End index_of_vec_bij.

Variable (R : comRingType).
Definition endofun m := forall T : lmodType R, nvect m T -> nvect m T.
Definition endo m := forall T : lmodType R, {linear nvect m T -> nvect m T}%R.
(* Actually, need the property (naturality)
 forall (f : endo m) (T1 T2 : lmodType R) (h : {linear T1 -> T2}),
   map h \o f T1 = f T2 \o map h
which is eqauivalent to the fact f = nvendo M for a square matrix M.
*)
Definition nsquare m := nvect m (nvect m R^o).

Definition nvendo_fun m (M : nsquare m) : endofun m :=
  fun T v =>
    [ffun vi : m.-tuple I => \sum_(vj : m.-tuple I) (M vi vj : R) *: v vj]%R.

Lemma nvendo_is_linear m M T : linear (@nvendo_fun m M T).
Proof.
move=> x y z.
apply/ffunP => vi; rewrite !ffunE.
rewrite scaler_sumr -big_split /=.
apply eq_bigr => vj _.
by rewrite ffunE scalerDr scalerA mulrC -scalerA ffunE.
Qed.

Definition nvendo m (M : nsquare m) : endo m :=
  fun T => Linear (@nvendo_is_linear m M T).

Definition mxnsquare m (M : 'M[R]_(vsz m,vsz m)) : nsquare m :=
  [ffun vi => [ffun vj => M (index_of_vec vi) (index_of_vec vj)]].

Definition mxendo m (M : 'M[R]_(vsz m,vsz m)) := nvendo (mxnsquare M).

Definition vec_nvect m (X : 'rV[R]_(vsz m)) : nvect m R^o :=
  [ffun vi => X ord0 (index_of_vec vi)].

Definition nvect_vec H m (X : nvect m R^o) : 'rV[R]_(vsz m) :=
  \row_i X (vec_of_index H i).

Lemma nvect_vector (H : #|I| > 0) n : Vector.axiom (vsz n) (nvect n R^o).
Proof.
exists (@nvect_vec H n).
- move=> x /= y z. apply/rowP => i. by rewrite !(ffunE,mxE).
- exists (@vec_nvect n).
  + move=> v. apply/ffunP => vi. by rewrite !(ffunE,mxE) index_of_vecK.
  + move=> X. apply/rowP => i. by rewrite !(ffunE,mxE) vec_of_indexK.
Qed.

Section curry_linear.
Variables (n m : nat) (l : lens n m) (T : lmodType R).

Lemma curry_is_linear : linear (curry l (T:=T)).
Proof. move=>x y z; apply/ffunP=>vi; apply/ffunP =>vj; by rewrite !ffunE. Qed.

Lemma uncurry_is_linear : linear (uncurry l (T:=T)).
Proof. move => x y z; apply/ffunP=> vi; by rewrite !ffunE. Qed.
End curry_linear.

Section focus.
Definition focus_fun n m (l : lens n m) (tr : endo m) : endofun n :=
  fun T (v : nvect n T) => uncurry l (tr _ (curry l v)).

Lemma focus_is_linear n m l tr T : linear (@focus_fun n m l tr T).
Proof.
move=> x y z.
apply/ffunP => vi; rewrite !ffunE.
rewrite /= (_ : curry l (T := T) = Linear (curry_is_linear l (T:=T))) //.
by rewrite !linearP !ffunE.
Qed.

Definition focus n m l tr : endo n :=
  fun T => Linear (@focus_is_linear n m l tr T).

Variables (T : lmodType R) (n m p : nat) (l : lens n m).

Section focusC.
Variable l' : lens n p.
Hypothesis Hdisj : [disjoint l & l'].

(* horizontal composition of endomorphisms *)
Lemma focusC (tr : nsquare m) (tr' : nsquare p) (v : nvect n T) :
  focus l (nvendo tr) _ (focus l' (nvendo tr') _ v) =
  focus l' (nvendo tr') _ (focus l (nvendo tr) _ v).
Proof.
rewrite /focus.
apply/ffunP => /= vi.
rewrite !ffunE !sum_ffunE.
under eq_bigr do rewrite !ffunE !sum_ffunE scaler_sumr.
rewrite exchange_big /=.
apply eq_bigr => /= vj _.
rewrite !ffunE !sum_ffunE scaler_sumr.
apply eq_bigr => /= vk _.
rewrite !ffunE !scalerA [in RHS]mulrC.
congr (tr _ vk * tr' _ vj *: v _)%R.
- by rewrite extract_merge_disjoint // disjoint_sym.
- by rewrite extract_merge_disjoint.
- by rewrite !merge_indices_extract_others inject_disjointC.
Qed.
End focusC.

Section focusA.
Variable l' : lens m p.

Definition lothers_comp := lothers (lens_comp l l').

Lemma others_in_l_present i :
  tnth (lens_comp l (lothers l')) i \in lothers_comp.
Proof.
rewrite mem_lothers.
apply/mapP => -[k Hk].
rewrite tnth_comp => /tnth_inj Hi.
move: (mem_tnth i (lothers l')).
by rewrite mem_lothers Hi (Hk,lens_uniq).
Qed.

Definition others_in_l :=
  [tuple lens_index (others_in_l_present i) | i < m - p].

Lemma uniq_others_in_l : uniq (others_in_l).
Proof.
apply/tnth_inj => i j.
rewrite !tnth_mktuple.
set k := lens_index _.
case.
move/(f_equal (nth (widen_ord (leq_subr _ _) k) (others (lens_comp l l')))).
rewrite !nth_index; try by rewrite others_in_l_present.
move/tnth_inj => -> //.
rewrite map_inj_uniq ?(lens_uniq (lothers l')) //.
exact/tnth_inj/lens_uniq.
Qed.

Definition lothers_in_l : lens (n-p) (m-p).
exists others_in_l.
exact uniq_others_in_l.
Defined.

Lemma cast_lothers_notin_l : n - p - (m - p) = n - m.
Proof. rewrite subnBA ?subnK // lens_leq //. exact: (lens_comp l l'). Qed.

Lemma size_lothers_notin_l : size (lothers lothers_in_l) == n - m.
Proof. by rewrite size_tuple cast_lothers_notin_l. Qed.

Definition lothers_notin_l : lens (n-p) (n-m).
exists (Tuple size_lothers_notin_l).
exact: (lens_uniq (lothers lothers_in_l)).
Defined.

Lemma lothers_in_l_comp :
  lens_comp lothers_comp lothers_in_l = lens_comp l (lothers l').
Proof.
apply/val_inj/eq_from_tnth => i.
rewrite !tnth_map tnth_ord_tuple.
have dm : 'I_m := widen_ord (leq_subr _ _) i.
have dn : 'I_n := widen_ord (lens_leq l) dm.
rewrite (tnth_nth dn) nth_index tnth_map // mem_lothers.
apply/negP => /mapP /= [j] Hj /tnth_inj Hj'.
have := mem_tnth i (lothers l').
by rewrite Hj' ?lens_uniq // mem_lothers Hj.
Qed.

Lemma sorted_others q r (ln : lens q r) : sorted ord_ltn (others ln).
Proof. exact/sorted_filter/sorted_enum/ltn_trans. Qed.

Lemma lothers_notin_l_comp :
  lens_comp lothers_comp lothers_notin_l = lothers l.
Proof.
apply/val_inj/val_inj => /=.
apply: (sorted_eq (leT:=ord_ltn) ltn_trans).
- move=> x y /andP[]. by rewrite /ord_ltn /= (ltnNge y) => /ltnW ->.
- apply/sorted_comp/sorted_others. exact: ltn_trans.
- exact: sorted_others.
- exact: sorted_others.
- apply uniq_perm.
    exact: (lens_uniq (lens_comp lothers_comp lothers_notin_l)).
    exact: (lens_uniq (lothers l)).
  move=> i.
  rewrite mem_lothers.
  apply/mapP; case: ifPn => Hi.
  + have /tnthP[j Hj]:  i \in lothers_comp.
      rewrite mem_lothers.
      apply: contra Hi => /mapP [j Hj] ->.
      exact: mem_tnth.
    exists j => //.
    rewrite mem_lothers.
    apply: contra Hi => /mapP [k _].
    rewrite Hj => ->.
    have Hol := others_in_l_present k.
    by rewrite lens_indexK tnth_map mem_tnth.
  + rewrite negbK in Hi.
    case=> j; rewrite mem_lothers => Hj Hi'.
    apply/negP: Hj; rewrite negbK.
    case/tnthP: Hi => k Hk.
    have Hk' : k \in lothers l'.
      rewrite mem_lothers.
      apply/tnthP => -[h] Hh.
      have : i \in lothers_comp by rewrite Hi' mem_tnth.
      by rewrite Hk Hh -tnth_comp mem_lothers mem_tnth.
    apply/tnthP.
    exists (lens_index Hk').
    apply (tnth_inj _ (lens_uniq lothers_comp)).
    rewrite -tnth_comp lothers_in_l_comp tnth_comp.
    by rewrite -Hi' Hk lens_indexK.
Qed.    

Lemma extract_lothers_comp (v : n.-tuple I) :
  extract lothers_comp v =
  merge_indices lothers_in_l
                (extract (lens_comp lothers_comp lothers_in_l) v)
                (extract (lens_comp lothers_comp (lothers lothers_in_l)) v).
Proof. by rewrite !extract_comp (merge_indices_extract lothers_in_l). Qed.

Lemma merge_indices_comp vj vk (vl : (n-p - (m-p)).-tuple I)
                               (vm : (n-m).-tuple I) :
  vl = vm :> seq I ->
  merge_indices (lens_comp l l') vj (merge_indices lothers_in_l vk vl) =
  merge_indices l (merge_indices l' vj vk) vm.
Proof.
rewrite /merge_indices => Hlm.
apply eq_mktuple => i.
case/boolP: (i \in lens_comp l l') => Hi.
  case/mapP: Hi => j Hj ->.
  rewrite tnth_lensK -tnth_nth tnth_mktuple index_map ?(nth_lens_index Hj) //.
  exact/tnth_inj/lens_uniq.
rewrite nth_lens_out //.
have Hilo : i \in lothers_comp by rewrite mem_lothers.
rewrite nth_lens_index tnth_mktuple.
case/boolP: (i \in l) => Hil.
  rewrite (nth_lens_index Hil) tnth_mktuple.
  have Hill' : lens_index Hil \notin l'.
    apply: contra Hi => Hill'.
    apply/mapP. exists (lens_index Hil) => //.
    by rewrite lens_indexK.
  rewrite [RHS]nth_lens_out //.
  have Hlol' : lens_index Hil \in lothers l' by rewrite mem_lothers.
  rewrite (nth_lens_index Hlol').
  have <- : tnth lothers_in_l (lens_index Hlol') = lens_index Hilo.
    apply (tnth_inj _ (lens_uniq lothers_comp)).
    by rewrite -tnth_comp lothers_in_l_comp tnth_comp !lens_indexK.
  by rewrite tnth_lensK -tnth_nth.
rewrite [RHS]nth_lens_out //.
have Hillo : lens_index Hilo \notin lothers_in_l.
  apply: contra Hil.
  case/tnthP => j /(f_equal (tnth lothers_comp)).
  rewrite -tnth_comp lothers_in_l_comp lens_indexK => ->.
  by rewrite tnth_comp mem_tnth.
rewrite [LHS]nth_lens_out //.
congr nth => //.
have Hillo' : lens_index Hilo \in lothers_notin_l by rewrite mem_lothers.
have Hill : i \in lothers l by rewrite mem_lothers.
rewrite (make_lens_index Hillo') (make_lens_index Hill).
congr val.
apply (tnth_inj _ (lens_uniq (lothers l))).
by rewrite -[in LHS]lothers_notin_l_comp tnth_comp !lens_indexK.
Qed.

(* associativity of actions of lenses *)
Lemma focusA (tr : nsquare p) (v : nvect n T) :
  focus (lens_comp l l') (nvendo tr) _ v = focus l (focus l' (nvendo tr)) _ v.
Proof.
rewrite /focus.
apply/ffunP => /= vi.
rewrite !ffunE extract_lothers_comp -!extract_comp.
rewrite -lothers_in_l_comp -lothers_notin_l_comp !sum_ffunE.
apply eq_bigr => /= vj _.
rewrite !ffunE.
congr (_ *: v _)%R.
exact: merge_indices_comp.
Qed.
End focusA.
End focus.

Section application.
Let lmodType_C := Type.
Let transformation m := forall T : lmodType_C, nvect m T -> nvect m T.
(*Definition transformation m : forall T : normedLmodType C,
 {unitary nvect m T -> nvect m T}.*)
End application.
End tensor_space.

(* Computable Ordinal constants *)
Definition succO {n} := lift (@ord0 n).
Fixpoint addnO {n} m (p : 'I_n) : 'I_(m+n) :=
  match m as x return 'I_(x+n) with
  | 0 => p
  | m.+1 => cast_ord (esym (addSnnS m n)) (addnO m (succO p))
  end.
Definition INO {n} m := addnO m (@ord0 n).
Notation "n '%:O'" := (INO n) (at level 2, left associativity, format "n %:O").

Notation "[ 'lens' x1 ; .. ; xn ]" :=
  (@mkLens _ _ [tuple of x1%:O :: .. [:: xn%:O] ..] erefl).

Section ordinal_examples.
Eval compute in uniq [tuple 0%:O; 1%:O; 2%:O]. (* = true *)

Let lens3_23 : lens 3 2 := [lens 1; 2].
End ordinal_examples.
