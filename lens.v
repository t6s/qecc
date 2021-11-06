From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma addnLR m n p : m + n = p -> n = p - m.
Proof. move/(f_equal (subn^~ m)); by rewrite addKn. Qed.

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

Section lens.
Variables (T : Type) (n m : nat).

Record lens := mkLens {lens_t :> m.-tuple 'I_n ; lens_uniq : uniq lens_t}.
Canonical len_subType := Eval hnf in [subType for lens_t].

Definition endo1 := m.-tuple T -> m.-tuple T.

Variables (l : lens) (f : endo1).

Definition extract (t : n.-tuple T) := [tuple tnth t (tnth l i) | i < m].

(* Focusing on subvector *)
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (tnth t i) t' (index i l) | i < n].
Definition focus1 (t : n.-tuple T) := inject t (f (extract t)).

Lemma focus1_out t i : i \notin val l -> tnth (focus1 t) i = tnth t i.
Proof.
move=> Hi; by rewrite tnth_mktuple nth_default // memNindex ?size_tuple.
Qed.

Lemma focus1_in t : extract (focus1 t) = f (extract t).
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple [RHS](tnth_nth (tnth t (tnth l i))).
case: l => /= s Hu.
by rewrite index_uniq // size_tuple.
Qed.

Lemma nth_extract_index dI t i :
  i \in val l -> nth dI (extract t) (index i l) = tnth t i.
Proof.
move/[dup] => Hi /index_tuple Hi'.
by rewrite nth_tnth tnth_mktuple (tnth_nth i) /= nth_index.
Qed.

Lemma nth_extract_out dI t i :
  i \notin val l -> nth dI (extract t) (index i l) = dI.
Proof. by move=> Hi; rewrite nth_default // memNindex // !size_tuple. Qed.

Lemma inject_extract t : inject t (extract t) = t.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple.
case/boolP: (i \in val l) => [/nth_extract_index | /nth_extract_out]; exact.
Qed.
End lens.

(* Composition of lenses *)
Section lens_comp.
Variables (n m p : nat) (l1 : lens n m) (l2 : lens m p).

Definition lens_comp : lens n p.
exists (extract l2 l1).
abstract (case: l1 l2 => l1' Hl1 [l2' Hl2] /=;
          rewrite map_inj_uniq ?enum_uniq // => i j /tnth_inj /tnth_inj; exact).
Defined.

Variable (T : eqType).

Lemma extract_comp (t : n.-tuple T) :
  extract lens_comp t = extract l2 (extract l1 t).
Proof. apply eq_from_tnth => i; by rewrite !tnth_mktuple. Qed.

(* Composition for subvectors *)
Lemma index_lens_comp i (H : index i l1 < m) :
  index i lens_comp = index (Ordinal H) l2.
Proof.
rewrite /=.
move: l1 l2 H => [l1' Hl1'] [l2' Hl2'] /= H.
set k := Ordinal H.
move/index_tuple/nth_index: (H).
move/(_ i) => /= <-.
rewrite map_comp nth_tnth index_map ?map_tnth_enum //; by apply/tnth_inj.
Qed.

Lemma inject_comp (t : n.-tuple T) t' :
  inject l1 t (inject l2 (extract l1 t) t') = inject lens_comp t t'.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple.
case/boolP: (i \in val l1) => Hl1.
  move/index_tuple: (Hl1) => Hl1'.
  rewrite (index_lens_comp Hl1') nth_tnth.
  by rewrite !tnth_mktuple (tnth_nth i) nth_index.
rewrite !nth_default // memNindex ?size_tuple //.
apply: contra Hl1 => /mapP [j Hj] ->; by rewrite mem_tnth.
Qed.

Lemma focus1_comp (f : p.-tuple T -> p.-tuple T) :
  focus1 l1 (focus1 l2 f) =1 focus1 lens_comp f.
Proof. move=> t; by rewrite /focus1 inject_comp extract_comp. Qed.

(* Commutativity of subvector operations *)

Section focus_commu_in.
Variables (q r : nat) (l : lens n q) (l' : lens n r) (t : n.-tuple T).
Hypothesis Hdisj : [disjoint val l & val l'].

Lemma extract_inject t' : extract l (inject l' t t') = extract l t.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple nth_default //.
by rewrite memNindex ?size_tuple // (disjointFr Hdisj) // mem_tnth.
Qed.

Lemma focus1_commu_in (f : endo1 T q) (g : endo1 T r) i : i \in val l ->
  tnth (focus1 l f (focus1 l' g t)) i = tnth (focus1 l' g (focus1 l f t)) i.
Proof.
move=> Hl; have Hl' : i \notin val l' by rewrite (disjointFr Hdisj).
rewrite (focus1_out _ _ Hl') /focus1 extract_inject // !tnth_mktuple.
apply set_nth_default; by rewrite size_tuple index_tuple.
Qed.
End focus_commu_in.

Variables (l3 : lens n p) (f : endo1 T m) (g : endo1 T p).
Hypothesis Hdisj : [disjoint val l1 & val l3].

Lemma focus1_commu : focus1 l1 f \o focus1 l3 g =1 focus1 l3 g \o focus1 l1 f.
Proof.
move=> t /=.
apply eq_from_tnth => i.
case/boolP: (i \in val l1) => Hl1; first exact: focus1_commu_in.
case/boolP: (i \in val l3) => Hl3.
  by rewrite [RHS]focus1_commu_in // disjoint_sym.
by rewrite !focus1_out.
Qed.
End lens_comp.

From mathcomp Require Import all_algebra.

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

Definition others := [seq i <- enum 'I_n | i \notin val l].
Lemma size_others : size others == n - m.
Proof.
move/cardsC/addnLR: [set i in val l].
rewrite [LHS]cards_filter.
rewrite (_ : filter _ _ = others); last by apply eq_filter => i; rewrite !inE.
move/card_uniqP: (lens_uniq l).
by rewrite size_tuple cardT size_enum_ord cardsE => -> ->.
Qed.

Definition lothers : lens n (n-m).
exists (Tuple size_others).
abstract (by rewrite filter_uniq // enum_uniq).
Defined.

Definition merge_indices (v : m.-tuple I) (w : (n-m).-tuple I) :=
  [tuple nth (nth dI w (index i lothers)) v (index i l) | i < n].

Lemma merge_indices_extract (v : n.-tuple I) :
  merge_indices (extract l v) (extract lothers v) = v.
Proof.
apply eq_from_tnth => i; rewrite tnth_mktuple.
case/boolP: (i \in val l) => Hi; first by rewrite nth_extract_index.
by rewrite nth_extract_out // nth_extract_index // mem_filter Hi /= mem_enum.
Qed.

Lemma tnth_lensK p (lp : lens n p) i : index (tnth lp i) lp = i.
Proof.
by rewrite (tnth_nth (tnth lp i)) index_uniq // (lens_uniq,size_tuple).
Qed.

Lemma extract_merge v1 v2 : extract l (merge_indices v1 v2) = v1.
Proof.
apply eq_from_tnth => i; by rewrite !tnth_mktuple tnth_lensK -tnth_nth.
Qed.

Lemma extract_lothers_merge v1 v2 : extract lothers (merge_indices v1 v2) = v2.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple nth_default.
  by rewrite tnth_lensK -tnth_nth.
rewrite memNindex ?size_tuple //.
move: (mem_tnth i lothers); rewrite mem_filter; by case/andP.
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

Variable (R : ringType).
Definition endo m := forall T : lmodType R, nvect m T -> nvect m T.

Definition nvendo m (M : nvect m (nvect m R^o)) : endo m :=
  fun T (v : nvect m T) =>
    [ffun vi : m.-tuple I => \sum_(vj : m.-tuple I) (M vi vj : R) *: v vj]%R.

Definition mxnvect m (M : 'M[R]_(vsz m,vsz m)) : nvect m (nvect m R^o) :=
  [ffun vi => [ffun vj => M (index_of_vec vi) (index_of_vec vj)]].

Definition mxendo m (M : 'M[R]_(vsz m,vsz m)) := nvendo (mxnvect M).

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

Section focus.
Definition focus n m (l : lens n m) (tr : endo m) : endo n :=
  fun T (v : nvect n T) => uncurry l (tr _ (curry l v)).

Variables (T : lmodType R) (n m p : nat).

(* horizontal composition of endomorphisms *)
Lemma focusC (l : lens n m) (l' : lens n p)
      (tr : endo m) (tr' : endo p) (v : nvect n T) :
  [disjoint val l & val l'] -> 
  focus l tr (focus l' tr' v) = focus l' tr' (focus l tr v).
Abort.

(* associativity of actions of lenses *)
Lemma focusA (l : lens n m) (l' : lens m p)
      (tr : endo p) (v : nvect n T) :
  focus (lens_comp l l') tr v = focus l (focus l' tr) v.
Abort.
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
