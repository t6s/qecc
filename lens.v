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

Lemma tnth_inj (A : eqType) n (t : n.-tuple A) :
  reflect (injective (tnth t)) (uniq t).
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

Lemma index_lens i : (index i l < m) <-> (i \in val l).
Proof. by rewrite -index_mem size_tuple. Qed.

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
move/[dup] => Hi /index_lens Hi'.
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
move/(index_lens (mkLens Hl1'))/nth_index: (H).
move/(_ i) => /= <-.
rewrite map_comp nth_tnth index_map ?map_tnth_enum //; by apply/tnth_inj.
Qed.

Lemma inject_comp (t : n.-tuple T) t' :
  inject l1 t (inject l2 (extract l1 t) t') = inject lens_comp t t'.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple.
case/boolP: (i \in val l1) => Hl1.
  move/index_lens: (Hl1) => Hl1'.
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
apply set_nth_default; by rewrite size_tuple index_lens.
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

Section tensor_space.
Variable (I : finType) (dI : I).

Definition nvect n T := {ffun n.-tuple I -> T}.
Definition endo m := forall T, nvect m T -> nvect m T.

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

Variables (T : Type).

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

Section focus.
Definition focus n m (l : lens n m) (tr : endo m) : endo n :=
  fun T (v : nvect n T) => uncurry l (tr _ (curry l v)).

(* horizontal composition of endomorphisms *)
Lemma focusC T n m p (l : lens n m) (l' : lens n p)
      (tr : endo m) (tr' : endo p) (v : nvect n T) :
  [disjoint val l & val l'] -> 
  focus l tr (focus l' tr' v) = focus l' tr' (focus l tr v).
Abort.

(* associativity of actions of lenses *)
Lemma focusA T n m p (l : lens n m) (l' : lens m p)
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
