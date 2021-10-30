From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Variables (l : lens) (f : m.-tuple T -> m.-tuple T).

Definition extract (t : n.-tuple T) := [tuple tnth t (tnth l i) | i < m].
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (tnth t i) t' (index i l) | i < n].
Definition focus (t : n.-tuple T) := inject t (f (extract t)).

Lemma focus_out t i : i \notin val l -> tnth (focus t) i = tnth t i.
Proof.
move=> Hi.
by rewrite tnth_mktuple nth_default // memNindex // !size_tuple.
Qed.

Lemma focus_in t : extract (focus t) = f (extract t).
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple [RHS](tnth_nth (tnth t (tnth l i))).
case: l => /= s Hu.
by rewrite index_uniq // size_tuple.
Qed.

Lemma inject_extract t : inject t (extract t) = t.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple.
case/boolP: (index i l < m) => Hi.
  rewrite nth_tnth tnth_mktuple (tnth_nth i) /=.
  by rewrite nth_index // -index_mem size_tuple.
by rewrite nth_default // leqNgt size_tuple.
Qed.
End lens.

Section lens_comp.

(* Composition of lenses *)

Variables (n m p : nat) (l1 : lens n m) (l2 : lens m p).

Definition lens_comp : lens n p.
exists (extract l2 l1).
abstract (case: l1 l2 => l1' Hl1 [l2' Hl2] /=;
          rewrite map_inj_uniq ?enum_uniq // => i j /tnth_inj /tnth_inj; exact).
Defined.

Lemma index_lens_comp i (H : index i l1 < m) :
  index i lens_comp = index (Ordinal H) l2.
Proof.
rewrite /=.
move: l1 l2 H => [l1' Hl1'] [l2' Hl2'] /= H.
set k := Ordinal H.
move: (H).
rewrite -[X in _ < X](size_tuple l1') index_mem map_comp => /nth_index.
move/(_ i) <-.
rewrite nth_tnth index_map.
  by rewrite map_tnth_enum.
by apply/tnth_inj.
Qed.

Variable (T : eqType).

Lemma inject_comp (t : n.-tuple T) t' :
  inject l1 t (inject l2 (extract l1 t) t') = inject lens_comp t t'.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple.
case/boolP: (i \in val l1) => Hl1.
  move: (Hl1).
  rewrite -index_mem size_tuple => Hl1'.
  rewrite (index_lens_comp Hl1') nth_tnth.
  by rewrite !tnth_mktuple (tnth_nth i) nth_index.
rewrite nth_default; last first.
  rewrite -index_mem -leqNgt size_tuple in Hl1.
  by rewrite size_tuple.
rewrite nth_default // leqNgt size_tuple.
rewrite -[X in _ < X](size_tuple lens_comp) index_mem.
apply: contra Hl1 => /mapP [j Hj] ->.
by rewrite mem_tnth.
Qed.

Lemma extract_comp (t : n.-tuple T) :
  extract lens_comp t = extract l2 (extract l1 t).
Proof. apply eq_from_tnth => i; by rewrite !tnth_mktuple. Qed.

Lemma focus_comp (f : p.-tuple T -> p.-tuple T) :
  focus l1 (focus l2 f) =1 focus lens_comp f.
Proof. move=> t; by rewrite /focus inject_comp extract_comp. Qed.

(* Commutativity of focussed operations *)

Variables (l3 : lens n p).
Variable (f : m.-tuple T -> m.-tuple T) (g : p.-tuple T -> p.-tuple T).
Hypothesis Hdisj : [disjoint val l1 & val l3].

Lemma extract_inject (t : n.-tuple T) t' :
  extract l1 (inject l3 t t') = extract l1 t.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple.
rewrite nth_default // leqNgt size_tuple -[X in _ < X](size_tuple l3).
by rewrite index_mem (disjointFr Hdisj) // mem_tnth.
Qed.

Lemma extract_inject' (t : n.-tuple T) t' :
  extract l3 (inject l1 t t') = extract l3 t.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple.
rewrite nth_default // leqNgt size_tuple -[X in _ < X](size_tuple l1).
by rewrite index_mem (disjointFl Hdisj) // mem_tnth.
Qed.

Lemma focus_commu : focus l1 f \o focus l3 g =1 focus l3 g \o focus l1 f.
Proof.
move=> t /=.
apply eq_from_tnth => i.
case/boolP: (i \in val l1) => Hl1.
  have Hl3 : i \notin val l3 by rewrite (disjointFr Hdisj).
  rewrite (focus_out _ _ Hl3).
  rewrite /focus extract_inject !tnth_mktuple.
  rewrite (set_nth_default (tnth t i)) //.
  by rewrite size_tuple -[X in _ < X](size_tuple l1) index_mem.
case/boolP: (i \in val l3) => Hl3.
  rewrite (focus_out _ _ Hl1).
  rewrite /focus extract_inject' !tnth_mktuple.
  rewrite (set_nth_default (tnth t i)) //.
  by rewrite size_tuple -[X in _ < X](size_tuple l3) index_mem.
by rewrite !focus_out.
Qed.

End lens_comp.

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

Section state.
Variable (I : finType) (dI : I).

Definition nvect n T := {ffun n.-tuple I -> T}.

Section merge_lens.

Variables (n m : nat) (l : lens n m).

Lemma cards_filter (A : finType) (p : pred A) :
  size [seq a <- enum A | p a] = #|[set a : A | p a]|.
Proof.
rewrite cardsE /= cardE -filter_predI.
congr size; apply eq_filter => /= i. 
by rewrite !inE andbT -[RHS]topredE.
Qed.

Definition others := [seq i <- enum 'I_n | i \notin val l].
Lemma size_others : size others == n - m.
Proof.
move: (cardsC [set i in val l]).
move/(f_equal (subn^~  #|[set i in val l]|)).
rewrite addKn /setC -cards_filter.
rewrite (_ : filter _ _ = others); last by apply eq_filter => i; rewrite !inE.
move->.
rewrite cardT size_enum_ord cardsE.
move/card_uniqP: (lens_uniq l) => ->.
by rewrite size_tuple.
Qed.

Definition lothers : lens n (n-m).
exists (Tuple size_others).
abstract (by rewrite filter_uniq // enum_uniq).
Defined.

Definition merge_indices (v : m.-tuple I) (w : (n-m).-tuple I) :=
  [tuple nth (nth dI w (index i lothers)) v (index i l) | i < n].

Lemma merge_indices_ok (v : n.-tuple I) :
  merge_indices (extract l v) (extract lothers v) = v.
Proof.
apply eq_from_tnth => i.
rewrite tnth_mktuple.
case/boolP: (i \in val l) => Hi.
  move: (Hi); rewrite -index_mem size_tuple => Hi'.
  by rewrite nth_tnth tnth_mktuple (tnth_nth i) nth_index.
rewrite nth_default; last first.
  by rewrite -index_mem !size_tuple -leqNgt in Hi *.
have Hc : i \in val lothers.
  by rewrite mem_filter Hi /= mem_enum.
move: (Hc); rewrite -index_mem size_tuple => Hc'.
by rewrite nth_tnth tnth_mktuple (tnth_nth i) /= nth_index.
Qed.
End merge_lens.

Definition curry T n m (l :lens n m) (st : nvect n T)
  : nvect m (nvect (n-m) T) :=
  [ffun v : m.-tuple I =>
   [ffun w : (n-m).-tuple I => st (merge_indices l v w)]].

Section application.
Let lmodType_C := Type.
Let transformation m : forall T : lmodType_C, nvect m T -> nvect m T.
(*Definition transformation m : forall T : normedLmodType C,
 {unitary nvect m T -> nvect m T}.*)
End application.
End state.


