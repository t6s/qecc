From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  rewrite (_ : index _ _ = Ordinal Hi) // -tnth_nth tnth_mktuple.
  by rewrite (tnth_nth i) nth_index // -index_mem size_tuple.
by rewrite nth_default // leqNgt size_tuple.
Qed.
End lens.

Lemma tnth_inj (A : eqType) n (t : n.-tuple A) :
  reflect (injective (tnth t)) (uniq t).
Proof.
apply: (iffP idP).
- move=> /uniqP Hu i j.
  rewrite (tnth_nth (tnth t i)) (tnth_nth (tnth t i) t j).
  move/(Hu (tnth t i) i j)/val_inj => -> //; by rewrite inE size_tuple.
- case: t => -[|a t] // Hlen.
  move=> Hinj.
  apply/(uniqP a) => i j.
  rewrite !inE !size_tuple => Hi Hj.
  move: (Hinj (Ordinal Hi) (Ordinal Hj)).
  by rewrite !(tnth_nth a) /= => /[apply] -[].
Qed.

Section lens_comp.

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
rewrite (_ : index i l1' = k) // -tnth_nth /= index_map.
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
  rewrite (index_lens_comp Hl1').
  rewrite [X in nth _ _ X](_ : index i _ = Ordinal Hl1') // -tnth_nth.
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

End lens_comp.
