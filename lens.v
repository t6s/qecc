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

Eval compute in uniq [tuple 0%:O; 1%:O; 2%:O]. (* = true *)

Notation "[ 'lens' x1 ; .. ; xn ]" :=
  (@mkLens _ _ [tuple of x1%:O :: .. [:: xn%:O] ..] erefl).

Definition lens3_23 : lens 3 2 := [lens 1; 2].

Section state.
Variable (I : finType) (dI : I).

Definition nvect n T := {ffun n.-tuple I -> T}.

Section merge_lens.

Variables (n m : nat) (l : lens n m).

Definition others := [seq i <- enum 'I_n | i \notin val l].

Definition rank_others i := i - size [seq j <- l | (j : 'I_n) < i].

Definition merge_indices (v : m.-tuple I) (w : (n-m).-tuple I) :=
  [tuple nth (nth dI w (rank_others i)) v (index i l) | i < n].

Definition select_other i :=
  i + \max_(j < size l | rank_others (i + j) < i) j.+1.

Definition extract_others (v : n.-tuple I) : (n-m).-tuple I :=
  [tuple nth dI v (select_other i) | i < n - m].

Lemma merge_extract (v : n.-tuple I) :
  merge_indices (extract l v) (extract_others v) = v.
Proof.
apply eq_from_tnth => i.
rewrite tnth_mktuple.
case/boolP: (i \in val l) => Hi.
  move: (Hi); rewrite -index_mem size_tuple => Hi'.
  rewrite (_ : index i l = Ordinal Hi') // -tnth_nth.
  by rewrite tnth_mktuple (tnth_nth i) nth_index.
rewrite /rank_others nth_default; last first.
  by rewrite size_tuple leqNgt -[X in _ < X](size_tuple (val l)) index_mem.
have Hc : i - size [seq j <- l | (j : 'I_n) < i] < n - m.
  admit.
rewrite (_ : i - _ = Ordinal Hc) //.
rewrite -tnth_nth tnth_mktuple (tnth_nth dI).
congr nth.
rewrite /select_other /=.
have Hci (k : 'I_n) : size [seq j <- l | (j : 'I_n) < k] <= k.
  apply (@leq_trans (size (map (widen_ord (ltnW (ltn_ord k))) (enum 'I_k)))).
    have : uniq [seq j <- l | (j : 'I_n) < k].
      apply filter_uniq. exact: lens_uniq.
    move/uniq_leq_size; apply => j.
    rewrite mem_filter => /andP[Hjk _].
    apply/mapP.
    exists (Ordinal Hjk).
      by rewrite mem_enum.
    exact/val_inj.
  by rewrite size_map size_enum_ord.
set maxj := \max_(j < size l | _) _.
have <- : maxj = size [seq j <- l | (j : 'I_n) < i].
  subst maxj.
  apply/eqP.
  rewrite eqn_leq.
  apply/andP; split.
    apply/bigmax_leqP => /= j.
    rewrite ltn_subRL /rank_others.
    rewrite addnBA; last first.
      set k := i - _ + j.
      have Hk : k < n.
        subst k.
        case: j => j Hj /=.
        rewrite size_tuple in Hj.
        rewrite ltn_subRL addnC in Hc.
        by rewrite (leq_trans _ Hc) // ltnS leq_add // ltnW.
      by rewrite (_ : k = Ordinal Hk) // Hci.
    rewrite addnA addnBA; last exact: Hci.
    rewrite addKn.
    set k := i - _ + j.
    have Hk : k < n.
      subst k.
      case: j => j Hj /=.
      rewrite addnC -ltn_subRL (leq_trans Hc) // leq_sub // ltnW //.
      by rewrite size_tuple in Hj.
    rewrite (_ : k = Ordinal Hk) //.
    rewrite ltn_subLR; last first.
      by rewrite (leq_trans (Hci (Ordinal Hk))) // leq_add // leq_subr.
    rewrite addnC ltn_add2r => /leq_trans; apply.
    rewrite (leq_trans (Hci _)) //= /k.
    rewrite addnBAC; last by apply Hci.
    rewrite leq_subLR leq_add //.
Abort.
End merge_lens.

Definition curry T n m (l :lens n m) (st : nvect n T)
  : nvect m (nvect (n-m) T) :=
  [ffun v : m.-tuple I =>
   [ffun w : (n-m).-tuple I => st (merge_indices l v w)]].

Definition lmodType_C := Type.
Definition transformation m : forall T : lmodType_C, nvect m T -> nvect m T.
(*Definition transformation m : forall T : normedLmodType C,
 {unitary nvect m T -> nvect m T}.*)

