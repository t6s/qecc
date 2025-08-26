From mathcomp Require Import all_ssreflect all_algebra.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Utility lemmas *)

Lemma addnLR m n p : m + n = p -> n = p - m.
Proof. move/(f_equal (subn^~ m)); by rewrite addKn. Qed.

Lemma ltn_ordK q (i : 'I_q) : Ordinal (ltn_ord i) = i.
Proof. by apply val_inj. Qed.

Lemma disjointP (T : finType) (a1 a2 : pred T) :
  reflect (forall i, i \in a1 -> ~ i \in a2) [disjoint a1 & a2].
Proof.
case/boolP: [disjoint a1 & a2] => /pred0P Hdisj; constructor.
  move=> i H1 H2. move: (Hdisj i). by rewrite /= H1 H2.
move=> H; elim: Hdisj => i /=.
case H1: (i \in a1) => //.
by apply/negbTE/negP/H.
Qed.

Lemma enum_filterP (T : finType) (P : pred T) :
  [seq x <- enum T | P x] = enum P.
Proof. by rewrite {2}/enum_mem -enumT. Qed.

Section tnth.
Variables (T : Type) (m n : nat) (vl : m.-tuple T) (vr : n.-tuple T).

Lemma cast_tuple_proof (H : m = n) (v : m.-tuple T) : size v == n.
Proof. by rewrite size_tuple H. Qed.

Definition cast_tuple H v : n.-tuple T := Tuple (cast_tuple_proof H v).

Lemma eq_ord_tuple (t1 t2 : n.-tuple 'I_m) :
  (t1 == t2) = (map val t1 == map val t2).
Proof. exact/esym/inj_eq/(inj_map val_inj). Qed.

Lemma nth_tnth i x0 (H : i < n) : nth x0 vr i = tnth vr (Ordinal H).
Proof. by rewrite (tnth_nth x0). Qed.

Lemma tnth_lshift i : tnth [tuple of vl ++ vr] (lshift n i) = tnth vl i.
Proof.
by rewrite (tnth_nth (tnth vl i)) /= nth_cat size_tuple ltn_ord -tnth_nth.
Qed.

Lemma tnth_rshift i : tnth [tuple of vl ++ vr] (rshift m i) = tnth vr i.
Proof.
rewrite (tnth_nth (tnth vr i)) /= nth_cat size_tuple ltnNge leq_addr /=.
by rewrite addKn -tnth_nth.
Qed.

Lemma eq_from_nth' (s1 s2 : seq T) :
  size s1 = size s2 -> (forall a i, i < size s1 -> nth a s1 i = nth a s2 i) ->
  s1 = s2.
Proof.
case: s1 => [|a s1 Hsz Heq].
   by move/esym/eqP/nilP ->.
exact (eq_from_nth Hsz (Heq a)).
Qed.
End tnth.

Lemma cast_tupleE n T (v : n.-tuple T) (H : n = n) : cast_tuple H v = v.
Proof. exact/val_inj. Qed.

Lemma cast_tuple_bij T m n H : bijective (@cast_tuple T m n H).
Proof. by exists (cast_tuple (esym H)); move => x; apply val_inj. Qed.

Section tnth_eq.
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
End tnth_eq.

Section sorted.
Definition ord_ltn {r} : rel 'I_r := relpre val ltn.

Lemma sorted_ord_enum r : sorted ord_ltn (enum 'I_r).
Proof.
rewrite /is_true -[RHS](iota_ltn_sorted 0 r) -val_enum_ord.
by elim: (enum 'I_r) => //= a [|b l] //= <-.
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

Lemma take_ord_enum n j :
  take j (enum 'I_n) = [seq i : 'I_n <- enum 'I_n | i < j].
Proof.
apply: (@irr_sorted_eq _ ord_ltn).
- exact/ltn_trans.
- by move=> x; rewrite /ord_ltn /= ltnn.
- exact/take_sorted/sorted_ord_enum.
- exact/sorted_filter/sorted_ord_enum/ltn_trans.
move=> x.
by rewrite mem_filter in_take ?mem_enum // index_enum_ord andbT.
Qed.
End sorted.
