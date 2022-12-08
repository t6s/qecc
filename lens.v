From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ 'lens' x1 ; .. ; xn ]"
  (format "[ 'lens'  x1 ;  .. ;  xn ]").
Reserved Notation "[ 'lens' ]" (format "[ 'lens' ]").

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

Lemma cast_tuple_proof : m = n -> size vl == n.
Proof. by rewrite size_tuple => ->. Qed.

Definition cast_tuple (H : m = n) : n.-tuple T := Tuple (cast_tuple_proof H).

Lemma eq_ord_tuple (t1 t2 : n.-tuple 'I_m) :
  (t1 == t2) = (map val t1 == map val t2).
Proof.
case: eqP => [-> | H]; apply/esym/eqP => // /inj_map H'.
by elim H; apply/val_inj/H'/val_inj.
Qed.

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

Lemma cast_tupleE n T (v : n.-tuple T) (H : n = n) : cast_tuple v H = v.
Proof. exact/val_inj. Qed.

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

Lemma sorted_enum r : sorted ord_ltn (enum 'I_r).
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
End sorted.

Section lens.
Variables (T : Type) (n m : nat).

Record lens := mkLens {lens_t :> m.-tuple 'I_n ; lens_uniq : uniq lens_t}.
Canonical lens_subType := Eval hnf in [subType for lens_t].
Canonical lens_predType := PredType (pred_of_seq : lens -> pred 'I_n).

Definition endo1 := m.-tuple T -> m.-tuple T.

Variables (l : lens) (f : endo1).

Definition extract (t : n.-tuple T) := [tuple of map (tnth t) l].

Definition lens_sorted (l' : lens) := sorted ord_ltn l'.

Lemma mem_lensE : l =i val (lens_t l).
Proof. done. Qed.

Lemma size_lens : size l = m.
Proof. by rewrite size_tuple. Qed.

Lemma lens_leq : m <= n.
Proof.
rewrite -(size_enum_ord n) -size_lens uniq_leq_size // ?lens_uniq //.
move=> i _; by rewrite mem_enum.
Qed.

Lemma tnth_lensK i : index (tnth l i) l = i.
Proof.
by rewrite (tnth_nth (tnth l i)) index_uniq // (lens_uniq,size_lens).
Qed.

Lemma tnth_extract (v : n.-tuple T) i :
  tnth (extract v) i = tnth v (tnth l i).
Proof. by rewrite tnth_map. Qed.

Lemma eq_lens_tnth (l' : lens) : (tnth l =1 tnth l') -> l = l'.
Proof. by move/eq_from_tnth/val_inj. Qed.

Lemma lens_inj : injective (fun x : lens => x : seq _).
Proof. move=> x y H; exact/val_inj/val_inj. Qed.

Lemma tnth_lens_inj : injective (tnth l).
Proof. exact/tnth_inj/lens_uniq. Qed.

Lemma lens_sortedP :
  reflect (exists p, l = [seq i <- enum 'I_n | p i] :> seq _) (lens_sorted l).
Proof.
case/boolP: (lens_sorted l) => Hl; constructor.
  exists (mem l). apply/(irr_sorted_eq (leT:=ord_ltn)) => //.
  - exact/ltn_trans.
  - by move=> x; rewrite /ord_ltn /= ltnn.
  - rewrite sorted_filter //. exact/ltn_trans. exact/sorted_enum.
    by move=> i; rewrite mem_filter mem_enum andbT.
case => p Hp.
move/negP: Hl; elim.
rewrite /lens_sorted Hp sorted_filter //. exact/ltn_trans. exact/sorted_enum.
Qed.

Section lens_index.
Variables (i : 'I_n) (H : i \in l).

Definition lens_index : 'I_m := Ordinal (proj2 (index_tuple l i) H).

Definition make_lens_index : index i l = lens_index. Proof. by []. Qed.

Lemma tnth_lens_index : tnth l lens_index = i.
Proof. by rewrite (tnth_nth i) nth_index. Qed.
End lens_index.

Lemma lens_indexK i (H : tnth l i \in l) : lens_index H = i.
Proof. by apply/val_inj => /=; rewrite tnth_lensK. Qed.

(* Focusing on subvector *)
Definition inject (t : n.-tuple T) (t' : m.-tuple T) :=
  [tuple nth (tnth t i) t' (index i l) | i < n].
Definition focus1 t := inject t (f (extract t)).

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
Proof. move=> H; by rewrite nth_lens_index tnth_map tnth_lens_index. Qed.

Lemma tnth_inject t t' i (H : i \in l) :
  tnth (inject t t') i = tnth t' (lens_index H).
Proof. by rewrite tnth_mktuple nth_lens_index. Qed.

Lemma tnth_inject_others t t' i :
  i \notin l -> tnth (inject t t') i = tnth t i.
Proof. by move=> H; rewrite tnth_mktuple nth_lens_out. Qed.

Lemma inject_extract t : inject t (extract t) = t.
Proof.
apply/eq_from_tnth => i.
case/boolP: (i \in l) => H; last by rewrite tnth_inject_others.
by rewrite tnth_inject tnth_extract tnth_lens_index.
Qed.
End lens.

(* Cast *)
Section cast_lens.
Variables (n n' m m' : nat) (l : lens n m) (l' : lens n m').

Definition cast_lens_ord (H : n = n') : lens n' m.
exists (map_tuple (cast_ord H) l).  
abstract (by rewrite map_inj_uniq ?lens_uniq // => i j /cast_ord_inj).
Defined.

Definition cast_lens (H : m' = m) : lens n m.
exists (cast_tuple l' H).
apply lens_uniq.
Defined.

Lemma eq_lens_sorted :
  l =i l' -> lens_sorted l -> lens_sorted l' -> l = l' :> seq _.
Proof.
move/irr_sorted_eq; apply.
- exact: ltn_trans.
- by move=> x; rewrite /ord_ltn /= ltnn.
Qed.

Hypothesis H : l = l' :> seq _.

Lemma lens_size_eq : m' = m.
Proof. by rewrite -(size_tuple l') -H size_tuple. Qed.

Lemma lens_eq_cast : l = cast_lens lens_size_eq.
Proof. exact/lens_inj. Qed.

Lemma extract_eq_cast A (v : n.-tuple A) :
 extract l v = cast_tuple (extract l' v) lens_size_eq.
Proof. apply val_inj => /=. by rewrite H. Qed.
End cast_lens.

Lemma cast_lens_ordE n m (l : lens n m) H : cast_lens_ord (n':=n) l H = l.
Proof. apply/eq_lens_tnth => i; rewrite tnth_map; by apply/val_inj. Qed.

Lemma cast_lensE n m (l : lens n m) H : cast_lens (m':=m) l H = l.
Proof. exact/lens_inj. Qed.

(* Identity *)
Section lens_id.
Variable n : nat.
Lemma uniq_ord_tuple : uniq (ord_tuple n). Proof. exact/enum_uniq. Qed.
Definition lens_id := mkLens uniq_ord_tuple.

Lemma lens_sorted_id : lens_sorted lens_id.
Proof. exact: sorted_enum. Qed.

Lemma tnth_lens_id i : tnth lens_id i = i.
Proof. by rewrite tnth_ord_tuple. Qed.

Lemma extract_lens_id I (v : n.-tuple I) : extract lens_id v = v.
Proof. apply eq_from_tnth => i. by rewrite tnth_extract tnth_lens_id. Qed.

Lemma index_lens_id i : index i lens_id = i.
Proof. by rewrite {1}(_ : i = tnth lens_id i) (tnth_ord_tuple,tnth_lensK). Qed.
End lens_id.

(* Composition of lenses *)
Section lens_comp.
Variables (n m p : nat) (l1 : lens n m) (l2 : lens m p).

Definition lens_comp : lens n p.
exists (extract l2 l1).
abstract (by rewrite map_inj_uniq ?lens_uniq // => i j /tnth_lens_inj ->).
Defined.

Lemma tnth_comp i : tnth lens_comp i = tnth l1 (tnth l2 i).
Proof. by rewrite tnth_map. Qed.

Lemma lens_sorted_comp :
  lens_sorted l1 -> lens_sorted l2 -> lens_sorted lens_comp.
Proof. move=> Hl1 Hl2; apply sorted_comp => //; exact: ltn_trans. Qed.

Variable (T : Type).

Lemma extract_comp (t : n.-tuple T) :
  extract lens_comp t = extract l2 (extract l1 t).
Proof. apply eq_from_tnth => i; by rewrite !tnth_extract. Qed.

(* Composition for subvectors *)

Lemma index_lens_comp i (H : i \in l1) :
  index i lens_comp = index (lens_index H) l2.
Proof.
have {1}-> : i = tnth l1 (lens_index H) by rewrite (tnth_nth i) nth_index.
rewrite index_map //; exact/tnth_lens_inj.
Qed.

Lemma mem_lens_comp i (H : i \in l1) :
  (i \in lens_comp) = (lens_index H \in l2).
Proof. by rewrite -!index_mem !size_tuple index_lens_comp. Qed.

Lemma lens_comp_sub :
  {subset lens_comp <= l1}.
Proof.
by move=> i; rewrite mem_lensE => /mapP [j] _ ->; rewrite mem_tnth.
Qed.

Lemma mem_lens_comp_out i : i \notin l1 -> i \notin lens_comp.
Proof. by apply contra => /lens_comp_sub. Qed.

Lemma inject_comp (t : n.-tuple T) t' :
  inject l1 t (inject l2 (extract l1 t) t') = inject lens_comp t t'.
Proof.
apply eq_from_tnth => i.
case/boolP: (i \in l1) => Hl1.
  rewrite tnth_inject [RHS]tnth_mktuple index_lens_comp.
  case/boolP: (lens_index Hl1 \in l2) => Hl2.
    by rewrite tnth_inject make_lens_index -tnth_nth.
  by rewrite tnth_inject_others // tnth_extract tnth_lens_index nth_lens_out.
by rewrite !tnth_inject_others // mem_lens_comp_out.
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
apply eq_from_tnth => i; rewrite !tnth_extract tnth_mktuple.
by rewrite nth_lens_out // (disjointFr Hdisj) // mem_tnth.
Qed.

Lemma inject_disjointC vj vk :
  inject l' (inject l t vk) vj = inject l (inject l' t vj) vk.
Proof.
apply eq_from_tnth => i.
case/boolP: (i \in l) => Hil.
  have Hil' : i \notin l' by rewrite (disjointFr Hdisj) // mem_tnth.
  by rewrite tnth_inject_others // !tnth_inject.
case/boolP: (i \in l') => Hil'.
  by rewrite tnth_inject tnth_inject_others // tnth_inject.
by rewrite !tnth_inject_others.
Qed.

Lemma focus1_commu_in (f : endo1 T q) (g : endo1 T r) i : i \in l ->
  tnth (focus1 l f (focus1 l' g t)) i = tnth (focus1 l' g (focus1 l f t)) i.
Proof.
move=> Hl; have Hl' : i \notin l' by rewrite (disjointFr Hdisj).
by rewrite (focus1_out _ _ Hl') /focus1 extract_inject // !tnth_inject.
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

Section lens_comp_id.
Variables (n m : nat) (l : lens n m).

Lemma lens_comp1l : lens_comp (lens_id n) l = l.
Proof. by apply/eq_lens_tnth => i; rewrite tnth_comp tnth_lens_id. Qed.

Lemma lens_compl1 : lens_comp l (lens_id m) = l.
Proof. by apply/eq_lens_tnth => i; rewrite tnth_comp tnth_lens_id. Qed.
End lens_comp_id.

Section lens_pred.
Variables (n : nat) (p : pred 'I_n).

Let pred_tuple := Tuple (enum_tupleP p).
Lemma uniq_pred_tuple : uniq pred_tuple.
Proof. exact/enum_uniq. Qed.

Definition lens_pred := mkLens uniq_pred_tuple.

Lemma lens_sorted_pred : lens_sorted lens_pred.
Proof. by apply/lens_sortedP; exists (mem p); rewrite enum_filterP. Qed.
End lens_pred.

(* Decomposition into inclusion and permutation *)
Section lens_basis_perm.
Variables (n p : nat) (l : lens n p).

Definition seq_basis := [seq i <- enum 'I_n | i \in l].
Lemma size_basis : size seq_basis == p.
Proof.
apply/eqP.
rewrite /seq_basis.
rewrite (eq_filter (a2:=mem [set i | i in l])); last first.
  move=> i. rewrite !inE.
  case: imsetP.
    by case => x Hx ->.
  by move=> Hx; apply/negP => Hi; move: Hx; elim; exists i.
rewrite enum_filterP /= -cardE card_imset // -[RHS](size_tuple l).
exact/card_uniqP/lens_uniq.
Qed.
Lemma uniq_basis : uniq (Tuple size_basis).
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Definition lens_basis := mkLens uniq_basis.

Lemma lens_sorted_basis : lens_sorted lens_basis.
Proof. by apply/lens_sortedP; exists (mem l). Qed.

Lemma lens_basis_sortedE : lens_sorted l -> lens_basis = l.
Proof.
move=> H.
apply/lens_inj/eq_lens_sorted => //; last exact/lens_sorted_basis.
by move=> j; rewrite mem_filter mem_enum /= andbT.
Qed.

Lemma perm_in_basis i : tnth l i \in lens_basis.
Proof. by rewrite mem_filter mem_tnth mem_enum. Qed.

Definition tuple_perm := [tuple lens_index (perm_in_basis i) | i < p].
Lemma uniq_perm : uniq tuple_perm.
Proof.
rewrite map_inj_uniq ?uniq_ord_tuple //.
move=> i j /(f_equal (tnth lens_basis)).
by rewrite !tnth_lens_index => /tnth_lens_inj.
Qed.

Definition lens_perm := mkLens uniq_perm.

Lemma lens_basis_perm : lens_comp lens_basis lens_perm = l.
Proof.
apply/eq_lens_tnth => i.
by rewrite tnth_comp tnth_mktuple tnth_lens_index.
Qed.

Lemma lens_perm_sortedE : lens_sorted l -> lens_perm = lens_id p.
Proof.
move=> H; apply/eq_lens_tnth => i.
rewrite tnth_mktuple tnth_ord_tuple.
apply/(tnth_inj lens_basis); first exact/lens_uniq.
by rewrite tnth_lens_index lens_basis_sortedE.
Qed.
End lens_basis_perm.

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

Lemma tnth_lens_cat_l i : tnth lens_cat (lshift p i) = tnth l1 i.
Proof. exact/tnth_lshift. Qed.

Lemma tnth_lens_cat_r i : tnth lens_cat (rshift m i) = tnth l2 i.
Proof. exact/tnth_rshift. Qed.

Variable (T : eqType).

Lemma extract_cat (t : n.-tuple T) :
  extract lens_cat t = [tuple of extract l1 t ++ extract l2 t].
Proof. apply val_inj => /=. by rewrite map_cat. Qed.
End lens_cat.

Section merge_lens.
Variables (I : Type) (dI : I) (n m : nat) (l : lens n m).

Lemma cards_filter (A : finType) (p : pred A) :
  #|[set a : A | p a]| = size [seq a <- enum A | p a].
Proof.
rewrite cardsE /= cardE -filter_predI.
congr size; apply eq_filter => /= i. 
by rewrite !inE andbT.
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

Lemma mem_others i : (i \in others) = ~~ (i \in l).
Proof. by rewrite mem_filter mem_enum andbT. Qed.

Lemma uniq_others : uniq others.
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Definition lothers : lens n (n-m).
exists (Tuple size_others).
exact uniq_others.
Defined.

Lemma mem_lothers i : (i \in lothers) = (i \notin l).
Proof. by rewrite mem_others. Qed.

Lemma lens_sorted_lothers : lens_sorted lothers.
Proof. exact/sorted_filter/sorted_enum/ltn_trans. Qed.

Definition merge_indices (v : m.-tuple I) (w : (n-m).-tuple I) :=
  [tuple nth (nth dI w (index i lothers)) v (index i l) | i < n].

Lemma tnth_merge_indices i vi vj (Hil : i \in l) :
  tnth (merge_indices vi vj) i = tnth vi (lens_index Hil).
Proof.
by rewrite !tnth_map !tnth_ord_tuple (make_lens_index Hil) -tnth_nth.
Qed.

Lemma tnth_merge_indices_lothers i vi vj (Hil : i \in lothers) :
  tnth (merge_indices vi vj) i = tnth vj (lens_index Hil).
Proof.
have Hil' := Hil; rewrite mem_lothers in Hil'.
rewrite !tnth_map !tnth_ord_tuple nth_lens_out //.
by rewrite (make_lens_index Hil) -!tnth_nth.
Qed.

Lemma extract_merge v1 v2 : extract l (merge_indices v1 v2) = v1.
Proof.
apply eq_from_tnth => i; rewrite tnth_extract.
by rewrite (tnth_merge_indices _ _ (mem_tnth i l)) lens_indexK.
Qed.

Lemma extract_lothers_merge v1 v2 : extract lothers (merge_indices v1 v2) = v2.
Proof.
apply eq_from_tnth => i /=; rewrite tnth_extract.
by rewrite (tnth_merge_indices_lothers _ _ (mem_tnth i lothers)) lens_indexK.
Qed.

Lemma merge_indices_extract_others v1 v2 :
  merge_indices v2 (extract lothers v1) = inject l v1 v2.
Proof.
apply eq_from_tnth => i.
case/boolP: (i \in l) => Hil.
  by rewrite tnth_merge_indices tnth_inject.
rewrite tnth_inject_others //.
rewrite -mem_lothers in Hil.
by rewrite tnth_merge_indices_lothers tnth_extract tnth_lens_index.
Qed.

Lemma merge_indices_extract (v : n.-tuple I) :
  merge_indices (extract l v) (extract lothers v) = v.
Proof. by rewrite merge_indices_extract_others inject_extract. Qed.

Lemma merge_indices_inj vj : injective (fun vi => merge_indices vi vj).
Proof.
move=> vi vi' Hm.
by rewrite -(extract_merge vi vj) -(extract_merge vi' vj) Hm.
Qed.

Lemma extract_merge_disjoint p (l' : lens n p) vi vj :
  [disjoint l & l'] ->
  extract l' (merge_indices vj (extract lothers vi)) = extract l' vi.
Proof.
move=> Hdisj; apply eq_from_tnth => i; rewrite !tnth_extract.
have Hil : tnth l' i \notin l by rewrite (disjointFl Hdisj) // mem_tnth.
have Hilo : tnth l' i \in lothers by rewrite mem_lothers.
by rewrite tnth_merge_indices_lothers tnth_extract tnth_lens_index.
Qed.
End merge_lens.

Lemma eq_lothers n m m' (l : lens n m) (l' : lens n m') :
  l =i l' -> lothers l = lothers l' :> seq _.
Proof. by move=> ll'; apply/eq_filter => i; rewrite ll'. Qed.

Section lens_comp_lothers.
Variables (n m p : nat) (l : lens n m) (l' : lens (n - m) p).

Lemma disjoint_comp_lothers : [disjoint l & lens_comp (lothers l) l'].
Proof.
rewrite disjoint_sym disjoint_has.
rewrite -all_predC.
apply/allP => i Hi /=.
apply/negP => Hi'.
move: Hi => /= /mapP [j Hj] ij.
have : i \notin l.
  by rewrite -mem_lothers ij mem_tnth.
by rewrite Hi'.
Qed.

Lemma lens_comp_lothers :
  lens_comp (lothers l) (lothers l') =
  lothers (lens_cat disjoint_comp_lothers) :> seq _.
Proof.
rewrite /= /others.
rewrite (eq_filter (a2:=preim (tnth (Tuple (size_others l)))
                    (mem (lothers (lens_comp (lothers l) l'))))); last first.
  move=> i /=.
  rewrite mem_lothers mem_lens_comp ?mem_tnth // => H.
  by rewrite lens_indexK.
rewrite -filter_map (_ : map _ _ = lothers l); last first.
  rewrite -(val_ord_tuple (n-m)); set mp := map _ _.
  by rewrite (_ : mp = [tuple of mp]) // -tuple_map_ord.
rewrite -filter_predI.
apply eq_filter => i /=.
by rewrite [in RHS]mem_lensE /= mem_cat negb_or andbC mem_lothers.
Qed.
End lens_comp_lothers.

(* Empty lens *)
Section lens_empty.
Variable n : nat.
Definition lens_empty : lens n 0 := {|lens_t := [tuple]; lens_uniq := erefl|}.

Lemma lens_sorted_empty : lens_sorted lens_empty.
Proof. done. Qed.

Lemma eq_lens_empty (l : lens n 0) : l = lens_empty.
Proof. case: l => -[] [] // Hl Hu; exact/lens_inj. Qed.

Lemma extract_lens_empty T (l : lens n 0) v : extract (T:=T) l v = [tuple].
Proof. apply eq_from_tnth => x. have := ltn_ord x. by rewrite ltn0. Qed.

Lemma lothers_id : lothers (lens_id n) = lens_empty :> seq _.
Proof. apply/nilP. by rewrite /nilp size_tuple subnn. Qed.

Lemma lothers_empty : lothers lens_empty = lens_id n :> seq _.
Proof. by rewrite /lothers /others /= filter_predT. Qed.

Lemma merge_indices_empty (T : eqType) (dI:T) v w :
  merge_indices dI lens_empty v w = cast_tuple w (subn0 n).
Proof.
rewrite /merge_indices.
rewrite (eq_mktuple (tnth (cast_tuple w (subn0 n)))); last first.
  move => i.
  by rewrite nth_lens_out // lothers_empty index_lens_id (tnth_nth dI).
by apply eq_from_tnth => i; rewrite tnth_mktuple.
Qed.

Lemma lens_cat_emptyl m (l : lens n m) (H : [disjoint lens_empty & l]) :
  lens_cat H = l.
Proof. exact/lens_inj. Qed.
End lens_empty.

Section lens_full.
Lemma mem_lens_full n i (l : lens n n) : i \in l.
Proof.
move/card_uniqP: (lens_uniq l) (cardC (mem l)) ->.
rewrite card_ord size_tuple => /(f_equal (subn^~ n)).
rewrite addKn subnn => /card0_eq/(_ i).
by rewrite !inE => /negbFE.
Qed.

Lemma lothers_full n (l : lens n n) : lothers l = lens_empty n :> seq _.
Proof.
rewrite /= /others (eq_filter (a2:=pred0)) ?filter_pred0 //= => i.
by rewrite mem_lens_full.
Qed.

Lemma lothers_comp_full n m (l : lens n m) (l1 : lens m m) :
  lothers (lens_comp l l1) = lothers l.
Proof.
apply/lens_inj/eq_lothers => i.
case/boolP: (i \in l) => Hi. by rewrite mem_lens_comp mem_lens_full.
apply/negbTE; apply: contra Hi. exact/lens_comp_sub.
Qed.
End lens_full.

Section merge_indices_basis.
Variables (I : Type) (dI : I) (n m : nat) (l : lens n m).
Lemma merge_indices_basis vi vj :
  merge_indices dI (lens_basis l) vi vj =
  merge_indices dI l (extract (lens_perm l) vi) vj.
Proof.
apply eq_from_tnth => i.
case/boolP: (i \in lens_basis l) => Hib.
  rewrite tnth_merge_indices.
  have Hil : i \in l.
    by rewrite -(lens_basis_perm l) mem_lens_comp mem_lens_full.
  rewrite tnth_merge_indices tnth_extract.
  congr tnth.
  apply/(tnth_inj (lens_basis l)); first by apply lens_uniq.
  by rewrite -tnth_comp lens_basis_perm !tnth_lens_index.
rewrite -mem_lothers in Hib.
have Hil : i \in lothers l.
  by rewrite -(lens_basis_perm l) lothers_comp_full.
rewrite !tnth_merge_indices_lothers.
congr tnth; apply/val_inj => /=.
congr index.
move/(f_equal (val \o val)): (lothers_comp_full (lens_basis l) (lens_perm l)).
by rewrite lens_basis_perm.
Qed.
End merge_indices_basis.

Section lens_single.
Variables n : nat.

Definition lens_single i : lens n 1 :=
  {|lens_t := [tuple i]; lens_uniq := erefl|}.

Lemma lens_sorted_single i : lens_sorted (lens_single i).
Proof. done. Qed.

Lemma index_lens_single i : index i (lens_single i) = (@ord0 1).
Proof. by rewrite /= eqxx. Qed.

Lemma lens_index_single i j (H : j \in lens_single i) : lens_index H = ord0.
Proof. by apply/val_inj => /=; move: H; rewrite inE eq_sym => ->. Qed.

Lemma tnth_lens_single i j : tnth (lens_single i) j = i.
Proof. by rewrite /= ord1. Qed.

Lemma tnth_merge_indices_single T (dI : T) i vi vj :
  tnth (merge_indices dI (lens_single i) vi vj) i = tnth vi ord0.
Proof.
rewrite tnth_merge_indices. by rewrite inE eqxx.
by move=> H; rewrite ord1.
Qed.
End lens_single.

Lemma tnth_lothers_single n (i : 'I_n.+2) (k : 'I_n.+1) :
    tnth (lothers (lens_single i)) k = lift i k.
Proof.
apply/val_inj; rewrite (tnth_nth i); case: k => /=.
elim: (n.+1) i => {n} [|n IH] i k.
  by rewrite ltn0.
move/eqP: (size_others (lens_single i)); rewrite /others enum_ordSl.
case: k => [|k] /=; rewrite mem_lensE inE.
case: (unliftP ord0 i) => [i'|] -> Hsz.
    by rewrite eq_liftF.
  by rewrite eqxx /= enum_ordSl.
case: (unliftP ord0 i) => [i'|] ->.
  rewrite ltnS => Hsz Hk.
  rewrite eq_liftF /= filter_map size_map in Hsz *.
  rewrite (nth_map i' _ (lift ord0)); last first.
    by rewrite -ltnS Hsz subn1 ltnS.
  rewrite bumpS /= /(bump 0) add1n.
  f_equal.
  rewrite (eq_filter (a2:=fun k => k \notin lens_single i')) //.
  exact: IH.
rewrite eqxx /= filter_map size_map => Hsz Hk.
rewrite (nth_map ord0 _ (lift ord0)); last by rewrite Hsz.
congr bump.
rewrite (eq_filter (a2:=predT)) //.
rewrite ltnS in Hk.
rewrite filter_predT (_ : k.+1 = lift ord0 (Ordinal Hk)) //.
by rewrite nth_ord_enum.
Qed.

Section lens_pair.
Variables (n : nat) (i j : 'I_n).
Lemma uniq_pair : i != j -> uniq [:: i; j].
Proof. by rewrite /= inE andbT. Qed.

Hypothesis ij : i != j.
Definition lens_pair : lens n 2 := mkLens (uniq_pair ij).

Lemma lens_pair0 : lens_comp lens_pair (lens_single ord0) = lens_single i.
Proof. by apply/eq_lens_tnth => k; rewrite tnth_comp !tnth_lens_single. Qed.

Lemma lens_pair1 :
  lens_comp lens_pair (lens_single (lift ord0 ord0)) = lens_single j.
Proof. by apply/eq_lens_tnth => k; rewrite tnth_comp !tnth_lens_single. Qed.
End lens_pair.

(* Ordered lenses *)
Section lens_left_right.
Variables m n : nat.

Definition lens_left : lens (m+n) m.
exists [tuple lshift n i | i < m].
abstract (rewrite map_inj_uniq ? enum_uniq //; exact/lshift_inj).
Defined.

Definition lens_right : lens (m+n) n.
exists [tuple rshift m i | i < n].
abstract (rewrite map_inj_uniq ? enum_uniq //; exact/rshift_inj).
Defined.

Variables (T : Type) (tl : m.-tuple T) (tr : n.-tuple T).
Lemma extract_lens_left : extract lens_left [tuple of tl ++ tr] = tl.
Proof.
apply eq_from_tnth => i; rewrite [LHS](tnth_nth (tnth tl i)) /= -map_comp.
by rewrite (nth_map i) /= ?size_enum_ord // nth_ord_enum tnth_lshift.
Qed.
Lemma extract_lens_right : extract lens_right [tuple of tl ++ tr] = tr.
Proof.
apply eq_from_tnth => i; rewrite [LHS](tnth_nth (tnth tr i)) /= -map_comp.
by rewrite (nth_map i) /= ?size_enum_ord // nth_ord_enum tnth_rshift.
Qed.

Lemma lens_left_right_disjoint : [disjoint lens_left & lens_right].
Proof.
apply/pred0P => /= i.
rewrite simpl_predE /=.
case: (split_ordP i) => j ->.
  suff /negbTE -> : lshift n j \notin lens_right.
    by rewrite andbF.
  apply/mapP => -[k] _ /esym/eqP.
  by rewrite eq_rlshift.
have /negbTE -> // : rshift m j \notin lens_left.
apply/mapP => -[k] _ /eqP.
by rewrite eq_rlshift.
Qed.

Lemma take_enum_lshift : take m (enum 'I_(m + n)) = [tuple lshift n i | i < m].
Proof.
apply/esym/eq_from_nth'.
  by rewrite size_map size_takel -cardT card_ord // leq_addr.
move=> a i.
rewrite size_map -cardT card_ord => Hi.
rewrite nth_tnth tnth_map tnth_ord_tuple nth_take //.
apply val_inj. by rewrite [RHS]nth_enum_ord // (leq_trans Hi) // leq_addr.
Qed.

Lemma drop_enum_rshift : drop m (enum 'I_(m + n)) = [tuple rshift m i | i < n].
Proof.
apply/esym/eq_from_nth'.
  by rewrite size_map size_drop -!cardT !card_ord addKn.
move=> a i.
rewrite size_map -cardT card_ord => Hi.
rewrite nth_tnth tnth_map tnth_ord_tuple nth_drop //.
apply val_inj. by rewrite [RHS]nth_enum_ord //= -addnS leq_add2l.
Qed.

Lemma lens_left_right : lens_cat lens_left_right_disjoint = lens_id (m+n).
Proof.
apply/lens_inj => /=.
by rewrite -[RHS](cat_take_drop m) take_enum_lshift drop_enum_rshift.
Qed.

Lemma lothers_left : lothers lens_left = lens_right :> seq _.
Proof.
rewrite /lothers /others /=.
have /= := f_equal val lens_left_right.
rewrite -(val_ord_tuple (m+n)) => <-.
rewrite filter_cat filter_map -(eq_filter (a1:=pred0)); last first.
  move=> i /=; rewrite mem_lensE mem_map ?mem_enum //; exact/lshift_inj.
rewrite filter_pred0 filter_map -(eq_filter (a1:=predT)) ?filter_predT //.
move=> i /=. rewrite mem_lensE /=.
by apply/esym/mapP => -[x _] /eqP; rewrite eq_shift.
Qed.

Lemma lothers_right : lothers lens_right = lens_left :> seq _.
Proof.
rewrite /lothers /others /=.
have /= := f_equal val lens_left_right.
rewrite -(val_ord_tuple (m+n)) => <-.
rewrite filter_cat filter_map -(eq_filter (a1:=predT)); last first.
  move=> i /=. rewrite mem_lensE /=.
  by apply/esym/mapP => -[x _] /eqP; rewrite eq_shift.
rewrite filter_predT filter_map -(eq_filter (a1:=pred0)).
  by rewrite filter_pred0 cats0.
move=> i /=; rewrite mem_lensE mem_map ?mem_enum //; exact/rshift_inj.
Qed.

Variables (p : nat) (l : lens p m) (l' : lens p n) (H : [disjoint l & l']).

Lemma lens_comp_left : l = lens_comp (lens_cat H) lens_left.
Proof.
by apply/eq_lens_tnth => i; rewrite tnth_comp tnth_mktuple tnth_lshift.
Qed.

Lemma lens_comp_right : l' = lens_comp (lens_cat H) lens_right.
Proof.
by apply/eq_lens_tnth => i; rewrite tnth_comp tnth_mktuple tnth_rshift.
Qed.

Definition lens_perm_left := lens_comp (lens_perm (lens_cat H)) lens_left.
Definition lens_perm_right := lens_comp (lens_perm (lens_cat H)) lens_right.

Lemma lens_perm_disjoint : [disjoint lens_perm_left & lens_perm_right].
Proof.
apply/disjointP => i /mapP [x] Hx -> /mapP [y] Hy.
move/(f_equal (tnth (lens_basis (lens_cat H)))).
rewrite -!tnth_comp lens_basis_perm => /tnth_lens_inj xy.
rewrite -xy in Hy.
by move/disjointP/(_ x): lens_left_right_disjoint; elim.
Qed.

Lemma lens_perm_leftE :
  lens_comp (lens_basis (lens_cat H)) lens_perm_left =
  lens_comp (lens_cat H) lens_left.
Proof.
by apply/eq_lens_tnth => i; rewrite !tnth_comp -tnth_comp lens_basis_perm.
Qed.

Lemma lens_perm_rightE :
  lens_comp (lens_basis (lens_cat H)) lens_perm_right =
  lens_comp (lens_cat H) lens_right.
Proof.
by apply/eq_lens_tnth => i; rewrite !tnth_comp -tnth_comp lens_basis_perm.
Qed.
End lens_left_right.

(* reindexing *)
Section reindex.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType) (dI : I).

Lemma reindex_merge_indices n m (l : lens n m) F :
  \big[op/idx]_i F i = \big[op/idx]_i \big[op/idx]_j F (merge_indices dI l i j).
Proof.
rewrite [RHS](pair_bigA _ (fun i j => F (merge_indices dI l i j))).
rewrite (reindex (fun v : m.-tuple I * (n-m).-tuple I =>
                    merge_indices dI l (fst v) (snd v))) //=.
exists (fun v => (extract l v, extract (lothers l) v)) => // v _.
  by rewrite extract_merge extract_lothers_merge; case: v.
by rewrite /= merge_indices_extract.
Qed.

Lemma reindex_left_right m n (F : m.-tuple I -> n.-tuple I -> R) :
  \big[op/idx]_i \big[op/idx]_j F i j =
  \big[op/idx]_v F (extract (lens_left m n) v) (extract (lens_right m n) v).
Proof.
rewrite pair_bigA /=.
rewrite [LHS](reindex (fun v : (m+n).-tuple I =>
         (extract (lens_left m n) v, extract (lens_right m n) v))) //.
exists (fun v : m.-tuple I * n.-tuple I => [tuple of v.1 ++ v.2]) => /= vj _.
  rewrite -[RHS]extract_lens_id -(lens_left_right m n).
  by apply/val_inj; rewrite /= map_cat.
case: vj => vl vr /=; congr pair; apply eq_from_tnth => i;
by rewrite tnth_map tnth_mktuple (tnth_lshift,tnth_rshift).
Qed.
End reindex.

Section inject_all.
Variables (I : Type) (m n : nat) (lm : lens (m+n) m) (ln : lens (m+n) n).
Hypothesis Hdisj : [disjoint lm & ln].

Lemma lens_all i : (i \in lm) || (i \in ln).
Proof.
have : [set a in lm] == [set a | a \notin ln].
  rewrite eqEcard.
  rewrite cards_filter (eqP (size_others ln)) addnK.
  have -> : #|[set a in lm]| = #|lm| by apply eq_card => j; rewrite inE.
  have/card_uniqP -> := lens_uniq lm.
  rewrite size_tuple leqnn andbT.
  apply/subsetP => j. by rewrite !inE => /(disjointFr Hdisj) ->.
move/eqP/setP/(_ i). rewrite !inE.
by case: (i \in ln) => ->.
Qed.

Lemma inject_all (vi vj : (m+n).-tuple I) :
  (inject ln (inject lm vi (extract lm vj)) (extract ln vj)) = vj.
Proof.
apply eq_from_tnth => i.
rewrite tnth_mktuple.
case/boolP: (i \in ln) => Hi.
  by rewrite (nth_lens_index Hi) tnth_map tnth_lens_index.
rewrite nth_lens_out // tnth_mktuple.
have := lens_all i.
rewrite (negbTE Hi) orbF => Him.
by rewrite (nth_lens_index Him) tnth_map tnth_lens_index.
Qed.
End inject_all.

(* Shifting of disjoint lenses *)
Section make_comp.
Variables (n m p : nat) (l : lens n m) (l' : lens n p).
Hypothesis Hdisj : [disjoint l & l'].

Lemma make_comp_present i :
  tnth l' i \in lothers l.
Proof.
move: (mem_tnth i l').
rewrite mem_lothers => Hl'; apply/negP => Hl.
move: Hdisj; rewrite disjoint_has => /hasP; elim.
by exists (tnth l' i).
Qed.

Definition make_comp :=
  [tuple lens_index (make_comp_present i) | i < p].

Lemma uniq_map_comp : uniq make_comp.
Proof.
rewrite /make_comp/= map_inj_in_uniq ?enum_uniq // => i j _ _.
move/(f_equal (tnth (lothers l))).
by rewrite !tnth_lens_index => /tnth_lens_inj.
Qed.

Definition lmake_comp := mkLens uniq_map_comp.

Lemma lmake_compE : lens_comp (lothers l) lmake_comp = l'.
Proof.
apply/eq_lens_tnth => i.
rewrite tnth_map tnth_mktuple (tnth_nth (tnth l' i)) /=.
by rewrite nth_index // make_comp_present.
Qed.
End make_comp.

(* associativity of focussing *)
Section lens_assoc.
Variables (I : Type) (dI : I) (n m p : nat) (l : lens n m) (l' : lens m p).

Local Notation merge_indices := (merge_indices dI).

Definition lothers_comp := lothers (lens_comp l l').

Lemma others_in_l_present i :
  tnth (lens_comp l (lothers l')) i \in lothers_comp.
Proof.
rewrite mem_lothers; apply/mapP => -[k Hk].
rewrite tnth_comp => /tnth_lens_inj Hi.
by apply/negP: Hk; rewrite -mem_lothers -Hi mem_tnth.
Qed.

Definition others_in_l :=
  [tuple lens_index (others_in_l_present i) | i < m - p].

Lemma uniq_others_in_l : uniq (others_in_l).
Proof.
apply/tnth_inj => i j; rewrite !tnth_mktuple.
set k := lens_index _.
case=> /(f_equal (nth (widen_ord (leq_subr _ _) k) lothers_comp)).
rewrite !nth_index; try by rewrite others_in_l_present.
move/tnth_inj => -> //.
rewrite map_inj_uniq ?(lens_uniq (lothers l')) //; exact/tnth_lens_inj.
Qed.

Definition lothers_in_l := mkLens uniq_others_in_l.

Lemma cast_lothers_notin_l : n - p - (m - p) = n - m.
Proof. rewrite subnBA ?subnK // lens_leq //. exact: (lens_comp l l'). Qed.

Lemma size_lothers_notin_l : size (lothers lothers_in_l) == n - m.
Proof. by rewrite size_tuple cast_lothers_notin_l. Qed.

Definition lothers_notin_l : lens (n-p) (n-m).
exists (Tuple size_lothers_notin_l).
exact (lens_uniq (lothers lothers_in_l)).
Defined.

Lemma lothers_in_l_comp :
  lens_comp lothers_comp lothers_in_l = lens_comp l (lothers l').
Proof.
apply/eq_lens_tnth => i.
by rewrite !tnth_map tnth_ord_tuple tnth_lens_index.
Qed.

Lemma lothers_notin_l_comp :
  lens_comp lothers_comp lothers_notin_l = lothers l.
Proof.
apply/lens_inj/eq_lens_sorted/lens_sorted_lothers/lens_sorted_comp;
  try exact/sorted_filter/sorted_enum/ltn_trans.
move=> /= i; rewrite mem_lothers.
case/boolP: (i \in l) => /= Hi; apply/mapP.
- case=> j; rewrite mem_lothers => Hj Hi'.
  apply/negP: Hj; rewrite negbK; apply/tnthP.
  case/tnthP: Hi => k Hk.
  have Hk' : k \in lothers l'.
    rewrite mem_lothers; apply/tnthP => -[h] Hh.
    have : i \in lothers_comp by rewrite Hi' mem_tnth.
    by rewrite Hk Hh -tnth_comp mem_lothers mem_tnth.
  exists (lens_index Hk').
  apply (tnth_lens_inj (l:=lothers_comp)).
  by rewrite -tnth_comp lothers_in_l_comp tnth_comp -Hi' Hk tnth_lens_index.
- have/tnthP [j Hj] :  i \in lothers_comp.
    rewrite mem_lothers; apply: contra Hi => /mapP [j Hj] ->.
    exact: mem_tnth.
  exists j => //.
  rewrite mem_lothers; apply: contra Hi => /mapP [k _].
  rewrite Hj => ->.
  have Hol := others_in_l_present k.
  by rewrite tnth_lens_index tnth_map mem_tnth.
Qed.

Lemma extract_lothers_comp (v : n.-tuple I) :
  extract lothers_comp v =
  merge_indices lothers_in_l
                (extract (lens_comp lothers_comp lothers_in_l) v)
                (extract (lens_comp lothers_comp (lothers lothers_in_l)) v).
Proof. by rewrite !extract_comp merge_indices_extract. Qed.

Lemma merge_indices_comp vj vk (vl : (n-p - (m-p)).-tuple I)
                               (vm : (n-m).-tuple I) :
  vl = vm :> seq I ->  (* can we use S-prop here? *)
  merge_indices (lens_comp l l') vj (merge_indices lothers_in_l vk vl) =
  merge_indices l (merge_indices l' vj vk) vm.
Proof.
move=> Hlm.
apply/eq_from_tnth => i.
case/boolP: (i \in l) => Hil.
  rewrite (tnth_merge_indices _ _ _ Hil).
  case/boolP: (lens_index Hil \in l') => Hill'.
    rewrite (tnth_merge_indices _ _ _ Hill').
    have Hilcl' : i \in lens_comp l l' by rewrite mem_lens_comp.
    rewrite (tnth_merge_indices _ _ _ Hilcl').
    congr tnth; apply/val_inj => /=; by rewrite -index_lens_comp.
  have Hilo : i \in lothers_comp by rewrite mem_lothers mem_lens_comp.
  rewrite -mem_lothers in Hill'.
  rewrite tnth_merge_indices_lothers [RHS]tnth_merge_indices_lothers.
  have Hic : i \in lens_comp l (lothers l') by rewrite mem_lens_comp.
  have Hilol : lens_index Hilo \in lothers_in_l.
    by rewrite -lothers_in_l_comp mem_lens_comp in Hic.
  rewrite tnth_merge_indices.
  congr tnth; apply (tnth_lens_inj (l:=lens_comp l (lothers l'))).
  by rewrite -{1}lothers_in_l_comp !tnth_comp !tnth_lens_index.
case/boolP: (i \in lens_comp l l') => [/lens_comp_sub|] Hic.
  by rewrite Hic in Hil.
rewrite -!mem_lothers in Hil Hic.
rewrite tnth_merge_indices_lothers [RHS]tnth_merge_indices_lothers.
have Hlil : lens_index Hic \in lothers lothers_in_l.
  rewrite -mem_lens_comp mem_lensE /=.
  by move/(f_equal (val \o val)): lothers_notin_l_comp => /= ->.
rewrite tnth_merge_indices_lothers.
set a := tnth vl _; rewrite /a (tnth_nth a) /= Hlm [RHS](tnth_nth a) /=.
congr nth. 
have /(f_equal (val \o val)) := lothers_notin_l_comp; rewrite [RHS]/= => <-.
by rewrite -[LHS](index_lens_comp (lothers lothers_in_l)).
Qed.

(* For focus_others, only uses variables *)
Lemma merge_indices_comp_others (l1 : lens (n-m) p) vi vj :
  merge_indices (lens_comp (lothers l) l1) vj
                (extract (lothers (lens_comp (lothers l) l1)) vi) =
  merge_indices l (extract l vi)
     (merge_indices l1 vj (extract (lens_comp (lothers l) (lothers l1)) vi)).
Proof.
set l2 := lens_comp (lothers l) l1.
apply eq_from_tnth => i.
case/boolP: (i \in l) => Hl.
  rewrite [RHS]tnth_merge_indices.
  have Hl2: i \notin l2.
    apply/negP => /lens_comp_sub; by rewrite mem_others Hl.
  rewrite -mem_lothers in Hl2.
  by rewrite tnth_merge_indices_lothers !tnth_extract !tnth_lens_index.
rewrite -mem_lothers in Hl.
rewrite [RHS]tnth_merge_indices_lothers.
case/boolP: (i \in l2) => Hl2.
  have := Hl2; rewrite mem_lens_comp => Hl1; rewrite !tnth_merge_indices.
  congr tnth; apply/val_inj; by rewrite /= -index_lens_comp.
have := Hl2; rewrite mem_lens_comp => Hl1.
rewrite -!mem_lothers in Hl1 Hl2.
by rewrite !tnth_merge_indices_lothers !tnth_extract !tnth_lens_index.
Qed.

Lemma merge_indices_pair (i i' : 'I_n.+2) (vi vj : 1.-tuple I)
      (vk : (n.+2 - 1 - 1).-tuple I)
      (Hior : i \in lothers (lens_single i'))
      (Hir : i != i') :
  merge_indices (lens_single i') vi
    (merge_indices (lens_single (lens_index Hior)) vj vk) =
  merge_indices (lens_pair Hir) [tuple of vj ++ vi] vk.
Proof.
apply/eq_from_tnth => j.
rewrite !tnth_map !tnth_ord_tuple.
rewrite [index j (lens_single _)]/= [index j (lens_pair _)]/=.
case: ifP => rij.
  rewrite [X in nth _ vi X](_ : 0 = @ord0 1)%N //.
  rewrite ifF; last by rewrite -(negbTE Hir) -(eqP rij).
  case: vj => -[] // a [] //= sza.
  by rewrite -!(tnth_nth _ vi ord0).
rewrite nth_default; last by rewrite size_tuple.
have Hjl : j \in lothers (lens_single i').
  by rewrite mem_lothers mem_lensE inE eq_sym rij.
case: ifPn => ij.
  rewrite -(eqP ij) in Hjl *.
  rewrite make_lens_index -tnth_nth.
  have -> : lens_index Hjl = lens_index Hior by apply/val_inj.
  rewrite tnth_merge_indices_single.
  by case: vj => -[].
rewrite make_lens_index -tnth_nth !tnth_map !tnth_ord_tuple.
rewrite nth_lens_out; last first.
  rewrite mem_lensE inE.
  apply: contra ij => /eqP /(f_equal (tnth (lothers (lens_single i')))).
  by rewrite !tnth_lens_index => ->.
rewrite [RHS]nth_default ?size_tuple //.
congr nth.
rewrite -(index_lens_comp (lothers (lens_single (lens_index Hior))) Hjl).
congr index.
rewrite lens_comp_lothers.
apply eq_lothers => /= k.
by rewrite !mem_lensE !inE tnth_lens_index orbC.
Qed.

Lemma merge_indices_perm (l1 : lens m m) (vi : m.-tuple I) vk :
  merge_indices (lens_comp l l1) (extract l1 vi) vk =
  merge_indices l vi vk.
Proof.
apply/eq_from_tnth => i.
case/boolP: (i \in l) => Hil.
  rewrite [RHS]tnth_merge_indices.
  have Hil1 : i \in lens_comp l l1 by rewrite mem_lens_comp mem_lens_full.
  rewrite tnth_merge_indices tnth_extract.
  congr tnth; apply (tnth_lens_inj (l:=l)).
  by rewrite -tnth_comp !tnth_lens_index.
rewrite -mem_lothers in Hil.
rewrite [RHS]tnth_merge_indices_lothers.
have Hic := Hil; rewrite -(lothers_comp_full _ l1) in Hic.
rewrite tnth_merge_indices_lothers.
congr tnth; apply/val_inj => /=.
by move/(f_equal (val \o val)): (lothers_comp_full l l1) => /= ->.
Qed.
End lens_assoc.

Section lens_rev.
Variables (I : Type) (dI : I) (n : nat).

Lemma uniq_lens_rev : uniq [tuple rev_ord i | i < n].
Proof.
rewrite (map_uniq (f:=@rev_ord n)) // -map_comp (eq_map (f2:=id)).
  by rewrite map_id enum_uniq.
by move=> x /=; rewrite rev_ordK.
Qed.
Definition lens_rev := mkLens uniq_lens_rev.

Lemma tnth_rev A (t : n.-tuple A) i :
  tnth [tuple of rev t] (rev_ord i) = tnth t i.
Proof.
rewrite (tnth_nth (tnth t i)) [RHS](tnth_nth (tnth t i)) /=.
rewrite nth_rev /= size_tuple; last by rewrite rev_ord_proof.
by move/(f_equal val): (rev_ordK i) => /= ->.
Qed.

Lemma merge_indices_rev m (l l' : lens m n)
      (vi vj : n.-tuple I) vk :
  l = rev l' :> seq _ -> vi = rev vj :> seq _ ->
  merge_indices dI l vi vk = merge_indices dI l' vj vk.
Proof.
move=> Hl Hv.
rewrite -(merge_indices_perm dI l' lens_rev).
f_equal.
  apply/eq_lens_tnth => i /=.
  rewrite tnth_extract tnth_mktuple -[LHS]tnth_rev.
  by congr tnth; apply/val_inj; rewrite /= Hl revK.
apply/eq_from_tnth => i.
rewrite tnth_extract tnth_mktuple -[LHS]tnth_rev.
by congr tnth; apply/val_inj; rewrite /= Hv revK.
Qed.
End lens_rev.

(* Computable Ordinal constants *)
Definition succO {n} := lift (@ord0 n).
Fixpoint addnO {n} m (p : 'I_n) : 'I_(m+n) :=
  match m as x return 'I_(x+n) with
  | 0 => p
  | m.+1 => cast_ord (esym (addSnnS m n)) (addnO m (succO p))
  end.
Lemma addnOK n m p : @addnO n m p = m + p :> nat.
Proof. elim: m n p => //= m IH n p. by rewrite IH /= addnS. Qed.

Definition INO {n} m := addnO m (@ord0 n).
Notation "n '%:O'" := (INO n) (at level 2, left associativity, format "n %:O").

Lemma succOS n m : succO m%:O = m.+1%:O :> 'I_(m.+1+n.+1).
Proof. apply/val_inj => /=. by rewrite /bump leq0n !addnOK !(addnC m). Qed.
Lemma succO0 n : succO ord0 = 1%:O :> 'I_n.+2.
Proof. exact/val_inj. Qed.
Definition succOE := (succO0,succOS).

Notation "[ 'lens' ]" := (@mkLens _ _ [tuple] erefl).
Notation "[ 'lens' x1 ; .. ; xn ]" :=
  (@mkLens _ _ [tuple of x1%:O :: .. [:: xn%:O] ..] erefl).

Fixpoint enum_ordinal n : seq 'I_n :=
  match n with
  | 0 => [::]
  | m.+1 => ord0 :: map succO (enum_ordinal m)
  end.

Lemma enum_ordinalE n : enum 'I_n = enum_ordinal n.
Proof.
apply/(@inj_map _ _ (val : 'I_n -> nat)). exact val_inj.
rewrite val_enum_ord.
elim: n => //= n IH.
rewrite -map_comp -(eq_map (f1:=S \o nat_of_ord (n:=n))) //.
by rewrite map_comp -IH (iotaDl 1 0 n).
Qed.

Ltac eq_lens :=
  apply/val_inj/eqP; rewrite ?eq_ord_tuple /= /others /= ?enum_ordinalE.

Section ordinal_examples.
Eval compute in uniq [tuple 0%:O; 1%:O; 2%:O]. (* = true *)

Let lens3_23 : lens 3 2 := [lens 1; 2].
End ordinal_examples.
