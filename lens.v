From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ 'lens' x1 ; .. ; xn ]"
  (format "[ 'lens'  x1 ;  .. ;  xn ]").

(* Utility lemmas *)

Lemma addnLR m n p : m + n = p -> n = p - m.
Proof. move/(f_equal (subn^~ m)); by rewrite addKn. Qed.

Lemma ltn_ordK q (i : 'I_q) : Ordinal (ltn_ord i) = i.
Proof. by apply val_inj. Qed.

Section tnth.
Variables (T : Type) (m n : nat) (vl : m.-tuple T) (vr : n.-tuple T).

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

Definition lens_index : 'I_m := Ordinal (proj2 (index_tuple l i) H).

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

(* Identity *)
Section lens_id.
Variable n : nat.
Lemma uniq_ord_tuple : uniq (ord_tuple n). Proof. exact/enum_uniq. Qed.
Definition lens_id := mkLens uniq_ord_tuple.

Lemma extract_lens_id I (v : n.-tuple I) : extract lens_id v = v.
Proof. apply eq_from_tnth => i; by rewrite tnth_map tnth_ord_tuple. Qed.

Lemma index_lens_id i : index i lens_id = i.
Proof. by rewrite {1}(_ : i = tnth lens_id i) (tnth_ord_tuple,tnth_lensK). Qed.
End lens_id.

(* Empty lens *)
Section lens_empty.
Variable n : nat.
Definition lens_empty : lens n 0 := {|lens_t := [tuple]; lens_uniq := erefl|}.

Lemma extract_lens_empty T v : extract (T:=T) lens_empty v = [tuple].
Proof. rewrite /extract; exact/val_inj. Qed.
End lens_empty.

(* Composition of lenses *)
Section lens_comp.
Variables (n m p : nat) (l1 : lens n m) (l2 : lens m p).

Definition lens_comp : lens n p.
exists (extract l2 l1).
abstract (by (rewrite map_inj_uniq ?lens_uniq // => i j /tnth_inj-> //;
          exact: lens_uniq)).
Defined.

Lemma tnth_comp i : tnth lens_comp i = tnth l1 (tnth l2 i).
Proof. by rewrite tnth_map. Qed.

Variable (T : Type).

Lemma extract_comp (t : n.-tuple T) :
  extract lens_comp t = extract l2 (extract l1 t).
Proof. apply eq_from_tnth => i; by rewrite !tnth_map. Qed.

(* Composition for subvectors *)

Lemma index_lens_comp i (H : i \in l1) :
  index i lens_comp = index (lens_index H) l2.
Proof.
have {1}-> : i = tnth l1 (lens_index H) by rewrite (tnth_nth i) nth_index.
rewrite index_map //; exact/tnth_inj/lens_uniq.
Qed.

Lemma mem_lens_comp i (H : i \in l1) :
  (i \in lens_comp) = (lens_index H \in l2).
Proof. by rewrite -!index_mem !size_tuple index_lens_comp. Qed.

Lemma inject_comp (t : n.-tuple T) t' :
  inject l1 t (inject l2 (extract l1 t) t') = inject lens_comp t t'.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple.
case/boolP: (i \in l1) => Hl1.
  rewrite nth_lens_index index_lens_comp.
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
apply eq_from_tnth => i; rewrite !tnth_map !tnth_ord_tuple.
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

Section merge_lens.
Variables (I : Type) (dI : I) (n m : nat) (l : lens n m).

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

Lemma extract_merge v1 v2 : extract l (merge_indices v1 v2) = v1.
Proof.
apply eq_from_tnth => i.
by rewrite !tnth_map tnth_ord_tuple tnth_lensK -tnth_nth.
Qed.

Lemma extract_lothers_merge v1 v2 : extract lothers (merge_indices v1 v2) = v2.
Proof.
apply eq_from_tnth => i; rewrite !tnth_map tnth_ord_tuple nth_lens_out //.
  by rewrite tnth_lensK -tnth_nth.
by rewrite -mem_lothers mem_tnth.
Qed.

Lemma merge_indices_extract_others v1 v2 :
  merge_indices v2 (extract lothers v1) = inject l v1 v2.
Proof.
apply eq_from_tnth => i; rewrite !tnth_mktuple.
case/boolP: (i \in l) => Hil; first by rewrite !nth_lens_index.
by rewrite !(nth_extract_index,nth_lens_out) // mem_lothers.
Qed.

Lemma merge_indices_extract (v : n.-tuple I) :
  merge_indices (extract l v) (extract lothers v) = v.
Proof. by rewrite merge_indices_extract_others inject_extract. Qed.

Lemma extract_merge_disjoint p (l' : lens n p) vi vj :
  [disjoint l & l'] ->
  extract l' (merge_indices vj (extract lothers vi)) = extract l' vi.
Proof.
move=> Hdisj; apply eq_from_tnth => i; rewrite !tnth_map tnth_ord_tuple.
have Hil : tnth l' i \notin l by rewrite (disjointFl Hdisj) // mem_tnth.
have Hilo : tnth l' i \in lothers by rewrite mem_lothers.
by rewrite nth_lens_out ?nth_lens_index // tnth_map lens_indexK.
Qed.
End merge_lens.

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
apply/val_inj/val_inj => /=.
by rewrite -[RHS](cat_take_drop m) take_enum_lshift drop_enum_rshift.
Qed.

Variables (p : nat) (l : lens p m) (l' : lens p n) (H : [disjoint l & l']).

Lemma lens_comp_left : l = lens_comp (lens_cat H) lens_left.
Proof.
apply/val_inj/eq_from_tnth => i /=.
by rewrite !tnth_map tnth_ord_tuple tnth_lshift.
Qed.

Lemma lens_comp_right : l' = lens_comp (lens_cat H) lens_right.
Proof.
apply/val_inj/eq_from_tnth => i /=.
by rewrite !tnth_map tnth_ord_tuple tnth_rshift.
Qed.
End lens_left_right.

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
  by rewrite (nth_lens_index Hi) tnth_map lens_indexK.
rewrite nth_lens_out // tnth_mktuple.
have := lens_all i.
rewrite (negbTE Hi) orbF => Him.
by rewrite (nth_lens_index Him) tnth_map lens_indexK.
Qed.      
End inject_all.

(* associativity of focussing *)
Section lens_assoc.
Variables (I : Type) (dI : I) (n m p : nat) (l : lens n m) (l' : lens m p).

Local Notation merge_indices := (merge_indices dI).

Definition lothers_comp := lothers (lens_comp l l').

Lemma others_in_l_present i :
  tnth (lens_comp l (lothers l')) i \in lothers_comp.
Proof.
rewrite mem_lothers; apply/mapP => -[k Hk].
rewrite tnth_comp => /tnth_inj Hi.
by apply/negP: Hk; rewrite -mem_lothers -Hi (mem_tnth,lens_uniq).
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
rewrite map_inj_uniq ?(lens_uniq (lothers l')) //; exact/tnth_inj/lens_uniq.
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
apply/val_inj/eq_from_tnth => i.
by rewrite !tnth_map tnth_ord_tuple lens_indexK.
Qed.

Lemma sorted_others q r (ln : lens q r) : sorted ord_ltn (others ln).
Proof. exact/sorted_filter/sorted_enum/ltn_trans. Qed.

Lemma sorted_lens_eq q r (l1 l2 : lens q r) :
  sorted ord_ltn l1 -> sorted ord_ltn l2 -> l1 =i l2 -> l1 = l2.
Proof.
move=> Hl1 Hl2 Heq; apply/val_inj/val_inj => /=.
apply: (sorted_eq (leT:=ord_ltn) ltn_trans) => //.
- move=> x y /andP[]. by rewrite /ord_ltn /= (ltnNge y) => /ltnW ->.
- apply uniq_perm => //; exact: lens_uniq.
Qed.

Lemma lothers_notin_l_comp :
  lens_comp lothers_comp lothers_notin_l = lothers l.
Proof.
apply sorted_lens_eq; do? apply/sorted_comp; try apply/sorted_others.
  exact: ltn_trans.
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
  apply (tnth_inj _ (lens_uniq lothers_comp)).
  by rewrite -tnth_comp lothers_in_l_comp tnth_comp -Hi' Hk lens_indexK.
- have/tnthP [j Hj] :  i \in lothers_comp.
    rewrite mem_lothers; apply: contra Hi => /mapP [j Hj] ->.
    exact: mem_tnth.
  exists j => //.
  rewrite mem_lothers; apply: contra Hi => /mapP [k _].
  rewrite Hj => ->.
  have Hol := others_in_l_present k.
  by rewrite lens_indexK tnth_map mem_tnth.
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
rewrite /merge_indices => Hlm.
apply eq_mktuple => i.
case/boolP: (i \in lens_comp l l') => Hi.
  case/mapP: Hi => j Hj ->.
  rewrite tnth_lensK -tnth_nth tnth_mktuple index_map ?(nth_lens_index Hj) //.
  exact/tnth_inj/lens_uniq.
have Hilo : i \in lothers_comp by rewrite mem_lothers.
rewrite nth_lens_out // nth_lens_index tnth_mktuple.
case/boolP: (i \in l) => Hil.
  rewrite mem_lens_comp in Hi.
  rewrite (nth_lens_index Hil) tnth_mktuple [RHS]nth_lens_out //.
  rewrite -mem_lothers in Hi.
  rewrite (nth_lens_index Hi).
  have <- : tnth lothers_in_l (lens_index Hi) = lens_index Hilo.
    apply (tnth_inj _ (lens_uniq lothers_comp)).
    by rewrite -tnth_comp lothers_in_l_comp tnth_comp !lens_indexK.
  by rewrite tnth_lensK -tnth_nth.
rewrite [RHS]nth_lens_out //.
have Hillo : lens_index Hilo \notin lothers_in_l.
  apply: contra Hil.
  case/tnthP => j /(f_equal (tnth lothers_comp)); rewrite lens_indexK => ->.
  by rewrite -tnth_comp lothers_in_l_comp tnth_comp mem_tnth.
rewrite [LHS]nth_lens_out //.
congr nth => //.
have Hillo' : lens_index Hilo \in lothers_notin_l by rewrite mem_lothers.
rewrite -mem_lothers in Hil.
rewrite (make_lens_index Hillo') (make_lens_index Hil).
congr val.
apply (tnth_inj _ (lens_uniq (lothers l))).
by rewrite -[in LHS]lothers_notin_l_comp tnth_comp !lens_indexK.
Qed.
End lens_assoc.

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
