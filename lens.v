From mathcomp Require Import all_ssreflect all_algebra.
From HB Require Import structures.
Require Export mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "[ 'lens' x1 ; .. ; xn ]"
  (format "[ 'lens'  x1 ;  .. ;  xn ]").
Reserved Notation "[ 'lens' ]" (format "[ 'lens' ]").

Section lens.
Variables (T : Type) (n m : nat).

Record lens := mkLens {lens_t :> m.-tuple 'I_n ; lens_uniq : uniq lens_t}.
HB.instance Definition _ := [isSub for lens_t].
Canonical lens_predType := PredType (pred_of_seq : lens -> pred 'I_n).

HB.instance Definition lens_isFinite := [Finite of lens by <:].

Definition endo1 := m.-tuple T -> m.-tuple T.

Variables (l : lens) (f : endo1).

Definition extract (t : n.-tuple T) := map_tuple (tnth t) l.

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

Lemma extract_cst (a : T) : extract [tuple a | _ < n] = [tuple a | _ < m].
Proof. apply eq_from_tnth => i; by rewrite tnth_extract !tnth_mktuple. Qed.

Lemma lens_sortedP :
  reflect (exists p, l = [seq i <- enum 'I_n | p i] :> seq _) (lens_sorted l).
Proof.
case/boolP: (lens_sorted l) => Hl; constructor.
  exists (mem l). apply/(irr_sorted_eq (leT:=ord_ltn)) => //.
  - exact/ltn_trans.
  - by move=> x; rewrite /ord_ltn /= ltnn.
  - exact/sorted_filter/sorted_ord_enum/ltn_trans.
  - by move=> i; rewrite mem_filter mem_enum andbT.
case => p Hp.
move/negP: Hl; elim.
rewrite /lens_sorted Hp.
exact/sorted_filter/sorted_ord_enum/ltn_trans.
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

Lemma tnth_injectC t t' i :
  i \notin l -> tnth (inject t t') i = tnth t i.
Proof. by move=> H; rewrite tnth_mktuple nth_lens_out. Qed.

Lemma inject_extract t : inject t (extract t) = t.
Proof.
apply/eq_from_tnth => i.
case/boolP: (i \in l) => H; last by rewrite tnth_injectC.
by rewrite tnth_inject tnth_extract tnth_lens_index.
Qed.

Lemma extract_inject t v : extract (inject t v) = v.
Proof.
apply/eq_from_tnth => i.
by rewrite tnth_map (tnth_inject _ _ (mem_tnth i l)) lens_indexK.
Qed.
End lens.

Lemma focus1_id T n m (l : lens n m) (v : n.-tuple T) : focus1 l id v = v.
Proof.
apply eq_from_tnth => i. case/boolP: (i \in l) => Hi.
- by rewrite tnth_inject tnth_extract tnth_lens_index.
- by rewrite focus1_out.
Qed.

(* Cast *)
Section cast_lens.
Variables (n n' m m' : nat).

Definition cast_lens_ord (H : n = n') (l : lens n m) : lens n' m.
exists (map_tuple (cast_ord H) l).  
abstract (by rewrite map_inj_uniq ?lens_uniq // => i j /cast_ord_inj).
Defined.

Definition cast_lens (H : m' = m) (l : lens n m') : lens n m.
exists (cast_tuple H l).
apply lens_uniq.
Defined.

Lemma cast_tuple_extract I (H : m' = m) (l : lens n m') (v : n.-tuple I) :
  cast_tuple H (extract l v) = extract (cast_lens H l) v.
Proof. exact/val_inj. Qed.

Variables (l : lens n m) (l' : lens n m').

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

Lemma lens_eq_cast : l = cast_lens lens_size_eq l'.
Proof. exact/lens_inj. Qed.

Lemma extract_eq_cast A (v : n.-tuple A) :
 extract l v = cast_tuple lens_size_eq (extract l' v).
Proof. apply val_inj => /=. by rewrite H. Qed.
End cast_lens.

Lemma cast_lens_ordE n m (l : lens n m) H : cast_lens_ord (n':=n) H l = l.
Proof. apply/eq_lens_tnth => i; rewrite tnth_map; by apply/val_inj. Qed.

Lemma cast_lensE n m (l : lens n m) H : cast_lens (m':=m) H l = l.
Proof. exact/lens_inj. Qed.

(* Identity *)
Section lens_id.
Variable n : nat.
Lemma uniq_ord_tuple : uniq (ord_tuple n). Proof. exact/enum_uniq. Qed.
Definition lens_id := mkLens uniq_ord_tuple.

Lemma lens_sorted_id : lens_sorted lens_id.
Proof. exact: sorted_ord_enum. Qed.

Lemma tnth_lens_id i : tnth lens_id i = i.
Proof. by rewrite tnth_ord_tuple. Qed.

Lemma extract_lens_id I (v : n.-tuple I) : extract lens_id v = v.
Proof. apply eq_from_tnth => i. by rewrite tnth_extract tnth_lens_id. Qed.

Lemma lens_index_id i (H : i \in lens_id) : lens_index H = i.
Proof. by apply/val_inj; rewrite /= index_enum_ord. Qed.

Lemma mem_lens_id i : i \in lens_id.
Proof. by rewrite -(tnth_ord_tuple i) mem_tnth. Qed.

Lemma index_lens_id i : index i lens_id = i.
Proof. by move/(f_equal val): (lens_index_id (mem_lens_id i)). Qed.
End lens_id.

(* Composition of lenses *)
Section lens_comp.
Variables (n m p : nat) (l1 : lens n m) (l2 : lens m p).

Lemma lens_comp_uniq : uniq (extract l2 l1).
Proof. by rewrite map_inj_uniq ?lens_uniq // => i j /tnth_lens_inj ->. Qed.

Definition lens_comp : lens n p := mkLens lens_comp_uniq.

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
  by rewrite tnth_injectC // tnth_extract tnth_lens_index nth_lens_out.
by rewrite !tnth_injectC // mem_lens_comp_out.
Qed.

Lemma focus1A (f : p.-tuple T -> p.-tuple T) :
  focus1 l1 (focus1 l2 f) =1 focus1 lens_comp f.
Proof. move=> t; by rewrite /focus1 inject_comp extract_comp. Qed.

(* Commutativity of subvector operations *)

Section disjoint_lenses.
Variables (q r : nat) (l : lens n q) (l' : lens n r) (t : n.-tuple T).
Hypothesis Hdisj : [disjoint l & l'].

Lemma extract_inject_out t' : extract l (inject l' t t') = extract l t.
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
  by rewrite tnth_injectC // !tnth_inject.
case/boolP: (i \in l') => Hil'.
  by rewrite tnth_inject tnth_injectC // tnth_inject.
by rewrite !tnth_injectC.
Qed.

Lemma focus1_commu_in (f : endo1 T q) (g : endo1 T r) i : i \in l ->
  tnth (focus1 l f (focus1 l' g t)) i = tnth (focus1 l' g (focus1 l f t)) i.
Proof.
move=> Hl; have Hl' : i \notin l' by rewrite (disjointFr Hdisj).
by rewrite (focus1_out _ _ Hl') /focus1 extract_inject_out // !tnth_inject.
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

Lemma lens_comp_inj n m p (l1 : lens n m) : injective (@lens_comp _ _ p l1).
Proof.
move=> l2 l3 H; apply eq_lens_tnth => i.
move/(f_equal (fun l : lens n p => tnth l i)): H.
by rewrite !tnth_comp => /tnth_lens_inj ->.
Qed.

Lemma cast_lens_comp n m p p' (H : p = p') (l1 : lens n m) (l2 : lens m p) :
  cast_lens H (lens_comp l1 l2)  = lens_comp l1 (cast_lens H l2).
Proof. by apply/val_inj; rewrite /= cast_tuple_extract. Qed.

Lemma lens_compA n m p q (l1 : lens n m) l2 (l3 : lens p q) :
  lens_comp (lens_comp l1 l2) l3 = lens_comp l1 (lens_comp l2 l3).
Proof. apply eq_lens_tnth => i; by rewrite !tnth_comp. Qed.

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
rewrite /seq_basis enum_filterP -cardE -{2}(size_tuple l).
exact/eqP/card_uniqP/lens_uniq.
Qed.
Lemma uniq_basis : uniq (Tuple size_basis).
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Definition lens_basis := mkLens uniq_basis.

Lemma mem_lens_basis : lens_basis =i l.
Proof. by move=> i; rewrite mem_filter mem_enum andbT. Qed.

Lemma lens_sorted_basis : lens_sorted lens_basis.
Proof. by apply/lens_sortedP; exists (mem l). Qed.

Lemma lens_basis_sortedE : lens_sorted l -> lens_basis = l.
Proof.
move=> H; exact/lens_inj/eq_lens_sorted/H/lens_sorted_basis/mem_lens_basis.
Qed.

Lemma perm_in_basis i : tnth l i \in lens_basis.
Proof. by rewrite mem_lens_basis mem_tnth. Qed.

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
apply: (tnth_lens_inj (l:=lens_basis)).
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
rewrite cardsE cardE -filter_predI.
congr size; apply eq_filter => /= i. 
by rewrite !inE andbT.
Qed.

Definition seq_lensC := [seq i <- enum 'I_n | i \notin l].
Lemma size_lensC : size seq_lensC == n - m.
Proof.
move/cardsC/addnLR: [set i in l].
rewrite [LHS]cards_filter /=.
rewrite (_ : filter _ _ = seq_lensC);
  last by apply eq_filter => i; rewrite !inE.
move/card_uniqP: (lens_uniq l).
by rewrite size_tuple cardT size_enum_ord cardsE => -> ->.
Qed.

Lemma mem_seq_lensC i : (i \in seq_lensC) = (i \notin l).
Proof. by rewrite mem_filter mem_enum andbT. Qed.

Lemma uniq_lensC : uniq (Tuple size_lensC).
Proof. by rewrite filter_uniq // enum_uniq. Qed.

Definition lensC : lens n (n-m) := mkLens uniq_lensC.

Lemma mem_lensC i : (i \in lensC) = (i \notin l).
Proof. by rewrite mem_seq_lensC. Qed.

Lemma lens_sorted_lensC : lens_sorted lensC.
Proof. exact/sorted_filter/sorted_ord_enum/ltn_trans. Qed.

(* For the definition of rank0 and select0, see:
   Gonzalo Navarro: Compact data structures, a practical approach.
   Cambridge University Press, 2016 *)

Definition rank0 j := #|[set i | (i \in lensC) && (i < j)]|.
Definition select0 i :=
  if i is k.+1 then (nth n (map val lensC) k).+1 else 0.

Definition lens_bits := [tuple i \in l | i < n].
Lemma rank0E j : rank0 j = count_mem false (take j lens_bits).
Proof.
rewrite /rank0 /lens_bits.
under eq_finset do rewrite mem_lensC.
rewrite cards_filter /= size_filter -map_take.
rewrite take_ord_enum count_map count_filter.
apply: eq_count => x /=.
by rewrite eqbF_neg.
Qed.

Lemma rank0_mono i j : i <= j -> rank0 i <= rank0 j.
Proof.
rewrite !rank0E => /minn_idPl <-.
by rewrite take_min leq_count_subseq // take_subseq.
Qed.

Lemma select0K i : i <= n - m -> rank0 (select0 i) = i.
Proof.
rewrite /rank0 /select0.
case: i => [_ | i Hi].
  rewrite cards_filter (eq_filter (a2:=pred0)) ?filter_pred0 // => x.
  by rewrite ltn0 andbF.
rewrite -(on_card_preimset (f:=tnth lensC)); last first.
  apply: (subon_bij (D2':=[pred y in [seq tnth lensC x | x in 'I_(n-m)]])).
    move=> /= j. rewrite !inE => /andP[] /tnthP[k ->] _.
    by rewrite map_f // mem_enum.
  apply/(bij_on_image (tnth_lens_inj (l:=lensC)))/(Ordinal Hi).
transitivity #|[set x in take i.+1 (ord_tuple (n-m))]|.
  congr #|pred_of_set _|; apply/setP => j.
  rewrite !inE mem_tnth ltnS.
  transitivity (j <= i).
    rewrite (_ : i = Ordinal Hi) // -tnth_nth tnth_map.
    case: (ltngtP (Ordinal Hi) j) => ij.
    - apply/negbTE; rewrite -ltnNge.
      exact/(@sorted_tnth _ ord_ltn)/ij/lens_sorted_lensC/ltn_trans.
    - exact/ltnW/(@sorted_tnth _ ord_ltn)/ij/lens_sorted_lensC/ltn_trans.
    - by rewrite (val_inj ij) leqnn.
  by rewrite in_take ?mem_enum // index_enum_ord ltnS.
rewrite cardsE.
have /card_uniqP -> : uniq (take i.+1 (ord_tuple (n-m))).
  exact/take_uniq/uniq_ord_tuple.
by rewrite size_takel // size_tuple.
Qed.

Lemma rank0_max i : i >= n -> rank0 i = n - m.
Proof.
rewrite /rank0 => Hin.
under eq_finset do rewrite (leq_trans (ltn_ord _)) // andbT.
rewrite cardsE -[RHS](size_tuple lensC).
exact/card_uniqP/lens_uniq.
Qed.

Lemma select0_max i : select0 i <= n.+1.
Proof.
case: i => // i.
case: (ltnP i (n-m)) => Hi.
  have Hin: i < n by rewrite (leq_trans _ (leq_subr m n)).
  rewrite /select0 (nth_map (Ordinal Hin)) ?size_tuple //.
  by rewrite /= ltnW // ltnS.
by rewrite /select0 nth_default // size_map size_tuple.
Qed.

Lemma rank0_pred_select0 i : 0 < i -> rank0 (select0 i).-1 < i.
Proof.
case: (ltnP (n-m) i).
  move=> Hin Hi.
  rewrite (leq_trans _ Hin) // ltnS -(@rank0_max n.+1) //.
  apply: rank0_mono.
  by rewrite (leq_trans (leq_pred _)) // select0_max.
case: i => //= i Hi _.
rewrite -(select0K Hi) !rank0E /select0.
rewrite (_ : seq_lensC = lensC) // {1}(_ : i = Ordinal Hi) // -tnth_nth.
rewrite tnth_map (take_nth true); last by rewrite size_tuple /=.
rewrite -tnth_nth -cats1 count_cat tnth_mktuple.
by rewrite -[_ \in _]negbK -mem_lensC mem_tnth addn1.
Qed.

Lemma select0_min i j : i <= n - m -> j < select0 i -> rank0 j < i.
Proof.
have [->|] := eqVneq i 0.
  by rewrite (ltn0 j).
rewrite -lt0n => H0i Hi Hj.
rewrite (leq_trans _ (rank0_pred_select0 _)) // ltnS.
rewrite !rank0E leq_count_subseq //.
have <- : minn j (select0 i).-1 = j.
  apply/minn_idPl.
  rewrite -ltnS prednK // /select0.
  by destruct i.
by rewrite take_min take_subseq.
Qed.

Lemma select0Kb i : i <= n - m -> rank0 (select0 i) == i.
Proof. by move=> *; apply/eqP/select0K. Qed.

Lemma select0E i (Hi : i <= n - m) :
  select0 i = ex_minn (ex_intro (fun j => rank0 j == i) _ (select0Kb Hi)).
Proof.
case: ex_minnP => j /eqP Hj Hrank.
have [] // := ltngtP (select0 i) j.
- destruct j => //.
  rewrite ltnS => /rank0_mono.
  rewrite select0K // -Hj => Hr'.
  move: (Hrank j).
  by rewrite -Hj eqn_leq Hr' rank0_mono // ltnn => /(_ isT).
- move/(select0_min Hi).
  by rewrite Hj ltnn.
Qed.

(* merge operation *)

Definition merge_nth (v : m.-tuple I) (w : (n-m).-tuple I) :=
  [tuple nth (nth dI w (index i lensC)) v (index i l) | i < n].

Lemma mem_lensNC i : i \notin l -> i \in lensC.
Proof. by rewrite mem_lensC. Qed.

Lemma mem_lensFC i : i \in l = false -> i \in lensC.
Proof. rewrite mem_lensC; exact/contraFN. Qed.

Definition merge (v : m.-tuple I) (w : (n-m).-tuple I) : n.-tuple I.
apply mktuple => i.
case (sumbool_of_bool (i \in l)) => H.
- exact (tnth v (lens_index H)).
- exact (tnth w (lens_index (mem_lensFC H))).
Defined.

Lemma mergeE v w : merge v w = merge_nth v w.
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple.
case: sumbool_of_bool => H.
  by rewrite nth_lens_index.
rewrite (tnth_nth dI) /= [RHS]nth_default // leqNgt.
by rewrite (size_tuple v) -{3}(size_lens l) index_mem negbT.
Qed.

Lemma tnth_merge_nth i vi vj (Hil : i \in l) :
  tnth (merge_nth vi vj) i = tnth vi (lens_index Hil).
Proof. by rewrite tnth_mktuple (make_lens_index Hil) -tnth_nth. Qed.

Lemma tnth_merge i vi vj (Hil : i \in l) :
  tnth (merge vi vj) i = tnth vi (lens_index Hil).
Proof.
rewrite tnth_mktuple; case: sumbool_of_bool => H.
  by congr tnth; apply/val_inj.
by exfalso; rewrite Hil in H.
Qed.

Lemma tnth_merge_nthC i vi vj (Hil : i \in lensC) :
  tnth (merge_nth vi vj) i = tnth vj (lens_index Hil).
Proof.
have Hil' := Hil; rewrite mem_lensC in Hil'.
rewrite !tnth_map !tnth_ord_tuple nth_lens_out //.
by rewrite (make_lens_index Hil) -!tnth_nth.
Qed.

Lemma tnth_mergeC i vi vj (Hil : i \in lensC) :
  tnth (merge vi vj) i = tnth vj (lens_index Hil).
Proof.
rewrite tnth_mktuple; case: sumbool_of_bool => H.
  by move: (Hil); rewrite mem_lensC H in Hil.
by congr tnth; apply/val_inj.
Qed.

Variant tnth_merge_index i vi vj : I -> Set :=
  | TnthMerge (H : i \in l) :
    tnth (merge vi vj) i = tnth vi (lens_index H) ->
    tnth_merge_index i vi vj (tnth (merge vi vj) i)
  | TnthMergeC (H : i \in lensC) :
    tnth (merge vi vj) i = tnth vj (lens_index H) ->
    tnth_merge_index i vi vj (tnth (merge vi vj) i).

Lemma tnth_mergeP i vi vj :
  tnth_merge_index i vi vj (tnth (merge vi vj) i).
Proof.
case/boolP: (i \in l) => Hi.
- exact/TnthMerge/tnth_merge.
- rewrite -mem_lensC in Hi; exact/TnthMergeC/tnth_mergeC.
Qed.

Lemma extract_merge v1 v2 : extract l (merge v1 v2) = v1.
Proof.
apply eq_from_tnth => i; rewrite tnth_extract.
by rewrite (tnth_merge _ _ (mem_tnth i l)) lens_indexK.
Qed.

Lemma extractC_merge v1 v2 : extract lensC (merge v1 v2) = v2.
Proof.
apply eq_from_tnth => i /=; rewrite tnth_extract.
by rewrite (tnth_mergeC _ _ (mem_tnth i lensC)) lens_indexK.
Qed.

Lemma merge_extractC v1 v2 :
  merge v2 (extract lensC v1) = inject l v1 v2.
Proof.
apply eq_from_tnth => i.
case: tnth_mergeP => Hi ->.
- by rewrite tnth_inject.
- by rewrite tnth_injectC -?mem_lensC // tnth_extract tnth_lens_index.
Qed.

Lemma merge_extract (v : n.-tuple I) :
  merge (extract l v) (extract lensC v) = v.
Proof. by rewrite merge_extractC inject_extract. Qed.

Lemma merge_inj vj : injective (fun vi => merge vi vj).
Proof.
move=> vi vi' Hm.
by rewrite -(extract_merge vi vj) -(extract_merge vi' vj) Hm.
Qed.

Lemma extract_merge_disjoint p (l' : lens n p) vi vj :
  [disjoint l & l'] ->
  extract l' (merge vj (extract lensC vi)) = extract l' vi.
Proof.
move=> Hdisj; apply eq_from_tnth => i; rewrite !tnth_extract.
rewrite tnth_mergeC => [|Hil].
  by rewrite mem_lensC (disjointFl Hdisj) // mem_tnth.
by rewrite tnth_extract tnth_lens_index.
Qed.
End merge_lens.

Lemma merge_inj_eq (I : eqType) n m (l : lens n m) v1 v2 v3 v4 :
  (@merge I _ _ l v1 v2 == merge l v3 v4) = ((v1 == v3) && (v2 == v4)).
Proof.
case/boolP: (merge _ _ _ == _) => /eqP Hm.
  rewrite -(extract_merge l v1 v2) Hm.
  rewrite -{2}(extract_merge l v3 v4) eqxx.
  rewrite -(extractC_merge l v1 v2) Hm.
  by rewrite -{2}(extractC_merge l v3 v4) eqxx.
case/boolP: (v1 == _) => // /eqP Hv1.
case/boolP: (v2 == _) => // /eqP Hv2.
by subst.
Qed.

Lemma eq_lensC n m m' (l : lens n m) (l' : lens n m') :
  l =i l' -> lensC l = lensC l' :> seq _.
Proof. by move=> ll'; apply/eq_filter => i; rewrite ll'. Qed.

Section lens_comp_lensC.
Variables (n m p : nat) (l : lens n m) (l' : lens (n - m) p).

Lemma disjoint_comp_lensC : [disjoint l & lens_comp (lensC l) l'].
Proof.
rewrite disjoint_sym disjoint_has -all_predC.
apply/allP => i /lens_comp_sub /=.
by rewrite mem_lensC.
Qed.

Lemma lens_comp_lensC :
  lens_comp (lensC l) (lensC l') =
  lensC (lens_cat disjoint_comp_lensC) :> seq _.
Proof.
apply/eq_lens_sorted/lens_sorted_lensC/lens_sorted_comp/lens_sorted_lensC
  /lens_sorted_lensC => i.
rewrite mem_lensC [in RHS]mem_lensE mem_cat negb_or.
case/boolP: (i \in l) => Hi /=.
  apply/negb_inj; by rewrite mem_lens_comp_out // mem_lensC Hi.
rewrite -mem_lensC in Hi.
rewrite mem_lens_comp mem_lensC -[in RHS](tnth_lens_index Hi) mem_map //.
exact/tnth_lens_inj.
Qed.
End lens_comp_lensC.

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

Lemma lensC_id : lensC (lens_id n) = lens_empty :> seq _.
Proof. apply/nilP. by rewrite /nilp size_tuple subnn. Qed.

Lemma lensC_empty : lensC lens_empty = lens_id n :> seq _.
Proof. by rewrite /lensC /seq_lensC /= filter_predT. Qed.

Lemma merge_empty (T : eqType) v w :
  merge (I:=T) lens_empty v w = cast_tuple (subn0 n) w.
Proof.
apply eq_from_tnth => i.
have Hi : i \in lensC lens_empty by rewrite mem_lensC.
pose dI := tnth w (lens_index Hi).
rewrite (tnth_mergeC _ _ Hi) 2!(tnth_nth dI) /=.
by rewrite [seq_lensC _]lensC_empty index_lens_id.
Qed.

Lemma merge_nth_empty (T : eqType) (dI : T) v w :
  merge_nth dI lens_empty v w = cast_tuple (subn0 n) w.
Proof.
rewrite /merge_nth (eq_mktuple (tnth (cast_tuple (subn0 n) w))); last first.
  move=> i.
  by rewrite nth_lens_out // lensC_empty index_lens_id (tnth_nth dI).
by apply eq_from_tnth => i; rewrite tnth_mktuple.
Qed.

Lemma lens_cat_emptyl m (l : lens n m) (H : [disjoint lens_empty & l]) :
  lens_cat H = l.
Proof. exact/lens_inj. Qed.
End lens_empty.

Section lens_full.
Variable (n : nat) (l : lens n n).

Lemma mem_lens_full i : i \in l.
Proof.
move/card_uniqP: (lens_uniq l) (cardC (mem l)) ->.
rewrite card_ord size_tuple => /(f_equal (subn^~ n)).
rewrite addKn subnn => /card0_eq/(_ i).
by rewrite !inE => /negbFE.
Qed.

Lemma lens_inv_uniq : uniq [tuple lens_index (mem_lens_full i) | i < n].
Proof.
rewrite -(map_inj_uniq (tnth_lens_inj (l:=l))).
rewrite -map_comp (@eq_map _ _ _ (@idfun _)).
  by rewrite map_id enum_uniq.
by move=> x; rewrite /= tnth_lens_index.
Qed.

Definition lens_inv : lens n n := mkLens lens_inv_uniq.

Lemma lens_invE : lens_comp lens_inv l = lens_id n.
Proof.
apply eq_lens_tnth => i.
by rewrite tnth_comp tnth_mktuple lens_indexK tnth_lens_id.
Qed.

Lemma lens_invE' : lens_comp l lens_inv = lens_id n.
Proof.
apply eq_lens_tnth => i.
by rewrite tnth_comp tnth_mktuple tnth_lens_index tnth_lens_id.
Qed.

Lemma extract_inj T : injective (@extract T _ _ l).
Proof.
move=> x y. move/(f_equal (extract lens_inv)).
by rewrite -!extract_comp lens_invE' !extract_lens_id.
Qed.

Lemma lensC_full : lensC l = lens_empty n :> seq _.
Proof.
rewrite /= /seq_lensC (eq_filter (a2:=pred0)) ?filter_pred0 //= => i.
by rewrite mem_lens_full.
Qed.
End lens_full.

Lemma lensC_comp_full n m (l : lens n m) (l1 : lens m m) :
  lensC (lens_comp l l1) = lensC l.
Proof.
apply/lens_inj/eq_lensC => i.
case/boolP: (i \in l) => Hi. by rewrite mem_lens_comp mem_lens_full.
apply/negbTE; apply: contra Hi. exact/lens_comp_sub.
Qed.

Section merge_basis.
Variables (I : Type) (n m : nat) (l : lens n m).
Lemma merge_basis vi vj :
  merge (I:=I) (lens_basis l) vi vj = merge l (extract (lens_perm l) vi) vj.
Proof.
apply eq_from_tnth => i.
case: tnth_mergeP => Hib ->.
  rewrite tnth_merge => [|Hil]. by rewrite -mem_lens_basis.
  rewrite tnth_extract.
  congr tnth.
  apply/(tnth_lens_inj (l:=lens_basis l)).
  by rewrite -tnth_comp lens_basis_perm !tnth_lens_index.
rewrite tnth_mergeC => [|Hil].
  by rewrite -(lens_basis_perm l) lensC_comp_full.
congr tnth; apply/val_inj => /=.
congr index.
move/(f_equal (val \o val)): (lensC_comp_full (lens_basis l) (lens_perm l)).
by rewrite lens_basis_perm.
Qed.
End merge_basis.

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

Lemma tnth_merge_single T i vi vj :
  tnth (merge (lens_single i) vi vj) i = tnth vi ord0 :> T.
Proof.
rewrite tnth_merge. by rewrite inE eqxx.
by move=> H; rewrite ord1.
Qed.
End lens_single.

Lemma tnth_lensC_single n (i : 'I_n.+2) (k : 'I_n.+1) :
    tnth (lensC (lens_single i)) k = lift i k.
Proof.
apply/val_inj; rewrite (tnth_nth i); case: k => /=.
elim: (n.+1) i => {n} [|n IH] i k.
  by rewrite ltn0.
move/eqP: (size_lensC (lens_single i)); rewrite /seq_lensC enum_ordSl.
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
rewrite inE /=.
apply/negP => /andP [].
case: (split_ordP i) => [j -> _ | j ->] /mapP [k] _ /eqP.
- by rewrite eq_sym eq_rlshift.
- by rewrite eq_rlshift.
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

Lemma lensC_left : lensC lens_left = lens_right :> seq _.
Proof.
rewrite /lensC /seq_lensC /=.
have /= := f_equal val lens_left_right.
rewrite -(val_ord_tuple (m+n)) => <-.
rewrite filter_cat filter_map -(eq_filter (a1:=pred0)); last first.
  move=> i /=; rewrite mem_lensE mem_map ?mem_enum //; exact/lshift_inj.
rewrite filter_pred0 filter_map -(eq_filter (a1:=predT)) ?filter_predT //.
move=> i /=. rewrite mem_lensE /=.
by apply/esym/mapP => -[x _] /eqP; rewrite eq_shift.
Qed.

Lemma lensC_right : lensC lens_right = lens_left :> seq _.
Proof.
rewrite /lensC /seq_lensC /=.
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
Variables (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType).

Lemma reindex_merge n m (l : lens n m) F :
  \big[op/idx]_i F i = \big[op/idx]_i \big[op/idx]_j F (merge (I:=I) l i j).
Proof.
rewrite [RHS](pair_bigA _ (fun i j => F (merge l i j))).
rewrite (reindex (fun v : m.-tuple I * (n-m).-tuple I =>
                    merge l (fst v) (snd v))) //=.
exists (fun v => (extract l v, extract (lensC l) v)) => // v _.
  by rewrite extract_merge extractC_merge; case: v.
by rewrite /= merge_extract.
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
  rewrite cards_filter (eqP (size_lensC ln)) addnK.
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
case/boolP: (i \in ln) => Hi.
  by rewrite tnth_inject tnth_extract tnth_lens_index.
rewrite tnth_injectC //.
have := lens_all i.
rewrite (negbTE Hi) orbF => Him.
by rewrite tnth_inject tnth_extract tnth_lens_index.
Qed.
End inject_all.

(* Shifting of disjoint lenses *)
Section make_comp.
Variables (n m p : nat) (l : lens n m) (l' : lens n p).
Hypothesis Hdisj : [disjoint l & l'].

Lemma make_comp_present i :
  tnth l' i \in lensC l.
Proof.
move: (mem_tnth i l').
rewrite mem_lensC => Hl'; apply/negP => Hl.
move: Hdisj; rewrite disjoint_has => /hasP; elim.
by exists (tnth l' i).
Qed.

Definition make_comp :=
  [tuple lens_index (make_comp_present i) | i < p].

Lemma uniq_map_comp : uniq make_comp.
Proof.
rewrite /make_comp/= map_inj_in_uniq ?enum_uniq // => i j _ _.
move/(f_equal (tnth (lensC l))).
by rewrite !tnth_lens_index => /tnth_lens_inj.
Qed.

Definition lmake_comp := mkLens uniq_map_comp.

Lemma lmake_compE : lens_comp (lensC l) lmake_comp = l'.
Proof.
apply/eq_lens_tnth => i.
rewrite tnth_map tnth_mktuple (tnth_nth (tnth l' i)) /=.
by rewrite nth_index // make_comp_present.
Qed.
End make_comp.

(* associativity of focussing *)
Section lens_assoc.
Variables (I : Type) (n m p : nat) (l : lens n m) (l' : lens m p).

Local Notation merge := (merge (I:=I)).

Definition lensC_comp := lensC (lens_comp l l').

Lemma others_in_l_present i :
  tnth (lens_comp l (lensC l')) i \in lensC_comp.
Proof.
rewrite mem_lensC; apply/mapP => -[k Hk].
rewrite tnth_comp => /tnth_lens_inj Hi.
by apply/negP: Hk; rewrite -mem_lensC -Hi mem_tnth.
Qed.

Definition others_in_l :=
  [tuple lens_index (others_in_l_present i) | i < m - p].

Lemma uniq_others_in_l : uniq (others_in_l).
Proof.
apply/tnth_inj => i j; rewrite !tnth_mktuple => /(f_equal (tnth lensC_comp)).
by rewrite !tnth_lens_index => /tnth_lens_inj.
Qed.

Definition lensC_in_l := mkLens uniq_others_in_l.

Lemma cast_lensC_notin_l : n - p - (m - p) = n - m.
Proof. rewrite subnBA ?subnK // lens_leq //. exact: (lens_comp l l'). Qed.

Lemma size_lensC_notin_l : size (lensC lensC_in_l) == n - m.
Proof. by rewrite size_tuple cast_lensC_notin_l. Qed.

Definition lensC_notin_l : lens (n-p) (n-m).
exists (Tuple size_lensC_notin_l).
exact (lens_uniq (lensC lensC_in_l)).
Defined.

Lemma lensC_in_l_comp :
  lens_comp lensC_comp lensC_in_l = lens_comp l (lensC l').
Proof.
apply/eq_lens_tnth => i.
by rewrite !tnth_map tnth_ord_tuple tnth_lens_index.
Qed.

Lemma cast_lensC_notin_l' : (n - p) - (n - m) = m - p.
Proof.
rewrite subnBA; last by apply lens_leq.
rewrite -addnABC; try apply/lens_leq => //; first last.
  exact (lens_comp l l').
by rewrite addKn.
Qed.

Lemma lens_basis_lensC_in_l :
  lens_basis lensC_in_l = lensC lensC_notin_l :> seq _.
Proof.
apply eq_lens_sorted.
- move=> x; by rewrite !(mem_lensC,mem_lens_basis) negbK.
- apply lens_sorted_basis.
- apply lens_sorted_lensC.
Qed.

Lemma lensC_lensC_notin_l_perm :
  lens_comp (cast_lens cast_lensC_notin_l' (lensC lensC_notin_l))
            (lens_perm lensC_in_l) = lensC_in_l.
Proof.
apply eq_lens_tnth => i.
rewrite !tnth_comp.
pose i1 :=
  tnth (lensC lensC_notin_l) (cast_ord (esym cast_lensC_notin_l') i).
rewrite (tnth_nth i1) /=.
rewrite -[seq_lensC lensC_notin_l]lens_basis_lensC_in_l.
set t := tnth (tuple_perm _) i.
rewrite (_ : t = cast_ord (esym cast_lensC_notin_l') t :> nat) //.
apply (@tnth_lens_inj _ _ lensC_comp).
rewrite -tnth_nth -(tnth_comp (lensC (lens_comp l l'))).
rewrite /t tnth_comp -(tnth_comp _ (lens_perm lensC_in_l)).
by rewrite lens_basis_perm -tnth_comp lensC_in_l_comp tnth_comp.
Qed.

Lemma lensC_notin_l_comp :
  lens_comp lensC_comp lensC_notin_l = lensC l.
Proof.
apply/lens_inj/eq_lens_sorted/lens_sorted_lensC/lens_sorted_comp;
  try exact/sorted_filter/sorted_ord_enum/ltn_trans.
move=> /= i; rewrite mem_lensC.
case/boolP: (i \in l) => /= Hi; apply/mapP.
- case=> j; rewrite mem_lensC => Hj Hi'.
  apply/negP: Hj; rewrite negbK; apply/tnthP.
  case/tnthP: Hi => k Hk.
  have Hk' : k \in lensC l'.
    rewrite mem_lensC; apply/tnthP => -[h] Hh.
    have : i \in lensC_comp by rewrite Hi' mem_tnth.
    by rewrite Hk Hh -tnth_comp mem_lensC mem_tnth.
  exists (lens_index Hk').
  apply (tnth_lens_inj (l:=lensC_comp)).
  by rewrite -tnth_comp lensC_in_l_comp tnth_comp -Hi' Hk tnth_lens_index.
- have/tnthP [j Hj] :  i \in lensC_comp.
    rewrite mem_lensC; apply: contra Hi => /mapP [j Hj] ->.
    exact: mem_tnth.
  exists j => //.
  rewrite mem_lensC; apply: contra Hi => /mapP [k _].
  rewrite Hj => ->.
  have Hol := others_in_l_present k.
  by rewrite tnth_lens_index tnth_map mem_tnth.
Qed.

Lemma extract_lensC_comp (v : n.-tuple I) :
  extract lensC_comp v =
  merge lensC_in_l (extract (lens_comp lensC_comp lensC_in_l) v)
        (extract (lens_comp lensC_comp (lensC lensC_in_l)) v).
Proof. by rewrite !extract_comp merge_extract. Qed.

Lemma merge_comp vj vk (vl : (n-p - (m-p)).-tuple I)
                               (vm : (n-m).-tuple I) :
  vl = vm :> seq I ->  (* can we use S-prop here? *)
  merge (lens_comp l l') vj (merge lensC_in_l vk vl) =
  merge l (merge l' vj vk) vm.
Proof.
move=> Hlm.
apply/eq_from_tnth => i.
case: (tnth_mergeP l) => Hil ->.
  case: (tnth_mergeP l') => Hill' ->.
    rewrite tnth_merge => [|Hilcl']. by rewrite mem_lens_comp.
    congr tnth; apply/val_inj => /=; by rewrite -index_lens_comp.
  have Hilo : i \in lensC_comp by rewrite mem_lensC mem_lens_comp -mem_lensC.
  rewrite tnth_mergeC.
  have Hic : i \in lens_comp l (lensC l') by rewrite mem_lens_comp.
  rewrite tnth_merge => [|Hilol].
    by rewrite -lensC_in_l_comp mem_lens_comp in Hic.
  congr tnth; apply (tnth_lens_inj (l:=lens_comp l (lensC l'))).
  by rewrite -{1}lensC_in_l_comp !tnth_comp !tnth_lens_index.
case: tnth_mergeP => [/lens_comp_sub Hic _ | Hic ->].
  by have : False by rewrite mem_lensC Hic in Hil.
rewrite tnth_mergeC => [|Hlil].
  rewrite -mem_lens_comp mem_lensE /=.
  by move/(f_equal (val \o val)): lensC_notin_l_comp => /= ->.
set a := tnth vl _; rewrite /a (tnth_nth a) /= Hlm [RHS](tnth_nth a) /=.
congr nth. 
have /(f_equal (val \o val)) := lensC_notin_l_comp; rewrite [RHS]/= => <-.
by rewrite -[LHS](index_lens_comp (lensC lensC_in_l)).
Qed.

(* For focus_others, only uses variables *)
Lemma merge_comp_others (l1 : lens (n-m) p) vi vj :
  merge (lens_comp (lensC l) l1) vj
        (extract (lensC (lens_comp (lensC l) l1)) vi) =
  merge l (extract l vi)
        (merge l1 vj (extract (lens_comp (lensC l) (lensC l1)) vi)).
Proof.
set l2 := lens_comp (lensC l) l1.
apply eq_from_tnth => i.
case: (tnth_mergeP l) => Hl ->.
  rewrite tnth_mergeC => [|Hl2].
    rewrite mem_lensC.
    apply/negP => /lens_comp_sub; by rewrite mem_lensC Hl.
  by rewrite !tnth_extract !tnth_lens_index.
case: (tnth_mergeP l2) => Hl2 ->.
  have := Hl2; rewrite mem_lens_comp => Hl1; rewrite !tnth_merge.
  congr tnth; apply/val_inj; by rewrite /= -index_lens_comp.
have := Hl2; rewrite mem_lensC mem_lens_comp -mem_lensC => Hl1.
by rewrite !tnth_mergeC !tnth_extract !tnth_lens_index.
Qed.

Lemma merge_lensC_notin_l (vj : (m - p).-tuple I) (vk : (n - m).-tuple I) :
  merge lensC_notin_l vk (cast_tuple (esym cast_lensC_notin_l') vj) =
  merge lensC_in_l (extract (lens_perm lensC_in_l) vj)
                     (cast_tuple (esym cast_lensC_notin_l) vk).
Proof.
apply eq_from_tnth => i.
case: (tnth_mergeP lensC_in_l) => Hill ->.
  have Hinl : i \in lensC lensC_notin_l by rewrite !mem_lensC Hill.
  rewrite tnth_mergeC tnth_extract.
  have Hill' := Hill.
  rewrite -(lens_basis_perm lensC_in_l) in Hill'.
  have Hilb : i \in lens_basis lensC_in_l by apply/lens_comp_sub: Hill'.
  rewrite mem_lens_comp in Hill'.
  have -> : lens_index Hill = lens_index Hill'.
    apply (tnth_lens_inj (l:=lensC_in_l)).
    rewrite tnth_lens_index -{1}(lens_basis_perm lensC_in_l).
    by rewrite tnth_comp !tnth_lens_index.
  rewrite tnth_lens_index.
  pose i1 := tnth vj (lens_index Hill).
  by rewrite !(tnth_nth i1) /= [seq_basis _]lens_basis_lensC_in_l.
rewrite tnth_merge.
pose i1 := tnth vk (cast_ord cast_lensC_notin_l (lens_index Hill)).
by rewrite !(tnth_nth i1).
Qed.

Lemma merge_pair (i i' : 'I_n.+2) (vi vj : 1.-tuple I)
      (vk : (n.+2 - 1 - 1).-tuple I)
      (Hior : i \in lensC (lens_single i'))
      (Hir : i != i') :
  merge (lens_single i') vi (merge (lens_single (lens_index Hior)) vj vk) =
  merge (lens_pair Hir) [tuple of vj ++ vi] vk.
Proof.
have dI : I by case: vi => -[].
rewrite !(mergeE dI).
apply/eq_from_tnth => j.
rewrite !tnth_map !tnth_ord_tuple.
rewrite [index j (lens_single _)]/= [index j (lens_pair _)]/=.
case: ifP => rij.
  rewrite [X in nth _ vi X](_ : 0 = @ord0 1)%N //.
  rewrite ifF; last by rewrite -(negbTE Hir) -(eqP rij).
  case: vj => -[] // a [] //= sza.
  by rewrite -!(tnth_nth _ vi ord0).
rewrite nth_default; last by rewrite size_tuple.
have Hjl : j \in lensC (lens_single i').
  by rewrite mem_lensC mem_lensE inE eq_sym rij.
case: ifPn => ij.
  rewrite -(eqP ij) in Hjl *.
  rewrite make_lens_index -tnth_nth.
  have -> : lens_index Hjl = lens_index Hior by apply/val_inj.
  rewrite -mergeE tnth_merge_single.
  by case: vj => -[].
rewrite make_lens_index -tnth_nth !tnth_map !tnth_ord_tuple.
rewrite nth_lens_out; last first.
  rewrite mem_lensE inE.
  apply: contra ij => /eqP /(f_equal (tnth (lensC (lens_single i')))).
  by rewrite !tnth_lens_index => ->.
rewrite [RHS]nth_default ?size_tuple //.
congr nth.
rewrite -(index_lens_comp (lensC (lens_single (lens_index Hior))) Hjl).
congr index.
rewrite lens_comp_lensC.
apply eq_lensC => /= k.
by rewrite !mem_lensE !inE tnth_lens_index orbC.
Qed.

Lemma merge_perm (l1 : lens m m) (vi : m.-tuple I) vk :
  merge (lens_comp l l1) (extract l1 vi) vk = merge l vi vk.
Proof.
apply/eq_from_tnth => i.
case: (tnth_mergeP l) => Hil ->.
  rewrite tnth_merge => [|Hil1]. by rewrite mem_lens_comp mem_lens_full.
  rewrite tnth_extract.
  congr tnth; apply (tnth_lens_inj (l:=l)).
  by rewrite -tnth_comp !tnth_lens_index.
have Hic := Hil; rewrite -(lensC_comp_full _ l1) in Hic.
rewrite tnth_mergeC.
congr tnth; apply/val_inj => /=.
by move/(f_equal (val \o val)): (lensC_comp_full l l1) => /= ->.
Qed.
End lens_assoc.

Section lens_rev.
Variables (I : Type) (n : nat).

Lemma uniq_lens_rev : uniq [tuple rev_ord i | i < n].
Proof.
rewrite (map_uniq (f:=@rev_ord n)) // -map_comp (@eq_map _ _ _ id).
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

Lemma merge_rev m (l l' : lens m n)
      (vi vj : n.-tuple I) vk :
  l = rev l' :> seq _ -> vi = rev vj :> seq _ ->
  merge l vi vk = merge l' vj vk.
Proof.
move=> Hl Hv.
rewrite -(merge_perm l' lens_rev).
f_equal.
  apply/eq_lens_tnth => i /=.
  rewrite tnth_extract tnth_mktuple -[LHS]tnth_rev.
  by congr tnth; apply/val_inj; rewrite /= Hl revK.
apply/eq_from_tnth => i.
rewrite tnth_extract tnth_mktuple -[LHS]tnth_rev.
by congr tnth; apply/val_inj; rewrite /= Hv revK.
Qed.
End lens_rev.
