From mathcomp Require Import all_ssreflect all_algebra complex.
Require Import qexamples_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Let succ_neq n (i : 'I_n) : widen_ord (leqnSn n) i != lift ord0 i.
Proof. by rewrite neq_ltn /= /bump leq0n ltnSn. Qed.

(* Specification *)
Definition ghz_state n : dpower n.+1 Co :=
  (1 / Num.sqrt 2)%:C *:
  (dpbasis C [tuple 0 | i < n.+1] + dpbasis C [tuple 1 | i < n.+1]).

(* Recursive definition *)
(* Uses a recursive embedding through dependent pattern-matching *)
Fixpoint ghz n :=
  match n as n return endo n.+1 with
  | 0 => tsmor hadamard
  | i.+1 =>
      tsapp (lens_pair (succ_neq ord_max)) cnot
      \v focus (lothers (lens_single ord_max)) (ghz i)
  end.

(* Alternative flat definition, using iterated composition *)
Definition ghz' n : endo n.+1 :=
  compn_mor (fun i : 'I_n => tsapp (lens_pair (succ_neq (rev_ord i))) cnot)
            xpredT
  \v tsapp [lens 0] hadamard.

(* Proof of correctness *)
Lemma ghz_def n : ghz' n =e ghz n.
Proof.
rewrite /ghz' /compn_mor.
elim: n => [|n IH] /=.
  rewrite big_pred0; last by move=> i; rewrite -(ltn_ord i) ltn0.
  rewrite comp_mor1f (_ : [lens 0] = lens_id 1); last by eq_lens.
  exact: focusI.
rewrite big_ord_recl.
move=> T v /=.
f_equal.
  do 3 f_equal; eq_lens; by rewrite subn1.
rewrite (focusE _ _ (ghz n)) /focus_fun -IH.
set f := \big[_/_]_(i < n) _ \v _.
rewrite -/(focus_fun dI (lothers (lens_single (@ord_max n.+1))) f v).
rewrite -focusE /f focus_comp /= -focusM.
rewrite (_ : lens_comp _ _ = [lens 0]);
  last by eq_lens; rewrite /= enum_ordinalE.
rewrite focus_compn_mor.
do 3 f_equal.
apply eq_bigr => i _; apply/morP => {}T {}v.
rewrite -focusM.
rewrite (_ : lens_comp _ _ = lens_pair (succ_neq (rev_ord (lift 0 i)))) //.
apply eq_lens_tnth => j.
rewrite tnth_comp tnth_lothers_single.
apply val_inj.
rewrite [LHS]lift_max !(tnth_nth 0) /=.
by case: j => -[|[]].
Qed.

Lemma bump0n n : bump 0 n = n.+1.
Proof. by rewrite /bump leq0n. Qed.

Lemma ghz_state0 : ghz_state 0 = tsmor hadamard Co (dpbasis C [tuple 0| _ < 1]).
Proof.
apply/ffunP => /= vi.
rewrite tsmorE !ffunE /= sum_enum_indices /=.
have := mem_enum_indices vi; rewrite !inE => /orP[] /eqP -> /=;
rewrite !ffunE !eq_ord_tuple /= enum_ordinalE /= !linE ![_ *: 1]mulr1;
by rewrite ![_ *: 0]mulr0 !linE.
Qed.

Lemma ghz_ok n : ghz n Co (dpbasis C [tuple 0 | i < n.+1]) = ghz_state n.
Proof.
elim: n => [| n IH] /=. by rewrite ghz_state0.
rewrite focus_dpbasis.
have Hex : extract (lothers (lens_single ord_max)) [tuple (0:I)  | _ < n.+2]
           = [tuple 0 | _ < n.+1].
  apply eq_from_tnth => i; by rewrite tnth_extract !tnth_map.
rewrite Hex {}IH /ghz_state !linearZ_LR /=.
congr (_ *: _); rewrite !linearE /=.
congr (_ + _); rewrite dpmerge_dpbasis.
  rewrite -Hex merge_extract focus_dpbasis.
  have Hex': extract (lens_pair (succ_neq ord_max)) [tuple (0:I) | _ < n.+2]
             = [tuple 0; 0].
    apply eq_from_tnth => i; rewrite tnth_extract !tnth_map.
    by case: i => -[|[]].
  by rewrite Hex' tsmor_cnot0 dpmerge_dpbasis -Hex' merge_extract.
rewrite (_ : extract _ _ = [tuple (0:I) | _ < _]); last first.
  apply eq_from_tnth => i; by rewrite tnth_extract !tnth_map.
rewrite (_ : merge _ _ _ _ =
             [tuple if (i < n.+1)%N then 1 else 0 | i < n.+2]); last first.
  apply eq_from_tnth => i; rewrite [RHS]tnth_map tnth_ord_tuple.
  case/boolP: (i == ord_max) => Hi.
  - have Hi' : i \in lothers (lothers (lens_single ord_max)).
      by rewrite !mem_lothers inE Hi.
    by rewrite tnth_merge_lothers tnth_map (eqP Hi) ltnn.
  - have Hi' : i \in lothers (lens_single ord_max).
      by rewrite mem_lothers inE Hi.
    by rewrite tnth_merge tnth_map ltn_neqAle Hi -ltnS ltn_ord.
rewrite focus_dpbasis.
rewrite (_ : extract _ _ = [tuple 1; 0]); last first.
  apply eq_from_tnth => i; rewrite !tnth_map tnth_ord_tuple.
  by case: i => -[|[]] //= Hi; rewrite !(tnth_nth 0) ?ltnSn // bump0n ltnn.
rewrite tsmor_cnot1 dpmerge_dpbasis.
rewrite (_ : merge _ _ _ _ = [tuple 1 | i < n.+2]) //.
apply eq_from_tnth => i; rewrite [RHS]tnth_map.
case/boolP: (i \in lens_pair (succ_neq ord_max)) => Hi.
- rewrite tnth_merge.
  case: (lens_index Hi) => -[|[]] // Hi'.
  rewrite (tnth_nth 0) //=; by apply val_inj.
- rewrite -mem_lothers in Hi.
  rewrite tnth_merge_lothers !tnth_map tnth_ord_tuple ifT //.
  rewrite ltn_neqAle -ltnS ltn_ord andbT.
  set lop := lothers _; have := mem_tnth (lens_index Hi) lop.
  rewrite mem_lothers !inE negb_or => /andP[_].
  apply contra => /eqP Hj.
  by apply/eqP/val_inj => /=; rewrite bump0n.
Qed.
