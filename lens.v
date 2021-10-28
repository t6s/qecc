From mathcomp Require Import all_ssreflect.

Section lens.
Variables (T : Type) (n m : nat).

Definition lens := {s : m.-tuple 'I_n | uniq s}.

Variables (l : lens) (f : m.-tuple T -> m.-tuple T).

Definition extract (t : n.-tuple T) := [tuple tnth t (tnth (val l) i) | i < m].

Definition focus (t : n.-tuple T) :=
  let t' := f (extract t) in
  [tuple nth (tnth t i) t' (index i (val l)) | i < n].

Lemma focus_out t i : i \notin (val l) -> tnth (focus t) i = tnth t i.
Proof.
move=> Hi.
by rewrite tnth_mktuple nth_default // memNindex // !size_tuple.
Qed.

Lemma focus_in t : extract (focus t) = f (extract t).
Proof.
apply eq_from_tnth => i.
rewrite !tnth_mktuple [RHS](tnth_nth (tnth t (tnth (val l) i))).
case: l => /= s Hu.
by rewrite index_uniq // size_tuple.
Qed.
End lens.
