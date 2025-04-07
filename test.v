From Stdlib Require Import List Nat.
Import ListNotations.

(* Eval step_eval in 1 + 1. *)

Fixpoint aiota (n: nat) :=
  match n with
  | 0 => [0]
  | S k => aiota k ++ [n]
  end.

Fixpoint riota_aux (n k: nat) :=
  match n with
  | 0 => [k]
  | S n => k :: riota_aux n (S k)
  end.

Definition riota (n: nat) := riota_aux n 0.

Lemma aiota_length n: length (aiota n) = S n.
Proof.
  induction n as [| ? IH]; [reflexivity |].
  simpl; rewrite length_app, IH, PeanoNat.Nat.add_1_r; reflexivity.
Qed.

Lemma aiota_nth n k: nth k (aiota n) k = k.
Proof.
  case (PeanoNat.Nat.le_decidable (length (aiota n)) k);
    [now apply nth_overflow |].
  rewrite PeanoNat.Nat.nle_gt; induction n as [| ? IH];
    [rewrite PeanoNat.Nat.lt_1_r; intros ->; reflexivity |].
  simpl; rewrite length_app; simpl.
  rewrite PeanoNat.Nat.add_1_r, PeanoNat.Nat.lt_succ_r, PeanoNat.Nat.lt_eq_cases.
  intros [Hlt | ->].
  - rewrite (app_nth1 _ _ _ Hlt); exact (IH Hlt).
  - rewrite nth_middle, aiota_length; reflexivity.
Qed.

Lemma riota_aux_length n: forall k, length (riota_aux n k) = S n.
Proof. now induction n as [| n IH]; [| simpl; intro k; rewrite IH]. Qed.

Lemma riota_length n: length (riota n) = S n.
Proof. now apply riota_aux_length. Qed.

Lemma riota_aux_nth k n a: nth k (riota_aux n a) (k + a) = k + a.
Proof.
  case (PeanoNat.Nat.le_decidable (S n) k);
    [now intros ?; apply nth_overflow; rewrite riota_aux_length |].
  rewrite PeanoNat.Nat.nle_gt; revert k a; induction n as [| ? IH]; intros k a;
    [rewrite PeanoNat.Nat.lt_1_r; intros ->; reflexivity |].
  case k as [| k]; [reflexivity |].
  now rewrite <-PeanoNat.Nat.succ_lt_mono, PeanoNat.Nat.add_succ_comm; apply IH.
Qed.

Lemma riota_nth k n: nth k (riota n) k = k.
Proof. now rewrite <-(PeanoNat.Nat.add_0_r k) at 2 3; apply riota_aux_nth. Qed.

Theorem same_iota n: aiota n = riota n.
Proof.
  assert (length (aiota n) = length (riota n)) as Hlen
    by now rewrite aiota_length, riota_length.
  apply (nth_ext _ _ n n Hlen).
  intros k Hlt; rewrite (nth_indep _ _ k Hlt).
  rewrite Hlen in Hlt; rewrite (nth_indep _ _ k Hlt), aiota_nth, riota_nth.
  reflexivity.
Qed.

Example motivation_test n: riota (4 + n) = riota 26 -> riota (8 + n) = riota 30.
Proof.
  intro H. cbv.
Abort.

Example perf_test n: riota (10000 + n) = riota 9999 ++ riota_aux n 10000.
Proof. reflexivity. Qed.


