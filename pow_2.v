(*** Function: next_pow_2
     Spec: next_pow_2_spec *)

Require Import Coq.Init.Nat.
Require Import PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Omega.

Definition is_power_of_2 (n : nat) : Prop := exists m, 2^m = n.

Definition is_power_of_2b (n : nat) := n =? 2 ^ log2 n.

Lemma is_power_of_2b_spec (n : nat)
  : Bool.reflect (is_power_of_2 n) (is_power_of_2b n).
Proof.
  destruct (is_power_of_2b n) eqn:H; constructor.
  - unfold is_power_of_2b in H; apply beq_nat_true in H.
    exists (log2 n); auto.
  - apply beq_nat_false in H.
    intro Contra; apply H.
    destruct Contra as [m Contra].
    subst; rewrite Nat.log2_pow2; omega.
Qed.

(** The function *)
Definition next_pow_2 (n : nat) :=
  if n =? 0 then 1 else if is_power_of_2b n then n else 2 ^ S (log2 n).

Lemma not_pow_2_le_lt (n m : nat) : ~ is_power_of_2 n -> n <= 2^m -> n < 2^m.
Proof.
  intros H0 H1; unfold is_power_of_2 in H0.
  assert (forall k, 2 ^ k <> n).
  { intros k HC. apply H0. exists k; auto. }
  specialize (H m);  omega.
Qed.

Lemma pow_2_lt_le (a b : nat) : 2^a < 2^b -> 2*2^a <= 2^b.
Proof.
  intro H.
  assert (H0: 2 * 2^a = 2 ^ (S a)). auto.
  rewrite H0. clear H0.
  assert (a < b).
  { rewrite Nat.pow_lt_mono_r_iff; eauto. }
  unfold lt in H0.
  apply Nat.pow_le_mono_r; auto.
Qed.


(** Specification and proof. *)
Lemma next_pow_2_spec (n : nat) :
  is_power_of_2 (next_pow_2 n) /\
  n <= next_pow_2 n /\
  forall m, n <= 2^m -> next_pow_2 n <= 2^m.
Proof.
  split.
  - unfold next_pow_2. destruct n; simpl.
    + exists 0; auto.
    + destruct (is_power_of_2b_spec (S n)); auto.
      rewrite Nat.add_0_r.
      exists (S (log2 (S n))); simpl; auto.
  - split.
    + unfold next_pow_2.
      destruct n; simpl; auto.
      destruct (is_power_of_2b_spec (S n)); auto.
      generalize (Nat.log2_spec (S n) (Nat.lt_0_succ n)). intros [_ H0].
      simpl in H0; omega.
    + intros m Hm; unfold next_pow_2.
      destruct n; simpl.
      * clear Hm; induction m; auto; simpl; omega.
      * destruct (is_power_of_2b_spec (S n)); auto.
        generalize (Nat.log2_spec (S n) (Nat.lt_0_succ n)). intros [H0 H1].
        rewrite Nat.add_0_r.
        apply not_pow_2_le_lt with (m:=m) in n0; auto.
        assert (H2: 2 ^ log2 (S n) < 2^m). omega.
        apply pow_2_lt_le in H2; omega.
Qed.


(** Test it out. *)
Eval compute in (next_pow_2 65).
