(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**
   lemmas.
   Some nice lemmas, mostly about le, lt, and mult.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Global Set Asymmetric Patterns.

From Stdlib Require Import ZArith.
From Stdlib Require Import EqNat.

Lemma predminus1 : forall n : nat, pred n = n - 1.
Proof.
   intro n. case n.
   simpl in |- *. reflexivity.
   simpl in |- *. intro m. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma le_mult_l : forall p q : nat, p <= q -> forall r : nat, r * p <= r * q.
Proof.
   intros p q H.
   simple induction r.
   simpl in |- *.
   apply le_n.
   intros r1 IHr1.
   simpl in |- *.
   apply Nat.add_le_mono.
   assumption.
   assumption.
Qed.

Lemma lt_plus_plus : forall n m p q : nat, n < m -> p < q -> n + p < m + q.
Proof.
   intros n m p q H H0.
   elim H; simpl in |- *; auto with arith.
Qed.

Lemma lt_mult_l :
 forall p q : nat, p < q -> forall r : nat, S r * p < S r * q.
Proof.
   intros p q H.
   simple induction r.
   simpl in |- *.
   rewrite <- plus_n_O.
   rewrite <- plus_n_O.
   assumption.
   intros r1 IHr1.
   simpl in |- *.
   apply lt_plus_plus.
   assumption.
   assumption.
Qed.

Lemma le_mult_r : forall p q : nat, p <= q -> forall r : nat, p * r <= q * r.
Proof.
   intros p q H.
   simple induction r.
   simpl in |- *.
   rewrite <- (mult_n_O p).
   rewrite <- (mult_n_O q).
   apply le_n.
   intros r1 IHr1.
   rewrite <- (mult_n_Sm p r1).
   rewrite <- (mult_n_Sm q r1).
   apply Nat.add_le_mono.
   assumption.
   assumption.
Qed.

Lemma sqrbound : forall p q : nat, p * p <= p * q \/ q * q <= p * q.
Proof.
   intros.
   elim (Nat.le_gt_cases p q).
   left.
   apply le_mult_l.
   assumption.
   right.
   apply le_mult_r.
   apply Nat.lt_le_incl.
   assumption.
Qed.

Lemma le_n_nm : forall n m : nat, n <= n * S m.
Proof.
   simple induction n.
   simpl in |- *.
   intros.
   apply le_n.
   intros n1 IHn1.
   simpl in |- *.
   intros.
   apply le_n_S.
   rewrite (Nat.add_comm m (n1 * S m)).
   eapply Nat.le_trans; [ | apply Nat.le_add_r ].
   apply IHn1.
Qed.

Lemma le_n_mn : forall n m : nat, n <= S m * n.
Proof.
   intros.
   rewrite (Nat.mul_comm (S m) n).
   apply le_n_nm.
Qed.

Lemma le_n_nn : forall n : nat, n <= n * n.
Proof.
   intro n. case n.
   simpl in |- *. apply le_n.
   simpl in |- *. intros. apply le_n_S. eapply Nat.le_trans; [ | apply Nat.le_add_r ]. apply le_n.
Qed.

Lemma lt_n_nm : forall n m : nat, 0 < n -> 1 < m -> n < n * m. 
Proof.
   intros n m.
   case n. intros. elim (Nat.nlt_0_r 0). assumption.
   intro n1. case m. intros. elim (Nat.nlt_0_r 1). assumption.
   intro m1. case m1. intros. elim (Nat.lt_irrefl 1). assumption.
   intro m2. elim n1.
   simpl in |- *. intros. apply -> Nat.succ_lt_mono. apply Nat.lt_0_succ.
   simpl in |- *. intros n2 IH. intros.
   apply -> Nat.succ_lt_mono.
   apply Nat.lt_trans with (S (S (m2 + n2 * S (S m2)))).
   apply IH.
   apply Nat.lt_0_succ.
   apply -> Nat.succ_lt_mono.
   apply Nat.lt_0_succ.
   apply -> Nat.succ_lt_mono.
   rewrite (Nat.add_comm m2).
   rewrite (Nat.add_comm m2).
   simpl in |- *.
   apply -> Nat.succ_lt_mono.
   apply Nat.lt_le_trans with (S (n2 * S (S m2) + m2)).
   apply Nat.lt_succ_diag_r.
   apply le_n_S.
   eapply Nat.le_trans; [ | apply Nat.le_add_r ].
   apply le_n.
Qed.

Lemma sqr_ascend : forall n : nat, n > 1 -> n < n * n.
Proof.
   simple induction n.
   intros.
   elim (Nat.nlt_0_r 1).
   assumption.
   intros m IHm.
   intro.
   unfold gt in H.
   unfold lt in H.
   elim (proj1 (Nat.lt_eq_cases 1 m)).
   intros.
   simpl in |- *.
   apply -> Nat.succ_lt_mono.
   rewrite <- (mult_n_Sm m m).
   rewrite Nat.add_comm.
   apply Nat.lt_lt_add_r.
   apply Nat.lt_lt_add_r.
   apply IHm.
   assumption.
   intros.
   rewrite <- H0.
   simpl in |- *.
   unfold lt in |- *.
   apply le_S.
   apply le_n.
   apply le_S_n.
   assumption.
Qed.

Lemma witness_le : forall x y : nat, (exists q : nat, x + q = y) -> x <= y.
Proof.
   intros. elim H. intro q. intros.
   rewrite <- H0.
   elim q.
   rewrite <- plus_n_O. apply le_n.
   intros. rewrite <- plus_n_Sm. apply le_S. assumption.
Qed.

Lemma le_witness : forall x y : nat, x <= y -> exists q : nat, x + q = y.
Proof.
   intros x y.
   intro.
   elim H.
   split with 0.
   simpl in |- *.
   symmetry  in |- *.
   apply plus_n_O.
   intros.
   case H1.
   intros.
   split with (S x0).
   replace (x + S x0) with (S (x + x0)).
   simpl in |- *.
   rewrite H2.
   reflexivity.
   apply plus_n_Sm.
Qed.

Lemma lt_witness :
 forall x y : nat, x < y -> exists q : nat, x + q = y /\ 0 < q.
Proof.
   unfold lt in |- *.
   intros.
   elim (le_witness (S x) y).
   intros.
   split with (S x0).
   split.
   rewrite <- plus_n_Sm.
   assumption.
   apply le_n_S.
   apply Nat.le_0_l.
   assumption.
Qed.


Lemma le_le_mult : forall b a c d : nat, a <= b -> c <= d -> a * c <= b * d.
Proof.
   simple induction b.
   intros.
   replace a with 0.
   simpl in |- *.
   apply le_n.
   symmetry  in |- *.
   apply -> Nat.le_0_r.
   assumption.
   intros b1 IHb1.
   simpl in |- *.
   intros.
   elim (proj1 (Nat.lt_eq_cases a (S b1))).
   unfold lt in |- *.
   intros.
   rewrite (Nat.add_comm d (b1 * d)).
   eapply Nat.le_trans; [ | apply Nat.le_add_r ].
   apply IHb1.
   apply le_S_n.
   assumption.
   assumption.
   intro.
   rewrite H1.
   replace (d + b1 * d) with (S b1 * d).
   apply le_mult_l.
   assumption.
   reflexivity.
   assumption.
Qed.

Lemma lt_lt_mult : forall a b c d : nat, a < b -> c < d -> a * c < b * d.
Proof.
   unfold lt in |- *.
   intros.
   apply Nat.le_trans with (S a * S c).
   simpl in |- *.
   apply le_n_S.
   rewrite <- (mult_n_Sm a c).
   rewrite (Nat.add_comm c (a * c + a)).
   eapply Nat.le_trans; [ | apply Nat.le_add_r ].
   eapply Nat.le_trans; [ | apply Nat.le_add_r ].
   apply le_n.
   apply le_le_mult.
   assumption.
   assumption.
Qed.

Lemma lt_n_nm_m_gt_1 : forall a b : nat, a < a * b -> b > 1.
Proof.
   intros a b. case b.
   rewrite <- (mult_n_O a). intro. elim (Nat.nlt_0_r a). assumption.
   intro b1. case b1.
   rewrite <- (mult_n_Sm a 0).
   rewrite <- (mult_n_O a). simpl in |- *. intro.
   elim (Nat.lt_irrefl a). assumption.
   intros. apply -> Nat.succ_lt_mono. apply Nat.lt_0_succ.
Qed.

Lemma n0n1_or_gt : forall n : nat, n = 0 \/ n = 1 \/ n > 1.
Proof.
   intro n. case n.
   left. reflexivity.
   intro n1. case n1.
   right. left. reflexivity.
   intro n2.
   right. right. apply -> Nat.succ_lt_mono. apply Nat.lt_0_succ.
Qed.

Lemma lt_multpred_pp : forall p : nat, p > 1 -> pred p * pred p < p * p.
Proof.
   intro.
   case p.
   intro.
   elim (Nat.nlt_0_r 1).
   assumption.
   intro p1.
   case p1.
   intro.
   elim (Nat.lt_irrefl 1).
   assumption.
   intro p2.
   intros.
   apply lt_lt_mult.
   simpl in |- *. apply Nat.lt_succ_diag_r.
   simpl in |- *. apply Nat.lt_succ_diag_r.
Qed.

Lemma le_diff0 : forall b a c : nat, a <= b -> a = b + c -> c = 0.
Proof.
   simple induction b.
   simpl in |- *. intro.
   case a.
   intros.
   rewrite H0.
   reflexivity.
   intros.
   elim (Nat.nlt_0_r n).
   assumption.
   intros b1 IH.
   simpl in |- *.
   intros.
   rewrite H0 in H.
   apply (IH (b1 + c) c).
   apply le_S_n.
   assumption.
   reflexivity.
Qed.

Lemma simpl_lt_mult_l : forall a b c : nat, a * b < a * c -> b < c.
Proof.
   simple induction a.
   simpl in |- *.
   intros.
   elim (Nat.lt_irrefl 0).
   assumption.
   intros a1 IH.
   intros.
   elim (Nat.le_gt_cases b c).
   intro.
   elim (proj1 (Nat.lt_eq_cases b c)).
   intro.
   assumption.
   intros.
   rewrite H1 in H.
   elim (Nat.lt_irrefl (S a1 * c)).
   assumption.
   assumption.
   intros.
   cut (S a1 * c <= S a1 * b).
   intros.
   elim (proj1 (Nat.le_ngt (S a1 * c) (S a1 * b))).
   assumption.
   assumption.
   apply Nat.lt_le_incl.
   apply lt_mult_l.
   assumption.
Qed.

Lemma simpl_le_mult_l : forall a b c : nat, 0 < a -> a * b <= a * c -> b <= c.
Proof.
   simple induction a.
   intros.
   elim (Nat.nlt_0_r 0).
   assumption.
   intros a1 IH.
   intros.
   simpl in H0.
   elim (Nat.le_gt_cases b c).
   intro.
   assumption.
   intro.
   elim (proj1 (Nat.lt_nge (S a1 * c) (S a1 * b))).
   apply lt_mult_l.
   assumption.
   assumption.
Qed.

Lemma simpl_eq_mult_l : forall a b c : nat, 0 < a -> a * b = a * c -> b = c.
Proof.
   intros. apply Nat.le_antisymm.
   apply simpl_le_mult_l with a. assumption. rewrite H0. apply le_n.
   apply simpl_le_mult_l with a. assumption. rewrite H0. apply le_n.
Qed.

Lemma mult_ppq_p0q1 : forall p q : nat, p = p * q -> p = 0 \/ q = 1.
Proof.
   intro p. case p. left. reflexivity.
   intro p1. right.
   apply simpl_eq_mult_l with (S p1). apply Nat.lt_0_succ.
   rewrite <- H.
   rewrite <- mult_n_Sm. rewrite <- mult_n_O.
   simpl in |- *. reflexivity.
Qed.

Lemma mult_pq1_p1q1 : forall p q : nat, p * q = 1 -> p = 1 /\ q = 1.
Proof.
   intro p. case p. simpl in |- *. intros. discriminate H.
   intro p1. case p1. simpl in |- *.
   intro q. rewrite <- plus_n_O. split. reflexivity. assumption.
   intro p2.
   intro q. case q. rewrite <- mult_n_O. intro. discriminate H.
   intro q1. case q1.
   rewrite <- mult_n_Sm.
   rewrite <- mult_n_O.
   simpl in |- *. intro. discriminate H.
   intro q2. simpl in |- *. intro. discriminate H.
Qed.

Lemma Zmult_ab0a0b0 : forall a b : Z, (a * b)%Z = 0%Z -> a = 0%Z \/ b = 0%Z.
Proof.
   simple induction a.
   simpl in |- *. left. reflexivity.
   intro p. simple induction b.
   simpl in |- *. right. reflexivity.
   simpl in |- *. intros. discriminate H.
   simpl in |- *. intros. discriminate H.
   intro. simple induction b.
   simpl in |- *. right. reflexivity.
   simpl in |- *. intros. discriminate H.
   simpl in |- *. intros. discriminate H.
Qed.

Lemma Zle_minus : forall a b : Z, (b <= a)%Z -> (0 <= a - b)%Z.
Proof.
   intros a b. intros.
   apply Zplus_le_reg_l with b.
   unfold Zminus in |- *. rewrite (Zplus_comm a).
   rewrite (Zplus_assoc b (- b)). rewrite Zplus_opp_r.
   simpl in |- *. rewrite <- Zplus_0_r_reverse. assumption.
Qed.

Lemma Zopp_lt_gt_0 : forall x : Z, (x < 0)%Z -> (- x > 0)%Z.
Proof.
   simple induction x.
   intro. unfold Z.lt in H. simpl in H. discriminate H.
   intros. unfold Z.lt in H. simpl in H. discriminate H.
   intros. simpl in |- *. unfold Z.gt in |- *. simpl in |- *. reflexivity.
Qed.

Lemma Zlt_neq : forall x y : Z, (x < y)%Z -> x <> y.
Proof.
   intros. intro.
   rewrite H0 in H.
   elim (Z.lt_irrefl y).
   assumption.
Qed.

Lemma Zgt_neq : forall x y : Z, (x > y)%Z -> x <> y.
Proof.
   intros. intro.
   rewrite H0 in H.
   elim (Z.lt_irrefl y).
   apply Z.gt_lt. assumption.
Qed.

Lemma S_inj : forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H; injection H; trivial.
Qed.

Lemma Zlt_mult_l :
 forall p q r : Z, (0 < r)%Z -> (p < q)%Z -> (r * p < r * q)%Z.
Proof.
   simple induction r.
   intros. elim (Z.lt_irrefl 0). assumption.
   intros. unfold Z.lt in |- *.
   rewrite (Zcompare_mult_compat p0 p q).
   assumption.
   intros. unfold Z.lt in H. simpl in H. discriminate H.
Qed.

Lemma Zle_mult_l :
 forall p q r : Z, (0 < r)%Z -> (p <= q)%Z -> (r * p <= r * q)%Z.
Proof.
   simple induction r.
   intros. simpl in |- *. apply Zeq_le. reflexivity.
   intros. unfold Z.le in |- *.
   rewrite (Zcompare_mult_compat p0 p q).
   assumption.
   intros. unfold Z.lt in H. simpl in H. discriminate H.
Qed.
