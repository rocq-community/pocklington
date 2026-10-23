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
   natZ.
   Some lemmas about inject_nat, absolu and the relation between
   Z and nat in general.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import EqNat.

Require Import lemmas.

Lemma abs_opp : forall x : Z, Z.abs_nat x = Z.abs_nat (- x).
Proof.
   simple induction x.
   simpl in |- *. reflexivity.
   simpl in |- *. reflexivity.
   simpl in |- *. reflexivity.
Qed.

Lemma inj_abs_pos : forall x : Z, (x >= 0)%Z -> Z_of_nat (Z.abs_nat x) = x.
Proof.
   simple induction x.
   reflexivity.
   intros. simpl in |- *.
   induction  p as [p Hrecp| p Hrecp| ].
   rewrite BinInt.Zpos_xI.
   rewrite <- Hrecp.
   replace (nat_of_P (xI p)) with (S (2 * nat_of_P p)).
   rewrite Znat.inj_S.
   rewrite Znat.inj_mult.
   rewrite Hrecp.
   simpl in |- *.
   reflexivity.
   apply Z.le_ge. apply Zorder.Zle_0_pos.
   replace 2 with (nat_of_P 2).
   rewrite <- nat_of_P_mult_morphism.
   simpl in |- *.
   rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
   rewrite P_of_succ_nat_o_nat_of_P_eq_succ.
   simpl in |- *.
   reflexivity.
   simpl in |- *.
   reflexivity.
   apply Z.le_ge. apply Zorder.Zle_0_pos.
   rewrite BinInt.Zpos_xO.
   rewrite <- Hrecp.
   replace (nat_of_P (xO p)) with (2 * nat_of_P p).
   rewrite Znat.inj_mult.
   rewrite Hrecp.
   simpl in |- *.
   reflexivity.
   apply Z.le_ge. apply Zorder.Zle_0_pos.
   replace 2 with (nat_of_P 2).
   rewrite <- nat_of_P_mult_morphism.
   simpl in |- *.
   reflexivity.
   simpl in |- *.
   reflexivity.
   apply Z.le_ge.
   apply Zorder.Zle_0_pos.
   reflexivity.
   intros.
   elim H.
   simpl in |- *.
   reflexivity.
Qed.

Lemma inj_abs_neg :
 forall x : Z, (x < 0)%Z -> Z_of_nat (Z.abs_nat x) = (- x)%Z.
Proof.
   intros.
   rewrite abs_opp.
   apply inj_abs_pos.
   apply Z.le_ge.
   apply Zplus_le_reg_l with x.
   rewrite <- Zplus_0_r_reverse.
   rewrite Zplus_opp_r.
   apply Zlt_le_weak.
   assumption.
Qed.

Lemma abs_inj : forall n : nat, Z.abs_nat (Z_of_nat n) = n.
Proof.
   simple induction n.
   simpl in |- *. reflexivity.
   intros m IH.
   rewrite <- IH. simpl in |- *.
   rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
   reflexivity.
Qed.

Lemma abs_mult : forall x y : Z, Z.abs_nat (x * y) = Z.abs_nat x * Z.abs_nat y.
Proof.
   simple induction x.
   simpl in |- *. intro. reflexivity.
   intro.
   simple induction y.
   simpl in |- *.
   rewrite <- mult_n_O.
   reflexivity.
   intro.
   simpl in |- *.
   rewrite <- nat_of_P_mult_morphism.
   reflexivity.
   simpl in |- *.
   intro.
   rewrite <- nat_of_P_mult_morphism.
   reflexivity.
   intro.
   simple induction y.
   simpl in |- *.
   rewrite <- mult_n_O.
   reflexivity.
   intro.
   unfold Z.abs_nat in |- *.
   simpl in |- *.
   rewrite <- nat_of_P_mult_morphism.
   reflexivity.
   intro.
   unfold Z.abs_nat in |- *.
   simpl in |- *.
   rewrite <- nat_of_P_mult_morphism.
   reflexivity.
Qed.

Lemma isnat_inj_abs :
 forall (x : Z) (n : nat), x = Z_of_nat n -> n = Z.abs_nat x.
Proof.
   intros.
   rewrite H.
   rewrite abs_inj.
   reflexivity.
Qed.

Lemma isnat_abs_inj :
 forall (x : Z) (n : nat), (0 <= x)%Z -> n = Z.abs_nat x -> x = Z_of_nat n.
Proof.
   intros.
   rewrite H0.
   rewrite inj_abs_pos.
   reflexivity.
   apply Z.le_ge.
   assumption.
Qed.

Lemma isnat_plus : forall x y : Z, (0 <= x)%Z -> (0 <= y)%Z -> (0 <= x + y)%Z.
Proof.
   simple induction x. simpl in |- *. intros. assumption.
   intro. simple induction y. simpl in |- *. intros. assumption.
   simpl in |- *. intros. unfold Z.le in |- *. simpl in |- *. discriminate.
   intros. unfold Z.le in H0. elim H0. simpl in |- *. reflexivity.
   intros. unfold Z.le in H. elim H. simpl in |- *. reflexivity.
Qed.

Lemma isnat_mult : forall x y : Z, (0 <= x)%Z -> (0 <= y)%Z -> (0 <= x * y)%Z.
Proof.
   simple induction x.
   simpl in |- *. intros. unfold Z.le in |- *. simpl in |- *. discriminate.
   intro. simple induction y. simpl in |- *. intros. unfold Z.le in |- *. simpl in |- *. discriminate.
   simpl in |- *. intros. unfold Z.le in |- *. simpl in |- *. discriminate.
   intros. unfold Z.le in H0. elim H0. simpl in |- *. reflexivity.
   intros. unfold Z.le in H. elim H. simpl in |- *. reflexivity.
Qed.


Lemma lezle :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> (x <= y)%Z -> Z.abs_nat x <= Z.abs_nat y.
Proof.
   intros.
   elim (Nat.le_gt_cases (Z.abs_nat x) (Z.abs_nat y)).
   intros. assumption.
   intros. elim (Zlt_not_le y x).
   rewrite <- (inj_abs_pos x).
   rewrite <- (inj_abs_pos y).
   apply Znat.inj_lt. assumption.
   apply Z.le_ge. assumption.
   apply Z.le_ge. assumption.
   assumption.
Qed.

Lemma gtzgt :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> (x > y)%Z -> Z.abs_nat x > Z.abs_nat y.
Proof.
   intros.
   elim (Nat.le_gt_cases (Z.abs_nat x) (Z.abs_nat y)).
   intros.
   elim (Zle_not_lt x y).
   rewrite <- (inj_abs_pos x).
   rewrite <- (inj_abs_pos y).
   apply Znat.inj_le. assumption.
   apply Z.le_ge. assumption.
   apply Z.le_ge. assumption.
   apply Z.gt_lt. assumption.
   unfold gt in |- *. intro. assumption.
Qed.

Lemma ltzlt :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> (x < y)%Z -> Z.abs_nat x < Z.abs_nat y.
Proof.
   intros.
   change (Z.abs_nat y > Z.abs_nat x) in |- *.
   apply gtzgt. assumption. assumption.
   apply Z.lt_gt. assumption.
Qed.

Lemma abs_plus_pos :
 forall x y : Z,
 (0 <= x)%Z -> (0 <= y)%Z -> Z.abs_nat (x + y) = Z.abs_nat x + Z.abs_nat y.
Proof.
   simple induction x.
   simpl in |- *.
   intros.
   reflexivity.
   intro.
   simple induction y.
   simpl in |- *.
   rewrite <- plus_n_O.
   intros.
   reflexivity.
   simpl in |- *.
   intros.
   apply nat_of_P_plus_morphism.
   intros.
   unfold Z.le in H0.
   simpl in H0.
   elim H0.
   reflexivity.
   intros.
   unfold Z.le in H.
   simpl in H.
   elim H.
   reflexivity.
Qed.

Lemma abs_minus_pos :
 forall x y : Z,
 (0 <= x)%Z ->
 (0 <= y)%Z -> (x >= y)%Z -> Z.abs_nat (x - y) = Z.abs_nat x - Z.abs_nat y.
Proof.
   intros.
   elim (Z_of_nat_complete x).
   intros nx Hx.
   elim (Z_of_nat_complete y).
   intros ny Hy.
   elim (Z_of_nat_complete (x - y)).
   intros d Hd.
   rewrite Hx.
   rewrite Hy.
   rewrite <- Znat.inj_minus1.
   rewrite abs_inj.
   rewrite abs_inj.
   rewrite abs_inj.
   reflexivity.
   rewrite (isnat_inj_abs x nx).
   rewrite (isnat_inj_abs y ny).
   apply lezle.
   assumption.
   assumption.
   apply Z.ge_le.
   assumption.
   assumption.
   assumption.
   unfold Zminus in |- *.
   apply Zle_left.
   apply Z.ge_le.
   assumption.
   assumption.
   assumption.
Qed.

Lemma abs_pred_pos :
 forall x : Z, (0 < x)%Z -> pred (Z.abs_nat x) = Z.abs_nat (x - 1).
Proof.
   intros.
   rewrite abs_minus_pos.
   replace (Z.abs_nat 1) with 1.
   rewrite predminus1.
   reflexivity.
   reflexivity.
   apply Zlt_le_weak.
   assumption.
   unfold Z.le in |- *.
   simpl in |- *.
   discriminate.
   apply Z.le_ge.
   change (Z.succ 0 <= x)%Z in |- *.
   apply Zlt_le_succ.
   assumption.
Qed.

Lemma abs_neq_lt : forall x : Z, x <> 0%Z -> 0 < Z.abs_nat x.
Proof.
   simple induction x.
   intro. elim H. reflexivity.
   intros. change (Z.abs_nat 0 < Z.abs_nat (Zpos p)) in |- *. apply ltzlt.
   unfold Z.le in |- *. simpl in |- *. discriminate.
   unfold Z.le in |- *. simpl in |- *. discriminate.
   unfold Z.lt in |- *. simpl in |- *. reflexivity.
   intros. change (Z.abs_nat 0 < Z.abs_nat (Zpos p)) in |- *. apply ltzlt.
   unfold Z.le in |- *. simpl in |- *. discriminate.
   unfold Z.le in |- *. simpl in |- *. discriminate.
   unfold Z.lt in |- *. simpl in |- *. reflexivity.
Qed.

Lemma nat_ge_0 : forall n : nat, (Z_of_nat n >= 0)%Z.
Proof.
   simple induction n.
   simpl in |- *. unfold Z.ge in |- *. simpl in |- *. discriminate.
   intros m IHm.
   change (Z_of_nat (S m) >= Z_of_nat 0)%Z in |- *.
   apply Znat.inj_ge. unfold ge in |- *.
   apply Nat.le_0_l.
Qed.
