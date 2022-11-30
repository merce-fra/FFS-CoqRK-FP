(**

Copyright (C) Faissole

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)
Require Import Reals Lra.

From mathcomp
     Require Import all_ssreflect ssralg matrix zmodp.

Require Import Rstruct Compl.

Import GRing.Theory.

Open Scope R_scope.

Definition matrix_norm {m n} : 'M[R]_(m,n) -> R :=
  fun A => \big[Rmax/0]_(i < m) (\sum_(j < n) (Rabs (A i j))).

Notation "||| A |||" := (matrix_norm A) (at level 23).

Notation "O_( m , n )" := (@const_mx _ m n 0) (at level 20).

Lemma matrix_norm_pos : forall {m n} (A : 'M[R]_(m,n)), 0 <= ||| A |||.
Proof.
  intros; apply big_Rmax_pos => //. 
Qed.

Lemma matrix_norm_def : forall {m n}, ||| O_(m,n) ||| = 0.
Proof.
  intros m n; unfold matrix_norm.
  cut (forall i j, Rabs ((O_( m, n)) i j) = 0); intros Hu.
  under eq_bigr => i do (under eq_bigr => j do (rewrite Hu)); rewrite big_Rplus_0. 
  now rewrite big_Rmax_0.
  intros; now rewrite !mxE Rabs_R0.
Qed.

Lemma matrix_norm_scal_r : forall {m n} (a : R) (A : 'M[R]_(m,n)),
    ||| map_mx (fun x => x*a) A ||| = Rabs a * ||| A |||.
Proof.
  intros m n a A; unfold matrix_norm.
  rewrite <- big_Rmax_scal; try apply Rabs_pos.
  symmetry; under eq_bigr => i do rewrite big_Rplus_scal_fun2.
  under eq_bigr => i do under eq_bigr => j do rewrite <- Rabs_mult, Rmult_comm.
  apply eq_bigr; intros; apply eq_bigr; intros; now rewrite !mxE.
Qed.

Lemma matrix_norm_scal_l : forall {m n} (a : R) (A : 'M[R]_(m,n)),
    ||| map_mx (fun x => a*x) A ||| = Rabs a * ||| A |||.
Proof.
  intros m n a A; unfold matrix_norm.
  rewrite <- big_Rmax_scal; try apply Rabs_pos.
  symmetry; under eq_bigr => i do rewrite big_Rplus_scal_fun2.
  under eq_bigr => i do under eq_bigr => j do rewrite <- Rabs_mult.
  apply eq_bigr; intros; apply eq_bigr; intros; now rewrite !mxE. 
Qed.

Lemma matrix_norm_triang :
  forall {m n} (A B : 'M[R]_(m,n)), ||| A + B ||| <= ||| A ||| + ||| B |||.
Proof.
  intros m n A B; unfold matrix_norm.
  eapply Rle_trans.
  apply big_Rmax_le.
  intros i; apply big_add_mat_le.
  apply big_Rmax_add_le.
Qed.

Lemma Rabs_sum_prod : forall n f g,
    Rabs (\sum_(i < n) ((f i) * (g i))) <= \sum_(i < n) (Rabs (f i) * Rabs (g i)).
Proof.
  intros n f g.
  apply Rge_le; under eq_bigr => i do (rewrite <- Rabs_mult). 
  apply Rle_ge; apply big_triang_le.
Qed.

(** Submultiplicativity of matrix/vector norms *) 
Lemma norm_submult : forall {m n p} (A : 'M[R]_(m,n)) (B : 'M[R]_(n,p)), 
                  (||| A *m B ||| <= ||| A ||| * ||| B |||)%Re.
Proof.
  intros m n p A B.
  unfold matrix_norm at 1, mulmx; simpl.
  under eq_bigr => i do under eq_bigr => j do rewrite !mxE.
  eapply Rle_trans.
  apply big_Rmax_le.
  intros i; apply big_Rplus_le.
  intros j; apply Rabs_sum_prod.
  simpl; under eq_bigr => i do rewrite big_Rplus_exchange.
  under eq_bigr => i do under eq_bigr => j do (rewrite <- big_Rplus_scal_fun2).
  under eq_bigr => i do under eq_bigr => j do rewrite Rmult_comm.
  eapply Rle_trans. simpl. 
  apply big_Rmax_le.
  intros i; apply big_Rplus_le.
  intros j; apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply (leq_bigmax (fun l => \big[Rplus/0]_(k < p) Rabs (B l k))).  
  simpl.
  eapply Rle_trans.
  apply big_Rmax_le. 
  intros i.
  apply Rle_trans with (\sum_(i0 < n) (||| B ||| * Rabs (A i i0))%Re).
  apply Rle_refl.
  rewrite <- big_Rplus_scal_fun2.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r.
  apply matrix_norm_pos.
  apply Rle_refl.
  simpl.
  under eq_bigr => i do rewrite Rmult_comm.
  rewrite big_Rmax_scal.
  rewrite Rmult_comm; apply Rle_refl.
  apply matrix_norm_pos. 
Qed.

Notation "Imx [ n ]" := (@scalar_mx real_ringType n 1) (at level 10).

Lemma matrix_norm_id : forall {n}, ||| Imx_[n.+1] ||| = 1.
Proof.
  intros n.
  unfold matrix_norm.
  cut (forall i, \big[Rplus/0]_(j < n.+1) Rabs (1%:M i j) = 1).
  intros Hc.
  under eq_bigr => i do rewrite Hc.
  clear Hc.
  induction n.
  simpl.
  rewrite big_ord_recl big_ord0.
  rewrite Rmax_left.
  reflexivity.
  auto with real.
  rewrite big_ord_recl.
  rewrite IHn.
  apply Rmax_left; auto with real.
  intros i.
  rewrite (bigD1 i); try easy.
  rewrite mxE.
  rewrite eqxx.
  simpl.
  rewrite Rabs_R1.
  rewrite big1.
  auto with real.
  intros j Hj; rewrite mxE.
  rewrite eq_sym.
  rewrite (negPf Hj).
  now rewrite Rabs_R0.
Qed.
