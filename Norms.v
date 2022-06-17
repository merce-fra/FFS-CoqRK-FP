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
Require Import Reals FunctionalExtensionality ProofIrrelevance Lia Lra.

From mathcomp
     Require Import all_ssreflect ssralg matrix.

Require Import Rstruct Rstruct_Rpos_compl Compl.

Definition matrix_norm {m n} : 'M[R]_(m,n) -> R :=
  fun A => \big[Rmax/0]_(i < m) (\big[Rplus/0]_(j < n) (Rabs (A i j))).

Notation "||| A |||" := (matrix_norm A) (at level 23).

Notation "O_( m , n )" := (@const_mx _ m n 0) (at level 20).

Lemma matrix_norm_pos : forall {m n} (A : 'M[R]_(m,n)), 0 <= ||| A |||.
Proof.
intros m n A.
unfold matrix_norm.
elim/big_rec:_=> //.
apply Rle_refl.
intros i x _ Hx.
apply Rle_trans with x; try lra.
apply Rmax_r.
Qed.

Lemma matrix_norm_def : forall {m n}, ||| O_(m,n) ||| = 0.
Proof.
intros m n; unfold matrix_norm.
cut (forall i j, Rabs ((O_( m, n)) i j) = 0); intros Hu.
under eq_bigr => i do under eq_bigr => j do (rewrite Hu).
elim/big_ind:_=> //.
intros x y Hx Hy; rewrite Hx Hy; rewrite Rmax_left; try lra.
intros; elim/big_ind:_=> //.
intros x y H1 H2; rewrite H1 H2; auto with real.
intros; unfold const_mx; now rewrite !mxE Rabs_R0.
Qed.

Lemma big_Rplus_scal_abs : forall m n (A : 'M[R]_(m,n))a i, (0 <= a)%Re ->
       (Rabs a * \big[Rplus/0]_(j < n) Rabs (A i j)) = \big[Rplus/0]_(j < n) (a*Rabs (A i j)).
Proof.
intros m n F a i Ha.
rewrite big_Rplus_scal; try auto with real.
rewrite Rabs_right; auto with real.
Qed.

Lemma matrix_norm_scal_r : forall {m n} (a : R) (A : 'M[R]_(m,n)),
           ||| map_mx (fun x => x*a) A ||| = (Rabs a * ||| A |||)%Re.
Proof.
intros m n a A; unfold matrix_norm.
rewrite <- big_Rmax_scal; try apply Rabs_pos.
under eq_bigr => i do under eq_bigr => j do rewrite !mxE GRing.mulrC Rabs_mult.
f_equal; apply functional_extensionality.
intros x; repeat f_equal.
now rewrite <- big_Rplus_scal; try apply Rabs_pos.
Qed.

Lemma matrix_norm_scal_l : forall {m n} (a : R) (A : 'M[R]_(m,n)),
           ||| map_mx (fun x => a*x) A ||| = (Rabs a * ||| A |||)%Re.
Proof.
intros m n a A; unfold matrix_norm.
rewrite <- big_Rmax_scal; try apply Rabs_pos.
under eq_bigr => i do under eq_bigr => j do rewrite !mxE Rabs_mult.
f_equal; apply functional_extensionality.
intros x; repeat f_equal.
now rewrite <- big_Rplus_scal; try apply Rabs_pos.
Qed.

Lemma sum_Rabs_triang : forall {m n} (A B : 'M[R]_(m,n)) i, 
      (\big[Rplus/0]_(j < n) Rabs ((A + B)%Ri i j) <=
        \big[Rplus/0]_(j < n) Rabs (A i j) +
        \big[Rplus/0]_(j < n) Rabs (B i j))%Re.
Proof.
intros m n A B i.
elim/big_rec3:_=>//; try auto with real.
intros j y1 y2 y3 _ H.
rewrite Rplus_assoc (Rplus_comm y2).
repeat rewrite <- Rplus_assoc.
rewrite Rplus_assoc.
apply Rplus_le_compat.
rewrite !mxE.
apply Rabs_triang.
now rewrite Rplus_comm.
Qed.

Lemma Rmax_plus_ineq : forall a b c d,
    Rmax (a + b) (c + d) <= Rmax a c + Rmax b d.
Proof.
  intros a b c d.
  destruct (Rle_dec a c) as [E1 | E1];
    destruct (Rle_dec b d) as [E2 | E2];
    destruct (Rle_dec (a + b) (c + d)) as [E3 | E3];
    try auto with real.
  + rewrite (Rmax_right _ _ E3).
    rewrite (Rmax_right _ _ E1).
    rewrite (Rmax_right _ _ E2).
    apply Rle_refl.
    apply Rnot_le_lt in E3.
    apply Rlt_le in E3.
    rewrite Rmax_left; try lra. 
    apply Rplus_le_compat.
    apply Rmax_l.
    apply Rmax_l.
  + rewrite Rmax_right; try lra.
    apply Rplus_le_compat.
    apply Rmax_r; try lra.
    apply Rmax_r; try lra.
  + apply Rnot_le_lt in E3.
    apply Rlt_le in E3.
    rewrite Rmax_left; try lra.
    apply Rplus_le_compat.
    apply Rmax_l.
    apply Rmax_l.
  + rewrite Rmax_right; try lra.
    apply Rplus_le_compat.
    apply Rmax_r; try lra.
    apply Rmax_r; try lra.
  + apply Rnot_le_lt in E3.
    apply Rlt_le in E3.
    rewrite Rmax_left; try lra.
    apply Rplus_le_compat.
    apply Rmax_l.
    apply Rmax_l.
  + rewrite Rmax_right; try lra.
  + apply Rnot_le_lt in E3.
    apply Rlt_le in E3.
    rewrite Rmax_left; try lra.
    apply Rplus_le_compat.
    apply Rmax_l.
    apply Rmax_l.
Qed.

Lemma matrix_norm_triang : forall {m n} (A B : 'M[R]_(m,n)),
            (||| A + B ||| <= ||| A ||| + ||| B |||)%Re.
Proof.
  intros m n A B; unfold matrix_norm.
  elim/big_rec3:_=> //; try auto with real.
  intros i y1 y2 y3 _ Hy.
  eapply Rle_trans.
  apply Rle_max_compat_l.
  apply Hy.
  eapply Rle_trans.
  apply Rle_max_compat_r.
  apply sum_Rabs_triang.
  apply Rmax_plus_ineq; 
    try (auto with real; try lra;
         elim/big_ind:_=> //; try (intros; auto with real; try lra; try apply Rabs_pos)).
Qed.

Lemma Rabs_sum_prod : forall n f g,
    Rabs (\sum_(i < n) ((f i) * (g i))) <= \sum_(i < n) (Rabs (f i) * Rabs (g i)).
Proof.
  intros n f g.
  apply Rge_le.
  under eq_bigr => i do rewrite <- Rabs_mult.
  elim/big_ind2:_ => //.
  rewrite Rabs_R0; apply Rle_refl.
  intros x1 x2 y1 y2 H1 H2.
  eapply Rge_trans.
  2: apply Rle_ge, Rabs_triang.
  apply Rplus_ge_compat; try auto with real.
  intros; auto with real.
Qed. 


(** Submultiplicativity of matrix/vector norms *) 
Lemma norm_submult : forall {m n p} (A : 'M[R]_(m,n)) (B : 'M[R]_(n,p)), 
                  (||| A *m B ||| <= ||| A ||| * ||| B |||)%Re.
Proof.
intros m n p A B.
unfold matrix_norm, mulmx.
simpl. 
apply Rle_trans with (\big[Rmax/0]_(i < m) \big[Rplus/0]_(j < p)
   Rabs (\sum_(k < n) A i k * B k j)).
apply big_Rmax_le.
intros i.
elim /big_ind2: _ => //; auto with real.
intros j _.
apply Req_le.
f_equal; now rewrite !mxE.
apply Rle_trans with 
   (\big[Rmax/0]_(i < m) \big[Rplus/0]_(j < p) (\sum_(k < n) 
           Rabs (A i k) * Rabs (B k j))).
apply big_Rmax_le.
intros i.
elim /big_ind2: _ => //; auto with real.
intros j _.
apply Rle_trans with (\sum_(k < n) Rabs (A i k * B k j)).
elim/big_rec2:_=>//.
by rewrite Rabs_R0; apply Rle_refl.
intros k y1 y2 _ Hy.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat; try apply Rle_refl; try easy.
apply Req_le.
f_equal; apply functional_extensionality; intros k.
f_equal. 
rewrite Rabs_mult.
auto with real. 
apply Rle_trans with 
     (\big[Rmax/0]_(i < m) (\sum_(k < n) 
            (\big[Rplus/0]_(j < p) (Rabs (A i k) * Rabs (B k j))))).
apply Req_le.
f_equal; apply functional_extensionality.
intros x; f_equal.
now rewrite big_Rplus_exchange.
apply Rle_trans with (\big[Rmax/0]_(i < m) (\sum_(k < n)
                       Rabs (A i k) * \big[Rplus/0]_(j < p) 
                         (Rabs (B k j)))).
apply Req_le; f_equal; apply functional_extensionality.
intros x; f_equal.
f_equal; apply functional_extensionality.
intros y; f_equal.
rewrite big_Rplus_scal.
reflexivity.
apply Rabs_pos.
apply Rle_trans with (\big[Rmax/0]_(i < m) (\sum_(k < n)
        (\big[Rmax/0]_(l < n) (\big[Rplus/0]_(j < p) (Rabs (B l j)))) 
    * Rabs (A i k))).
apply big_Rmax_le.
intros i.
elim /big_ind2: _ => //; auto with real.
intros j _.
rewrite <- Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply (@leq_bigmax n (fun l => \big[Rplus/0]_(j0 < p) Rabs (B l j0))).
intros l.
elim/big_rec:_=> //.
apply Rle_refl.
intros k x _ Hx.
apply Rle_trans with (Rplus 0 0).
auto with real.
apply Rplus_le_compat. 
apply Rabs_pos.
easy.
apply Rle_trans with 
  (\big[Rmax/0]_(i < m) ((\big[Rmax/0]_(l < n) 
                         (\big[Rplus/0]_(j < p) 
                         Rabs (B l j)))
          *(\sum_(k < n) Rabs (A i k)))).
apply big_Rmax_le.
intros i.
rewrite big_Rplus_scal.
apply Rle_refl.
elim/big_rec:_=> //.
apply Rle_refl.
intros j x _ Hx.
unfold Rmax.
destruct (Rle_dec (\big[Rplus/0]_(j0 < p) Rabs (B j j0)) x).
easy.
elim/big_rec:_=> //.
apply Rle_refl.
intros k y _ Hy.
apply Rle_trans with (Rplus 0 0). 
auto with real.
apply Rplus_le_compat.
apply Rabs_pos.
easy.
rewrite big_Rmax_scal.
rewrite <- Rmult_comm.
apply Rle_refl.
elim/big_rec:_=> //.
apply Rle_refl.
intros i x _ Hx.
unfold Rmax;
destruct (Rle_dec (\big[Rplus/0]_(j < p) Rabs (B i j)) x).
easy.
elim/big_rec:_=> //.
apply Rle_refl.
intros j y _ Hy.
apply Rle_trans with (Rplus 0 0).
auto with real.
apply Rplus_le_compat; try easy.
apply Rabs_pos.
Qed.

Notation "Imx [ n ]" := (@scalar_mx real_ringType n 1) (at level 10). 
(*
Lemma big_mkord_true n (F : _ -> R) op idx :
  \big[op/idx]_(0 <= i < n) F i = \big[op/idx]_(i < n) F i.
Proof.
 transitivity (\big[op/idx]_(i < n | true) F i). 
 now rewrite big_mkord. 
 reflexivity. 
Qed.
*)
(** Norm of the identity matrix *)
Lemma mat_id_sum_1 : forall {n} i, 
        \big[Rplus/0]_(j < n.+1) Rabs (Imx_[n.+1] i j) = 1.
Proof.
  intros n i.
  induction n.
  + rewrite big_ord_recr.
    simpl; rewrite big_ord0.
    unfold scalar_mx; simpl; rewrite !mxE.
    cut ((i == ord_max) = true).
    intros Hc; rewrite Hc.
    simpl; rewrite Rabs_R1; auto with real.
    unfold ord_max; destruct i; simpl.
    apply/eqP; apply ord_inj; simpl.
    induction m;
      [ auto with real | exfalso; auto with real ].
  + rewrite big_ord_recr; simpl.
    case (Nat.eq_dec i n.+1); intros Hin.
    - transitivity (0 + 1)%Re; try auto with real.
      f_equal.
      transitivity (\big[Rplus/0]_(i0 < n.+1) 0).
      elim/big_rec2:_=>//; try auto with real.
      intros k y z _ Hyz.
      rewrite Hyz; f_equal; try auto with real.
      unfold scalar_mx; simpl; rewrite !mxE.
      cut ((i == widen_ord (m:=n.+2) (leqnSn n.+1) k) = false).
      intros Hc; rewrite Hc.
      simpl; apply Rabs_R0.
      apply/eqP.
      destruct k as (k,Hk).
      intros Hf.
      cut (k <> n.+1).
      intros Hf'; apply Hf'.
      symmetry in Hf.
      inversion Hin.
      apply/eqP; inversion Hf.
      simpl; auto.
      intros Hneq; clear Hf.
      rewrite Hneq in Hk.
      contradict Hk; generalize Nat.lt_irrefl; intros Hir Hn.
      apply (Hir n.+1); auto with arith.
      apply/ltP; apply Hn.
      elim/big_ind:_ => //.
      intros x y Hx Hy; rewrite Hx Hy; auto with real.
      rewrite <- Rabs_R1.
      f_equal.
      unfold scalar_mx; simpl; rewrite !mxE.
      cut ((i == ord_max) = true).
      intros Hc; rewrite Hc; try easy.
      unfold ord_max; destruct i; simpl.
      apply/eqP; apply ord_inj; simpl.
      apply Hin.
    - transitivity (1 + 0)%Re; try auto with real.
      f_equal.
      destruct i as (m,Hm).
      simpl in Hin. 
      assert (Hmn: (m < n.+1)%N).
      apply/ltP. 
      cut (m < n.+2)%coq_nat.
      intros Hm'; try lia.
      apply/ltP.
      easy.
      etransitivity.
      2:apply (IHn (Ordinal (n:=n.+1) (m:=m) Hmn)).
      elim/big_ind2:_ => //.
      intros x1 x2 y1 y2 H1 H2; rewrite H1 H2; reflexivity.
      intros k _; f_equal.
      rewrite !mxE. f_equal.
      cut ((i == ord_max) = false).
      intros Hc; unfold scalar_mx; simpl; rewrite !mxE Hc.
      simpl; apply Rabs_R0.
      unfold ord_max; destruct i; simpl.
      apply/eqP.
      intros H. 
      apply Hin. inversion H.
      now simpl. 
Qed.

Lemma matrix_norm_id : forall {n}, ||| Imx_[n.+1] ||| = 1.
Proof. 
intros n. 
unfold matrix_norm.
cut (forall i,
        \big[Rplus/0]_(j < n.+1) Rabs (1%:M i j) = 1).
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
apply mat_id_sum_1.
Qed.
