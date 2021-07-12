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

Require Import Rdefinitions Raxioms RIneq Rbasic_fun.
Require Import Epsilon FunctionalExtensionality Lra 
               ProofIrrelevance Lia Omega.

Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool 
               mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.fintype
               mathcomp.ssreflect.finfun mathcomp.ssreflect.prime mathcomp.ssreflect.binomial
               mathcomp.ssreflect.choice mathcomp.ssreflect.bigop mathcomp.algebra.ssralg
               mathcomp.ssreflect.finset mathcomp.fingroup.fingroup mathcomp.ssreflect.seq 
               mathcomp.ssreflect.div mathcomp.algebra.ssrnum mathcomp.algebra.ssralg
               mathcomp.algebra.finalg mathcomp.algebra.matrix.

Require Import Rstruct Rstruct_Rpos_compl Compl.
Require Import Flocq.Core.Core.
Require Import Flocq.Prop.Mult_error.
Require Import Flocq.Prop.Plus_error.
Require Import Flocq.Prop.Relative.
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory.

(** Infinite vector norm *)

Definition vec_norm {n} : 'cV[R]_n -> R := 
       fun v => \big[Rmax / 0%R]_(i < n) Rabs (v i $0). 

Notation "\| x \|" := (vec_norm x) (at level 23).

Lemma vec_norm_pos : forall {n} (v : 'cV[R]_n),
            (0 <= \| v \|)%Re.
Proof.
intros n v. 
unfold vec_norm.
elim/big_rec:_=> //.
apply Rle_refl.
intros i x _ Hx.
unfold Rmax; destruct (Rle_dec (Rabs (v i $0)) x); try easy.
apply Rabs_pos.
Qed. 

Lemma vec_norm_def : forall {n},
           @vec_norm n (const_mx 0) = 0.
Proof.
intros n.
unfold vec_norm.
transitivity (\big[Rmax/0%R]_(i < n) 0).
f_equal; apply functional_extensionality.
intros x; simpl; rewrite !mxE.
now rewrite Rabs_R0.
rewrite big_const_ord.
induction n.
simpl; reflexivity.
simpl; rewrite IHn.
unfold Rmax; destruct (Rle_dec 0%Ri 0%Ri).
reflexivity.
case n0; apply Rle_refl. 
Qed.

Lemma vec_norm_scal : forall {n} (alpha : R) (v : 'cV[R]_n),
           (\| map_mx (fun a => alpha*a) v \| <= 
           Rabs alpha * \| v \|)%Re.  
Proof.
intros n alpha v.
unfold vec_norm.
rewrite <- big_Rmax_scal.
apply Req_le.
f_equal; apply functional_extensionality.
intros x; repeat f_equal.
rewrite <- Rabs_mult.
f_equal.
rewrite !mxE.
auto with real.
apply Rabs_pos.
Qed.

Lemma vec_norm_triang : forall {n} (v1 v2 : 'cV[R]_n),
            (\| v1 + v2 \| <= \| v1 \| + \| v2 \|)%Re.
Proof. 
intros n v1 v2.
unfold vec_norm.
elim/big_ind2: _ => //.
replace 0 with (Rplus R0 R0) at 1.
apply Rplus_le_compat.
apply Rle_refl.
elim/big_rec:_ => //.
apply Rle_refl.
intros i x _ H.
unfold Rmax; destruct (Rle_dec (Rabs (v2 i $0)) x); try easy.
apply Rabs_pos.
auto with real.
intros x1 x2 y1 y2 H1 H2.
unfold Rmax at 1 2.
destruct (Rle_dec x2 y2); 
destruct (Rle_dec x1 y1); try easy.
apply Rle_trans with 
  (y1 + \big[Rmax/0%R]_(i < n) Rabs (v2 i $0)); 
try easy.
apply Rplus_le_compat_r; lra.
apply Rle_trans with 
  (x1 + \big[Rmax/0%R]_(i < n) Rabs (v2 i $0)); 
try easy.
apply Rplus_le_compat_r; lra.
intros i _.
repeat (rewrite mat_apply_add_distr).
apply Rle_trans with (Rabs (v1 i $0) + Rabs (v2 i $0)).
eapply Rle_trans.
2 : eapply Rabs_triang.
auto with real.
apply Rplus_le_compat_l.
apply (@leq_bigmax n (fun i => Rabs (v2 i $0))).
intros x; apply Rabs_pos. 
Qed.

(** Infinite matrix norm *)

Definition matrix_norm {n} : 'M[R]_n -> R := fun A => 
                    \big[Rmax/0%R]_(i < n) (\big[Rplus/0%R]_(j < n) Rabs (A i j)).

Notation "||| A |||" := (matrix_norm A) (at level 23).

Lemma matrix_norm_pos : forall {n} (A : 'M[R]_n),
            (0 <= ||| A |||)%Re.
Proof.
intros n A.
unfold matrix_norm.
elim/big_rec:_=> //.
apply Rle_refl.
intros i x _ Hx.
unfold Rmax.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (A i j)) x).
easy.
elim/big_rec:_=> //.
apply Rle_refl.
intros j xj _ Hxj.
apply Rle_trans with (Rplus 0 0).
auto with real.
apply Rplus_le_compat.
apply Rabs_pos.
easy. 
Qed.

Lemma matrix_norm_def : forall {n},
           @matrix_norm n (const_mx 0) = 0.
Proof.
intros n.
unfold matrix_norm.
transitivity (\big[Rmax/0%R]_(i < n) 0).
f_equal; apply functional_extensionality.
intros x; simpl; f_equal.
transitivity (\big[Rplus/0%R]_(i < n) 0).
elim/big_rec2:_=> //.
intros i y1 y2 _ H.
rewrite H.
f_equal.
transitivity (Rabs 0).
f_equal.
now rewrite !mxE.
now rewrite Rabs_R0.
elim/big_ind:_=> //.
intros z y Hz Hy.
rewrite Hz Hy; auto with real.
elim/big_ind:_=> //.
intros z y Hz Hy.
rewrite Hz Hy.
destruct (Rle_dec 0 0).
rewrite Rmax_left; auto.
exfalso; apply n0; auto with real.
Qed. 

Lemma matrix_norm_scal : forall {n} (alpha : R) (A : 'M[R]_n),
           (||| map_mx (fun a => alpha*a) A ||| <= 
           Rabs alpha * ||| A |||)%Re.  
Proof.
intros n a A.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
apply Req_le.
f_equal; apply functional_extensionality.
intros x; repeat f_equal.
rewrite <- big_Rplus_scal.
elim/big_rec2:_ => //.
intros i y1 y2 _ Hy.
rewrite Hy.
rewrite <- Rabs_mult.
transitivity (Rabs ((map_mx [eta  *%R a] A) x i) + y1).
auto with real.
f_equal.
f_equal.
rewrite !mxE.
auto with real.
apply Rabs_pos.
apply Rabs_pos.
Qed.

Lemma sum_Rabs_triang : forall {n} (A B : 'M[R]_n) i, 
      (\big[Rplus/0]_(j < n) Rabs ((A + B)%Ri i j) <=
        \big[Rplus/0]_(j < n) Rabs (A i j) +
        \big[Rplus/0]_(j < n) Rabs (B i j))%Re.
Proof.
intros n A B i.
elim/big_rec3:_=>//.
auto with real.
intros j y1 y2 y3 _ H.
rewrite Rplus_assoc.
rewrite (Rplus_comm y2).
rewrite <- Rplus_assoc.
rewrite <- Rplus_assoc.
rewrite Rplus_assoc.
apply Rplus_le_compat.
rewrite !mxE.
apply Rabs_triang.
now rewrite Rplus_comm.
Qed.


Lemma matrix_norm_triang : forall {n} (A B : 'M[R]_n),
            (||| A + B ||| <= ||| A ||| + ||| B |||)%Re.
Proof.
intros n A B.
unfold matrix_norm.
elim/big_rec3:_=> //.
auto with real.
intros i y1 y2 y3 _ Hy.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs ((A + B)%Ri i j)) y3).
rewrite Rmax_right; try easy.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (A i j)) y2).
rewrite Rmax_right; try easy.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (B i j)) y1).
rewrite Rmax_right; try easy.
rewrite Rmax_left.
2: auto with real.
apply Rle_trans with (y2 + y1); try easy.
apply Rle_trans with (Rplus y2 y1); try easy.
auto with real.
apply Rplus_le_compat_l.
auto with real.
rewrite Rmax_left; try auto with real.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (B i j)) y1).
rewrite Rmax_right; try easy.
apply Rle_trans with (Rplus y2  y1); try easy.
apply Rplus_le_compat_r.
auto with real.
rewrite Rmax_left; try auto with real.
apply Rle_trans with (Rplus y2 y1); try easy. 
apply Rplus_le_compat; auto with real.
rewrite Rmax_left; try auto with real.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (A i j)) y2).
rewrite Rmax_right; try easy.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (B i j)) y1).
rewrite Rmax_right; try easy.
apply Rle_trans with (Rplus (\big[Rplus/0]_(j < n) Rabs (A i j))
                            (\big[Rplus/0]_(j < n) Rabs (B i j))).
apply sum_Rabs_triang.
apply Rplus_le_compat; auto with real.
rewrite Rmax_left; try auto with real.
apply Rle_trans with (Rplus (\big[Rplus/0]_(j < n) Rabs (A i j))
                            (\big[Rplus/0]_(j < n) Rabs (B i j))).
apply sum_Rabs_triang.
apply Rplus_le_compat_r; try easy.
rewrite Rmax_left; try auto with real.
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (B i j)) y1).
rewrite Rmax_right; try easy.
apply Rle_trans with (Rplus (\big[Rplus/0]_(j < n) Rabs (A i j))
                            (\big[Rplus/0]_(j < n) Rabs (B i j))).
apply sum_Rabs_triang.
apply Rplus_le_compat_l.
auto with real.
rewrite Rmax_left; try auto with real.
apply sum_Rabs_triang.
Qed.

(** Submultiplicativity of matrix/vector norms *) 

Lemma mx_vec_norm_submult : forall {n} (A : 'M[R]_n) (y : 'cV[R]_n), 
                  (\| A *m y \| <= ||| A ||| * \| y \|)%Re.
Proof. 
intros n A y.
unfold vec_norm, mulmx, matrix_norm.
simpl.
apply Rle_trans with (\big[Rmax/0]_(i < n) 
   Rabs (\sum_(j < n) A i j * y j $0)).
apply big_Rmax_le.
intros i.
apply Req_le.
f_equal; now rewrite !mxE.
apply Rle_trans with 
   (\big[Rmax/0]_(i < n) (\sum_(j < n) 
           Rabs (A i j) * Rabs (y j $0))).
apply big_Rmax_le.
intros i.
apply Rle_trans with (\sum_(j < n) Rabs (A i j * y j $0)).
elim/big_rec2:_=>//.
by rewrite Rabs_R0; apply Rle_refl.
intros j y1 y2 _ Hy.
eapply Rle_trans.
apply Rabs_triang.
apply Rplus_le_compat; try apply Rle_refl; try easy.
apply Req_le.
f_equal; apply functional_extensionality; intros j.
f_equal; now rewrite Rabs_mult.
apply Rle_trans with 
     (\big[Rmax/0]_(i < n) (\sum_(j < n) (Rabs (A i j) 
            * (\big[Rmax/0]_(k < n) (Rabs (y k $0)))))).
apply big_Rmax_le.
intros i.
elim /big_ind2: _ => //; auto with real.
intros j _.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply (@leq_bigmax n (fun k => Rabs (y k $0))).
intros k; apply Rabs_pos.
replace (\big[Rmax/0]_(i < n) (\sum_(j < n) Rabs (A i j) *
              \big[Rmax/0]_(k < n) Rabs (y k $0))) with 
        (\big[Rmax/0]_(i < n) ((\sum_(j < n) 
            ((\big[Rmax/0]_(k < n) Rabs (y k $0)) 
             * Rabs (A i j))))).
apply Rle_trans with 
   (\big[Rmax/0]_(i < n) (\big[Rmax/0]_(k < n) 
                 Rabs (y k $0)  * (\sum_(j < n) 
               Rabs (A i j)))).
apply big_Rmax_le.
intros i. 
rewrite big_Rplus_scal.
apply Req_le.
reflexivity.
elim/big_rec:_=>//.
apply Rle_refl.
intros j x _ Hx.
unfold Rmax; destruct (Rle_dec (Rabs (y j $0)) x); 
   try easy.
apply Rabs_pos.
rewrite Rmult_comm.
rewrite big_Rmax_scal.
apply Req_le; reflexivity.
elim/big_rec:_=>//.
apply Rle_refl.
intros j x _ Hx.
unfold Rmax; destruct (Rle_dec (Rabs (y j $0)) x); 
   try easy.
apply Rabs_pos.
f_equal; apply functional_extensionality.
intros x; f_equal.
f_equal; apply functional_extensionality.
intros t; f_equal.
rewrite <- Rmult_comm.
auto with real.
Qed.

(** Norm of the identity matrix *)

Lemma mat_id_sum_1 : forall {n} i, (0 < n)%coq_nat ->
        \big[Rplus/0]_(j < n) Rabs (1%:M i j) = 1.
Proof.
intros n i Hn. 
transitivity (\big[Rplus/0]_(j < n) 
                 (match (eq_nat_dec i j) with 
                      | left _ => 1
                      | right _ => 0 end)).
f_equal; apply functional_extensionality.
intros j; f_equal.
destruct (Nat.eq_dec i j).
transitivity (Rabs (1%:M i i)).
f_equal. f_equal. 
symmetry.
destruct i as (i,Hi).
destruct j as (j,Hj).
simpl in e.
generalize Hj; rewrite <- e.
intros Hj0.
f_equal.
apply proof_irrelevance.
rewrite !mxE.
rewrite Rabs_right.
rewrite eq_refl.
reflexivity.
rewrite eq_refl; simpl.
apply Rle_ge.
auto with real.
transitivity (Rabs 0). 
f_equal.
rewrite !mxE.
unfold nat_of_bool, eq_op.
replace (Equality.op 
  (Equality.class (ordinal_finType n)) i j) 
   with false.
reflexivity.
simpl.
symmetry.
now apply/eqP.
rewrite Rabs_right; try apply Rle_refl.
reflexivity.
induction n.
now exfalso.
rewrite big_ord_recr.
simpl.
destruct (Nat.eq_dec i n).
transitivity (\big[Rplus/0]_(i0 < n) 0 + 1).
apply Rplus_eq_compat_r.
elim/big_rec2:_=>//.
intros z y1 y2 _ Hy.
rewrite Hy.
f_equal.
destruct (Nat.eq_dec i z).
destruct z as (z,Hz).
simpl in e0.
rewrite <- e0 in Hz.
rewrite e in Hz.
assert (Hz' : (n < n)%coq_nat).
now apply/ltP.
exfalso; omega.
reflexivity.
elim/big_rec:_=> //.
auto with real.
intros _ x _ H.
transitivity (0 + (x + 1)).
transitivity ((0 + x) + 1). 
reflexivity.
rewrite <- Rplus_assoc.
reflexivity.
rewrite H. 
auto with real.
transitivity (1 + 0)%Re.
f_equal.
assert (Hi : (i < n)%N).
destruct i as (i,Hii).
assert (Hii' : (i < n.+1)%coq_nat).
now apply/ltP.
simpl; simpl in n0.
apply/ltP.
omega.
assert (IH : (0 < n)%coq_nat).
apply le_lt_trans with i.
omega.
now apply/ltP.
specialize (IHn (Ordinal Hi) IH).
simpl in IHn.
rewrite IHn.
reflexivity.
auto with real.
Qed.

Lemma matrix_norm_id : forall {n}, (0 < n)%coq_nat 
                        -> @matrix_norm n 1%:M = 1.
Proof. 
intros n Hn. 
unfold matrix_norm.
transitivity (\big[Rmax/0]_(i < n) 1).
f_equal; apply functional_extensionality.
intros x; f_equal.
now apply mat_id_sum_1.
induction n.
now exfalso.
rewrite big_ord_recl.
destruct (Nat.eq_dec 0 n).
generalize Hn; rewrite <- e.
intros _.
rewrite big_ord0.
rewrite Rmax_left.
reflexivity.
auto with real.
rewrite IHn.
rewrite Rmax_left; try (apply Rle_refl).
reflexivity.
auto with arith.
Qed.

(** Submultiplicativity of the matrix norm *)

Lemma mx_norm_submult : forall {n} (A B : 'M[R]_n),
           (||| A *m B ||| <=  ||| A ||| * ||| B |||)%Re.
Proof.
intros n A B.
unfold matrix_norm, mulmx.
simpl.
apply Rle_trans with (\big[Rmax/0]_(i < n) \big[Rplus/0]_(j < n)
   Rabs (\sum_(k < n) A i k * B k j)).
apply big_Rmax_le.
intros i.
elim /big_ind2: _ => //; auto with real.
intros j _.
apply Req_le.
f_equal; now rewrite !mxE.
apply Rle_trans with 
   (\big[Rmax/0]_(i < n) \big[Rplus/0]_(j < n) (\sum_(k < n) 
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
     (\big[Rmax/0]_(i < n) (\sum_(k < n) 
            (\big[Rplus/0]_(j < n) (Rabs (A i k) * Rabs (B k j))))).
apply Req_le.
f_equal; apply functional_extensionality.
intros x; f_equal.
now rewrite big_Rplus_exchange.
apply Rle_trans with (\big[Rmax/0]_(i < n) (\sum_(k < n)
                       Rabs (A i k) * \big[Rplus/0]_(j < n) 
                         (Rabs (B k j)))).
apply Req_le; f_equal; apply functional_extensionality.
intros x; f_equal.
f_equal; apply functional_extensionality.
intros y; f_equal.
rewrite big_Rplus_scal.
reflexivity.
apply Rabs_pos.
apply Rle_trans with (\big[Rmax/0]_(i < n) (\sum_(k < n)
        (\big[Rmax/0]_(l < n) (\big[Rplus/0]_(j < n) (Rabs (B l j)))) 
    * Rabs (A i k))).
apply big_Rmax_le.
intros i.
elim /big_ind2: _ => //; auto with real.
intros j _.
rewrite <- Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply (@leq_bigmax n (fun l => \big[Rplus/0]_(j0 < n) Rabs (B l j0))).
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
  (\big[Rmax/0]_(i < n) ((\big[Rmax/0]_(l < n) 
                         (\big[Rplus/0]_(j < n) 
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
destruct (Rle_dec (\big[Rplus/0]_(j0 < n) Rabs (B j j0)) x).
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
destruct (Rle_dec (\big[Rplus/0]_(j < n) Rabs (B i j)) x).
easy.
elim/big_rec:_=> //.
apply Rle_refl.
intros j y _ Hy.
apply Rle_trans with (Rplus 0 0).
auto with real.
apply Rplus_le_compat; try easy.
apply Rabs_pos.
Qed. 
