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

From mathcomp Require Import all_ssreflect ssralg zmodp matrix.

From Flocq.Core Require Import Core.

Require Import Rstruct. 

Import GRing.Theory.

Open Scope ring_scope.
Open Scope R_scope.

(** Complements on big operators *)
Lemma big_Rmax_0 : forall d, \big[Rmax/0%R]_(i < d) 0 = 0.
Proof.
  intros d.
  rewrite big_const_ord.
  induction d; simpl; try lra.
  reflexivity.
  rewrite IHd; rewrite Rmax_left; try lra.
Qed.

Lemma big_Rplus_0 : forall d, \big[Rplus/0%R]_(i < d) 0 = 0.
Proof.
  intros d; rewrite big_const_ord.
  induction d; simpl; try lra.
  reflexivity.
  rewrite IHd; lra.
Qed.

Lemma big_Rplus_le : forall d F G,
    (forall i, F i <= G i) -> \sum_(i < d) (F i) <= \sum_(i < d) (G i).
Proof.
  intros d F G H; elim/big_ind2:_=> //; auto with real.
Qed.

Lemma big_Rmax_le : forall d (F1 : 'I_d -> R) F2,
     (forall i, (F1 i <= F2 i)) ->
      \big[Rmax/0%R]_(i < d) F1 i <= \big[Rmax/0%R]_(i < d) F2 i.
Proof.
intros n F1 F2 Hi; elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
apply Rle_trans with (Rmax x2 y1).
now apply Rle_max_compat_l.
now apply Rle_max_compat_r.
Qed.

Lemma big_Rplus_exchange : forall {n m} (F : 'I_n -> 'I_m -> R), 
    \sum_(i < n) (\sum_(j < m) (F i j)) = \sum_(j < m) (\sum_(i < n) (F i j)).
Proof.
intros n m F.
apply exchange_big_dep; trivial.
Qed.

Lemma big_Rplus_scal : forall d x (a : R),
    (a * \sum_(i < d) x) = \sum_(i < d) (a * x).
Proof.
intros n x a.
by rewrite <- mulr_sumr.
Qed.

Lemma big_Rplus_scal_fun1 : forall d F (a : R),
    (a * \sum_(i < d) (F i)) = \sum_(i < d) (a * (F i)).
Proof.
intros n F a.
by rewrite <- mulr_sumr.
Qed.

Lemma big_Rplus_scal_fun2 : forall d d' (A : 'M_(d,d')) (F : R -> R) (a : R) i,
    (a * \sum_(j < d') (F (A i j))) = \sum_(j < d') (a * (F (A i j))).
Proof.
intros d d' A F a i.
by rewrite <- mulr_sumr.
Qed.

Lemma big_Rmax_scal : forall d F a,
    0 <= a -> \big[Rmax/0%R]_(i < d) (a * (F i)) = a * \big[Rmax/0%R]_(i < d) F i.
Proof.
intros n F a Ha.
rewrite big_endo ?mulm0 //.
intros x y; rewrite RmaxRmult//.
apply Rmult_0_r.
Qed.

Lemma big_Rplus_half_const : forall d F (C : R), 
     \sum_(i < d) (F i + C) = \sum_(i < d) (F i) + INR d * C.
Proof.
intros d F C.
rewrite big_split big_const_ord iter_addr_0 -mulr_natl.
replace (d%:R) with (INR d); try auto with real.
clear F; elim: d => // n IH.
now rewrite S_INR IH (natrD _ 1) addrC.
Qed.

Lemma Rmax_Rplus_compat : forall (a b c : R), (Rmax a b) + c = Rmax (a + c) (b + c).
Proof.
intros a b c; unfold Rmax.
destruct (Rle_dec a b); 
destruct (Rle_dec (a + c) (b + c)); auto with real.
Qed. 

Lemma big_Rmax_half_const : forall d F C,
         (forall x, 0 <= F x) -> 0 <= C  ->
         \big[Rmax/0%R]_(i < d.+1) ((F i) + C) = \big[Rmax/0%R]_(i < d.+1) (F i) + C.
Proof.
  intros d F C H H0.
  induction d.
  + rewrite 2!big_ord_recl 2!big_ord0.
    destruct (Req_dec (F ord0) 0) as [E | E].
    rewrite E.
    repeat rewrite Rmax_left; try auto with real.
    apply Rle_trans with C; try auto with real.
    symmetry.
    repeat rewrite Rmax_left; try auto with real.
    apply Rle_trans with (0+0); try auto with real.
  + rewrite big_ord_recl.
    symmetry.
    rewrite IHd.
    simpl.
    rewrite big_ord_recl.
    rewrite big_ord_recl.
    now rewrite Rmax_Rplus_compat.
    auto with real.
Qed.

Lemma leq_bigmax : forall {d} F (i0 : 'I_d), 
        F i0 <= \big[Rmax/0]_(i < d) F i.
Proof.
intros d F i0.
generalize (mem_index_enum i0).
elim: index_enum => //= a l IH.
rewrite big_cons.
rewrite inE => /orP[/eqP->| Hi].
apply: Rmax_l.
eapply Rle_trans.
now apply: IH.
apply: Rmax_r.
Qed.

Lemma big_Rplus_pos (d : nat) (F : 'I_d -> R) :
  (forall i : 'I_d, 0 <= F i) -> 0 <= \sum_(i < d) F i.
Proof.
intros H.
eapply Rle_trans.
2: apply: big_Rplus_le.
2: exact: H.
rewrite big1; auto with real.
Qed.

Lemma big_Rmax_pos (d : nat) (F : 'I_d -> R) :
  0 <= \big[Rmax/0]_(i < d) F i.
Proof.
elim/big_rec:_=> //; auto with real.
intros i x _ H.
apply Rle_trans with (1 := H).
apply Rmax_Rle; auto with real.
Qed.

Lemma big_Rmax_add_le (d : nat) F G :
  \big[Rmax/0]_(i < d) (F i + G i) <= \big[Rmax/0]_(i < d) (F i) + \big[Rmax/0]_(i < d) (G i).
Proof.
  elim/big_ind3:_ => //; auto with real; try lra.
  intros x1 x2 x3 y1 y2 y3 H1 H2.
  unfold Rmax; destruct (Rle_dec x3 y3); destruct (Rle_dec x2 y2); destruct (Rle_dec x1 y1); lra.
Qed.


Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Lemma ring_R_plus_rw : forall (x y : R), (x + y)%Ri = (x + y)%Re.
Proof.
  reflexivity.
Qed.

Lemma ring_R_minus_rw : forall (x y : R), (x - y)%Ri = (x - y)%Re.
Proof.
  reflexivity.
Qed.

Lemma ring_R_opp_rw : forall (x : R), (- x)%Ri = (- x)%Re.
Proof.
  reflexivity.
Qed.

Lemma ring_R_mult_rw :  forall (x y : R), (x * y)%Ri = (x * y)%Re.
Proof.
  reflexivity.
Qed.

Ltac Rring_tac :=
  repeat rewrite ring_R_plus_rw;
  repeat rewrite ring_R_minus_rw;
  repeat rewrite ring_R_opp_rw;
  repeat rewrite ring_R_mult_rw.

Lemma big_Rplus_add (d : nat) F G :
  \big[Rplus/0]_(i < d) (F i + G i) = \big[Rplus/0]_(i < d) (F i) + \big[Rplus/0]_(i < d) (G i).
Proof.
  elim/big_ind3:_ => //; auto with real; try lra.
  intros x1 x2 x3 y1 y2 y3 H1 H2.
  rewrite H1 H2; lra. 
Qed.

Lemma big_Rplus_sub : forall d F G,
    \sum_(i < d) F i - \sum_(i < d) G i = \sum_(i < d) (F i - G i).
Proof.
  intros d F G.
  elim/big_ind3:_ => //; try auto with real.
  intros x1 x2 x3 y1 y2 y3 H1 H2.
  Rring_tac; lra.
Qed.

Lemma big_triang_le (d : nat) (F : 'I_d -> R) :
  Rabs (\sum_(i < d) (F i)) <= \sum_(i < d) Rabs (F i). 
Proof.
  elim/big_ind2:_ => //; try auto with real.
  rewrite Rabs_R0; apply Rle_refl.
  intros x1 x2 y1 y2 H1 H2.
  eapply Rle_trans.
  apply Rabs_triang.
  Rring_tac; lra.  
Qed.

(** technical lemmas for matrices *)

Lemma mat_apply_add_distr : forall {n m} (A B : 'M[R]_(m,n)) i j,
                        (A + B)%Ri i j = A i j + B i j.
Proof.
intros n m A B i j.
now rewrite !mxE.
Qed.

Lemma mat_apply_opp_distr : forall {n m} (A: 'M[R]_(m,n)) i j,
                        (- A)%Ri i j = - (A i j).
Proof.
intros n m A i j.
now rewrite !mxE.
Qed.



Lemma big_add_mat_le : forall {m n} (A B : 'M[R]_(m,n)) i,
  \sum_(j < n) Rabs ((A + B)%Ri i j) <= \sum_(j < n) Rabs (A i j) + \sum_(j < n) Rabs (B i j). 
Proof.
  intros m n A B i.
  elim/big_ind3:_=> //; auto with real; try lra.
  intros x1 x2 x3 y1 y2 y3 H1 H2.
  Rring_tac; lra.
  intros k _; rewrite mat_apply_add_distr; apply Rabs_triang.
Qed.

