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
Require Import Epsilon FunctionalExtensionality Lra ProofIrrelevance Lia Omega.
From mathcomp
Require Import all_ssreflect finalg ssrnum ssralg finalg matrix.
From Flocq.Core 
Require Import Core. 
From Flocq.Prop 
Require Import Mult_error Plus_error Relative.
Require Import Rstruct Rstruct_Rpos_compl.
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory.


Notation "$0" := (Ordinal (ltn0Sn O)).

(** Complements on big operators *)

Lemma big_Rmax_le : forall d (F1 : 'I_d -> R) F2, 
      (forall i, (F1 i <= F2 i)%Re) ->
      (\big[Rmax/0%R]_(i < d) F1 i <= \big[Rmax/0%R]_(i < d) F2 i)%Re.
Proof.
intros n F1 F2 Hi; elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
apply Rle_trans with (Rmax x2 y1).
now apply Rle_max_compat_l.
now apply Rle_max_compat_r.
Qed.  


Lemma big_Rplus_exchange : forall {n} (F : 'I_n -> 'I_n -> R), 
        \sum_(i < n) (\sum_(j < n) (F i j)) = \sum_(j < n) (\sum_(i < n) (F i j)).
Proof. 
intros n F.
apply exchange_big_dep; trivial.
Qed. 


Lemma big_Rplus_scal : forall d F a, (0 <= a)%Re ->
      \sum_(i < d) (a * (F i)) = a * \sum_(i < d) F i.
Proof.
intros n F a Ha.
elim/big_ind2: _; auto with real.
intros x1 x2 y1 y2 H1 H2.
rewrite H1 H2; auto with real.
Qed.

Lemma big_Rmax_scal : forall d F a, (0 <= a)%Re ->
      \big[Rmax/0%R]_(i < d) (a * (F i)) = a * \big[Rmax/0%R]_(i < d) F i.
Proof.
intros n F a Ha.
rewrite big_endo ?mulm0 //.
intros x y; rewrite RmaxRmult//.
apply Rmult_0_r.
Qed.

Lemma big_Rplus_half_const : forall d F (C : R), 
     \sum_(i < d) ((F i) + C) = (\sum_(i < d) (F i)) + INR d* C.
Proof.
intros d F C.
transitivity (\sum_(i < d) (F i) 
            + \sum_(i < d) C). 
elim/big_ind3:_=>//.
auto with real.
intros x1 x2 x3 y1 y2 y3 H1 H2.
rewrite H1 H2.
rewrite <- Rplus_assoc.
rewrite <- Rplus_assoc.
f_equal.
rewrite Rplus_assoc.
rewrite Rplus_assoc.
f_equal.
now rewrite Rplus_comm.
f_equal.
rewrite big_const_ord.
clear F.
induction d.
auto with real.
rewrite iterS.
rewrite IHd.
rewrite S_INR.
transitivity ((INR d + 1) * C)%Re.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
auto with real.
auto with real.
Qed.


Lemma Rmax_Rplus_compat : forall (a b c : R), (Rmax a b) + c = Rmax (a + c) (b + c).
Proof.
intros a b c.
unfold Rmax.
destruct (Rle_dec a b); 
destruct (Rle_dec (a + c) (b + c)).
auto with real.
exfalso; apply n.
now apply Rplus_le_compat_r.
exfalso; apply n.
now apply Rplus_le_reg_r with c.
auto with real.
Qed. 

Lemma big_Rmax_half_const : forall d F C, 
         (forall x, (0 <= F x)%Re) -> (0 <= C)%Re  -> 
         \big[Rmax/0%R]_(i < d.+1) ((F i) + C) = \big[Rmax/0%R]_(i < d.+1) (F i) + C.
Proof.
intros d F C H H0.
induction d.
rewrite 2!big_ord_recl 2!big_ord0.
destruct (Req_dec (F ord0) 0) as [E | E].
rewrite E.
repeat rewrite Rmax_left; try auto with real.
apply Rle_trans with C; try auto with real.
destruct (Req_dec C 0) as [E' | E'].
rewrite E'.
repeat rewrite Rmax_left; try auto with real.
apply Rle_trans with (F ord0); try auto with real.
unfold Rmax.
destruct (Rle_dec (F ord0 + C)%Ri 0);
destruct (Rle_dec (F ord0) 0).
exfalso.
auto with real.
exfalso.
apply Rle_not_lt in r.
apply r.
apply Rle_lt_trans with C; try auto with real.
apply Rle_lt_trans with (0 + C); auto with real.
exfalso; auto with real.
reflexivity.
rewrite big_ord_recl.
rewrite IHd.
etransitivity.
2 : {rewrite big_ord_recl.
reflexivity. }
rewrite Rmax_Rplus_compat.
reflexivity.
now intros.
Qed. 



Lemma big_Rmax_pos_eq_big_Rmax {d} (F : 'I_d -> R) (H : forall i, (0 <= F i)%Re) :
               \big[Rmax/0]_(i < d) F i = toR (\big[Rmax_pos/Rpos_0]_(i < d) (mk_Rpos (H i))). 
Proof. 
elim/big_rec2:_=> //.
intros i y1 y2 _ Hy.
rewrite Hy.
unfold Rmax_pos; simpl.
unfold Rmax_pos_aux.
f_equal.
Qed. 

Lemma leq_bigmax_aux : forall {d} F (i0 : 'I_d), 
         (toR (F i0) <= toR (\big[Rmax_pos/Rpos_0]_(i < d) F i))%Re.
Proof.
intros d F i0.
induction d.
destruct i0; now exfalso.
rewrite big_ord_recr.
simpl; unfold Rmax_pos_aux.
destruct i0 as (i,Hi).
destruct (lt_dec i d).
assert (Hy : (i < d)%nat).
now apply/ltP.
pose (F2 := fun i:'I_d => 
       F (widen_ord (leqnSn d) i)).
specialize (IHd F2).
replace (F (Ordinal Hi)) with 
        (F2 (Ordinal Hy)).
replace (\big[Rmax_pos/Rpos_0]_(i0 < d) 
           F (widen_ord (leqnSn d) i0)) 
   with (\big[Rmax_pos/Rpos_0]_(i0 < d) (F2 i0)).
apply Rmax_Rle.
left.
apply IHd.
f_equal.
unfold F2; f_equal.
unfold widen_ord; simpl.
f_equal.
apply proof_irrelevance.
assert (Hid : i = d).
assert (Hi' : (i < d.+1)%coq_nat).
now apply/ltP.
lia.
apply Rmax_Rle.
right.
apply Req_le; f_equal.
unfold ord_max; f_equal.
generalize Hi.
rewrite Hid.
intros Hi2.
f_equal.
apply proof_irrelevance.
Qed.

Lemma leq_bigmax : forall {d} F (i0 : 'I_d), 
        (forall i, (0 <= F i)%Re) -> 
        (F i0 <= \big[Rmax/0]_(i < d) F i)%Re.
Proof.
intros d F i0 Hf.
rewrite big_Rmax_pos_eq_big_Rmax.
apply Rle_trans with (toR {| toR := F i0; Hpos := Hf i0 |}).
simpl; apply Rle_refl. 
apply: leq_bigmax_aux.
Qed.

(** Complements on INR *)
Local Open Scope R_scope.

Lemma du_pred_cond : forall d x, 0 <= x ->
   (1 <= d)%coq_nat -> INR d * x < 1 -> INR (d - 1) * x < 1.
Proof.
intros d x H0 Hd Hdu.
apply Rle_lt_trans with (INR d * x); try easy.
apply Rmult_le_compat_r; try easy.
apply le_INR.
destruct d.
unfold subn; simpl; reflexivity.
replace (d.+1 - 1)%nat with ((d.+1).-1).
apply Nat.le_pred_l.
unfold subn; simpl; auto with arith.
Qed. 

Lemma INR_d_succ : forall d, 
      (1 <= d)%coq_nat -> INR (d - 1) + 1 = INR d.
Proof.
intros d Hd.
replace 1 with (INR 1) by reflexivity.
rewrite <- plus_INR.
destruct d.
exfalso; easy.
replace (d.+1 - 1 + 1)%coq_nat with (d.+1).
reflexivity.
rewrite subn1.
simpl.
lia.
Qed. 

(** From list to vectors, from fold to bigop *)

(* Equivalence btw fold_right on sum and bigop *)
Lemma list_fold_right_sum : forall (l : list R), 
          \sum_(i < length l) (nth i l) 0 = 
          fold_right (fun x y => (x+y)) 0 l.
Proof.
intros l.
induction l.
simpl;now rewrite big_ord0.
rewrite big_ord_recl.
simpl.
apply Rplus_eq_compat_l.
easy.
Qed.

(* Equivalence btw fold_right on rounded sum and bigop *)
Lemma list_fold_right_rnd_sum : forall (l : list R) W, 
          \big[(fun x y => W (x + y)) / 0%R]_(i < length l) (nth i l) 0 = 
          fold_right (fun x y => W (x + y)) 0 l.
Proof.
intros l W.
induction l.
simpl;now rewrite big_ord0.
rewrite big_ord_recl.
simpl.
transitivity (W (a + \big[(fun x y => 
  W (x + y))/0]_(i < length l) nth i l 0)).
repeat f_equal. 
now repeat f_equal.
Qed.


Lemma list_fold_right_sum' : forall (l : list R) d, d = length l ->
          \sum_(i < d) (nth i l) 0 = 
          fold_right (fun x y => (x+y)) 0 l.
Proof.
intros l d Hdl.
transitivity (\sum_(i < length l) nth i l 0).
now rewrite Hdl.
apply list_fold_right_sum. 
Qed.

Lemma list_fold_right_rnd_sum' : forall (l : list R) d W, d = length l ->
          \big[(fun x y => W (x + y)) / 0%R]_(i < d) (nth i l) 0 = 
          fold_right (fun x y => W (x+y)) 0 l.
Proof.
intros l d W Hdl.
transitivity (\big[(fun x y => W (x + y)) / 0%R]_(i < length l) nth i l 0).
now rewrite Hdl.
apply list_fold_right_rnd_sum.
Qed.


Definition vec_to_list {d} (v : 'cV[R]_d.+1) : list R := 
        map (fun i => v (@inord d i) ord0) (seq 0 d.+1).


Lemma map_seq_nth : forall n (u : nat -> R) len, (n < len)%coq_nat ->
             nth n (map u (seq 0 len)) 0 = u (nth n (seq 0 len) O).
Proof.
intros n v len Hn.
transitivity (nth n (map v (seq 0 len)) (v O)).
apply nth_indep.
rewrite map_length.
now rewrite seq_length.
rewrite map_nth.
reflexivity.
Qed.

Lemma vec_to_list_corr : forall {d} (v : 'cV_d.+1) (i : 'I_d.+1), 
             nth i (vec_to_list v) 0 = v i $0.
Proof.
intros d v i.
rewrite map_seq_nth.
f_equal.
rewrite seq_nth.
transitivity (@inord d i).
f_equal.
rewrite inord_val.
reflexivity.
apply/ltP.
auto with arith.
apply/ltP.
auto with arith.
Qed. 


Lemma vec_to_list_length : forall {d} (v : 'cV[R]_d.+1), 
                  length (vec_to_list v) = d.+1.
Proof.
intros d v.
unfold vec_to_list.
rewrite map_length.
rewrite seq_length.
reflexivity.
Qed. 

Definition F_mat {m n} (A : 'M[R]_(m,n)) F := 
                             forall i j, F (A i j).

Lemma vec_to_list_format : forall {d} (v : 'cV[R]_d.+1) (F : R -> Prop), 
              F_mat v F -> Forall F (vec_to_list v).
Proof. 
intros d v F Hv.
unfold F_mat in Hv.
assert (Hw : forall i, F (v i $0)).
intros i; apply Hv.
unfold vec_to_list.
apply Forall_forall.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (s,(Hs1,Hs2)).
rewrite <- Hs1.
apply Hw.
Qed.  


(** technical lemmas for matrices *)

Lemma mat_apply_fun : forall {n m} (F : ordinal n -> ordinal m -> R) i j, 
           (\matrix_(k,k') (F k k'))%R i j = F i j.
Proof. 
intros n m F i j.
now rewrite !mxE.
Qed.

 
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
