
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


Require Import Reals. 
Require Import List.
Require Import FunctionalExtensionality.
Require Import Lra Lia.
Require Import Flocq.Core.Core.
Require Import Flocq.Prop.Mult_error.
Require Import Flocq.Prop.Plus_error.
Require Import Flocq.Prop.Relative.
Require Import Rstruct Compl Norms RungeKutta FP_prel Error_loc_to_glob.
               


Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool 
               mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.fintype
               mathcomp.ssreflect.finfun mathcomp.ssreflect.prime mathcomp.ssreflect.binomial
               mathcomp.ssreflect.choice mathcomp.ssreflect.bigop mathcomp.algebra.ssralg
               mathcomp.ssreflect.finset mathcomp.fingroup.fingroup mathcomp.ssreflect.seq 
               mathcomp.ssreflect.div mathcomp.algebra.ssrnum mathcomp.algebra.ssralg
               mathcomp.algebra.finalg mathcomp.algebra.matrix.

Require Import Interval.Interval_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.


Notation "a *_sm A" := (map_mx (fun x => (a*x)) A) (at level 40).

Notation "a (x)_s[ W ] A" := (map_mx (fun x => W (a*x)) A) (at level 40).

Notation "A (+)_[ W ]  B" := (rnd_mat (A + B) W) (at level 40).

Notation "A (x)_[ W ] B" := (mulmx_rnd A B W) (at level 45).


Section RK_def.

(** À la Horner implementations of Euler and RK2 *)
Variable d : nat.

Definition Euler (h : R) (A : 'M_d.+1) : Sc d := fun (W : R -> R) => 
    (fun y => (y (+)_[ W ] ((h (x)_s[ W ] (rnd_mat A W)) (x)_[ W ] y))).  

Definition RK2 (h : R) (A : 'M_d.+1) : Sc d := fun W : R -> R => 
    (fun y => (y (+)_[ W ] ((h (x)_s[ W ] (rnd_mat A W)) (x)_[ W ]
                (y (+)_[ W ] (((W (h/2)) (x)_s[ W ] (rnd_mat A W)) (x)_[ W ] y))))). 
 
End RK_def.

Section Error_ana.  

Variable d : nat. 
Variable choice : Z -> bool. 

Variables (beta : radix) (emin prec : Z).
Context { prec_gt_0_ : Prec_gt_0 prec }.
Notation u := (u beta prec).
Notation eta := (eta beta emin). 

Notation r_flt := (r_flt beta emin prec).

Notation format := (generic_format beta (FLT_exp prec emin)).

Notation format_mat := (format_mat beta emin prec).

Hypothesis Hdu : INR d.+1 * u < 1/100.
Hypothesis Hemin : (emin <= 0)%Z.

Ltac preproc_interval := unfold u; 
rewrite bpow_powerRZ;
replace (IZR beta) with 2 by easy;
interval.

Lemma u_lt_cent : u < 1 / 100.
Proof.
apply Rle_lt_trans with (2 := Hdu).
rewrite <- (Rmult_1_l u) at 1.
apply Rmult_le_compat_r.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
clear. 
induction d.
apply Rle_refl.
apply Rle_trans with (1 := IHn).
apply le_INR; lia.
Qed.

Section Error_loc. 

(** Local error bound for Euler *)
Lemma Euler_loc_FLT : forall n y0 h (A : 'M_d.+1), 0 < h ->
  error_loc (Euler h A) n y0 r_flt
  <= (u + (INR d.+1 + (3 + 1/10))*h*u*||| A ||| 
     + ((508 / 100) * (1 + h) * INR d.+1)*eta)
        *\| meth_iter (Euler h A) n y0 r_flt \|
     + ((6/10)* INR d.+1 * eta).
Proof with auto with typeclass_instances.
intros n y0 h A Hh.
unfold error_loc.
assert (Hff : format_mat (meth_iter (Euler h A) n y0 r_flt)).
induction n.
simpl; unfold format_mat.
intros i j.
rewrite !mxE.
apply generic_format_round...
simpl; unfold format_mat. 
intros i j.
rewrite !mxE; simpl.
apply generic_format_round...
revert Hff. 
generalize (meth_iter (Euler h A) n y0 r_flt).
intros y Hyf.
eapply Rle_trans.
unfold Euler.
replace (y (+)_[id] (h *_sm rnd_mat A id (x)_[id] y))
  with ((1%:M + ((h *_sm A) *m 1%:M)) *m y)%R.
pose (A2f := h (x)_s[r_flt] rnd_mat A r_flt).
fold A2f. 
apply build_bound_mult_loc_wk; try easy.
apply Rle_refl.
3 : apply Rle_refl.
5 : {repeat rewrite Rmult_0_l.
rewrite Rplus_0_l.
apply Req_le.
rewrite mul1mx.
rewrite GRing.Theory.addrN.
apply vec_norm_def. }
2 : apply Rle_refl.
3 : apply Rle_refl.
3 : { apply error_mat_const_prod; try easy.
replace (Rabs (h - h)) with 0. 
apply Rle_refl.
rewrite <- Rabs_R0.
f_equal; ring.
instantiate (2 := 1).
instantiate (1 := INR d.+1 * (/2)).
ring_simplify.
unfold matrix_norm.
elim/big_ind2:_ => //.
rewrite Rmult_0_r.
rewrite Rplus_0_l.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
intros x1 x2 y1 y2 H1 H2.
unfold Rmax. 
destruct (Rle_dec x2 y2); 
destruct (Rle_dec x1 y1); try easy.
apply Rle_trans with (1 := H2).
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rle_trans with (1 := H1).
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0. 
assumption.
intros i _.
rewrite <- big_Rplus_scal.
rewrite Rmult_assoc.
rewrite <- big_Rplus_half_const.
elim/big_ind2:_=>//; try lra. 
intros x1 x2 y1 y2 H1 H2; auto with real.
intros j _.
rewrite !mxE.
apply relative_error_N_FLT_strong...
apply Rmult_le_pos; try lra. 
apply bpow_ge_0. }
ring_simplify.
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat. 
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply bpow_ge_0.
apply Rabs_pos.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rabs_pos. 
apply matrix_norm_pos.
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_l 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
ring_simplify.
apply Rabs_pos.
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply pos_INR.
repeat rewrite Rmult_0_l.
rewrite Rplus_0_l.
apply Req_le.
rewrite mul1mx.
rewrite GRing.Theory.addrN.
apply vec_norm_def.
now apply Rlt_le.
rewrite mulmx1.
rewrite mulmxDl.
rewrite mul1mx.
apply/matrixP => i j.
rewrite !mxE.
f_equal.
f_equal; apply functional_extensionality.
unfold rnd_mat; simpl.
intros x; f_equal.
rewrite !mxE.
reflexivity.
repeat rewrite matrix_norm_id.
repeat rewrite Rmult_0_r.
repeat rewrite Rmult_0_l.
repeat rewrite Rplus_0_l.
repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
rewrite Rmult_0_r.
repeat rewrite Rplus_0_l.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply vec_norm_pos.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
apply Rge_le.
rewrite Rplus_assoc.
apply Rle_ge.
apply Rplus_le_compat_l.
replace (||| h *_sm A |||) 
  with (h * ||| A |||).
rewrite Rmult_plus_distr_l.
rewrite <- Rplus_assoc.
apply Rplus_le_compat.
replace (Rabs h) with h.
apply Rle_trans with 
 ((((INR d.+1+1+1 / 100)*u*h) +
 (1+3/100) * (((1+u)*(u*h) +u*h)))*||| A |||).
apply Req_le; ring.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
cut (u <  1/100). 
intros HH.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_r.
apply Rle_trans with 
  ((INR d.+1 + 1 + 1/100 + (1 + 3 / 100) * (2 + u)) * h * u).
apply Req_le; ring.
repeat apply Rmult_le_compat_r.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
lra.
eapply Rle_trans.
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
lra.
apply Rplus_le_compat_l.
apply Rlt_le, HH.
rewrite 2!Rplus_assoc.
apply Rplus_le_compat_l.
interval.
apply Rle_lt_trans with (2 := Hdu).
rewrite <- (Rmult_1_l u) at 1.
apply Rmult_le_compat_r.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rle_trans with (INR 1); try apply Rle_refl.
apply le_INR.
lia.
rewrite Rabs_right; try reflexivity.
lra.
rewrite <- 2!Rmult_assoc.
apply Rmult_le_compat_r.
apply bpow_ge_0.
eapply Rle_trans with (((1 + 3 / 100) *
    ((1 + u) * Rabs h  * / 2 + / 2) )* INR d.+1).
apply Req_le; ring.
apply Rmult_le_compat_r.
apply pos_INR.
rewrite Rabs_right.
eapply Rle_trans.
apply Rmult_le_compat_l.
lra.
repeat apply Rplus_le_compat_r; try lra.
repeat apply Rmult_le_compat_r; try lra.
instantiate (1 := 1 + 1/100).
generalize u_lt_cent; intros Hc.
lra.
lra.
lra.
unfold matrix_norm.
rewrite <- big_Rmax_scal; try lra.
f_equal; apply functional_extensionality.
intros i; f_equal.
rewrite <- big_Rplus_scal; try lra.
f_equal; apply functional_extensionality.
intros j; f_equal.
rewrite !mxE.
rewrite Rabs_mult.
apply Rmult_eq_compat_r.
rewrite Rabs_right; try reflexivity.
lra.
lia.
Qed.

(** Local error bound for RK2 *)
Lemma RK2_loc_FLT_aux : forall h (A : 'M_d.+1) (y : 'cV_d.+1),
 let CA := (17 / 10 + 6 / 10 * (INR d.+1 + 1) * h) * u + 7 / 10 * eta in 
   let Ce := 12 / 10 * INR d.+1 in
        0 < h <= 1 -> format_mat y -> 
  \| y (+)_[r_flt] (r_flt (h / 2) (x)_s[r_flt] rnd_mat A r_flt (x)_[r_flt] y) -
    (1%:M + (h / 2) *_sm A *m 1%:M) *m y \|
  <= (u + CA * ||| A ||| + Ce * eta)*\| y \| 
   + (6/10 * INR d.+1)* eta.
Proof with auto with typeclass_instances.
intros h A y CA Ce Hh Hy.
eapply Rle_trans.
apply build_bound_mult_loc_wk; try easy.
apply Rle_refl.
3 : apply Rle_refl.
5 : {repeat rewrite Rmult_0_l.
rewrite Rplus_0_l.
apply Req_le.
rewrite mul1mx.
rewrite GRing.Theory.addrN.
apply vec_norm_def. }
2 : apply Rle_refl.
3 : apply Rle_refl.
3 : { apply error_mat_const_prod; try easy.
instantiate (1 := u *(h/2) + eta */2).
rewrite <- (Rabs_right (h/2)) at 3.
eapply Rle_trans.
apply relative_error_N_FLT_strong...
apply Req_le; ring.
lra.
instantiate (2 := 1).
instantiate (1 := INR d.+1 * (/2)).
ring_simplify.
unfold matrix_norm.
elim/big_ind2:_ => //.
rewrite Rmult_0_r.
rewrite Rplus_0_l.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
intros x1 x2 y1 y2 H1 H2.
unfold Rmax. 
destruct (Rle_dec x2 y2); 
destruct (Rle_dec x1 y1); try easy.
apply Rle_trans with (1 := H2).
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rle_trans with (1 := H1).
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0. 
assumption.
intros i _.
rewrite <- big_Rplus_scal.
rewrite Rmult_assoc.
rewrite <- big_Rplus_half_const.
elim/big_ind2:_=>//; try lra. 
intros x1 x2 y1 y2 H1 H2; auto with real.
intros j _.
rewrite !mxE.
apply relative_error_N_FLT_strong...
apply Rmult_le_pos; try lra. 
apply bpow_ge_0. }
repeat apply Rmult_le_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rabs_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rabs_pos.
apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rabs_pos. 
apply pos_INR.
apply Rmult_le_pos; try lra.
apply pos_INR.
repeat rewrite Rmult_0_l.
rewrite Rplus_0_l.
apply Req_le.
rewrite mul1mx.
rewrite GRing.Theory.addrN.
apply vec_norm_def.
lra.
repeat rewrite matrix_norm_id.
repeat rewrite Rmult_0_r.
repeat rewrite Rmult_0_l.
repeat rewrite Rplus_0_l.
repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
rewrite Rmult_0_r.
repeat rewrite Rplus_0_l.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply vec_norm_pos.
eapply Rle_trans.
repeat apply Rplus_le_compat.
2 : apply Rle_refl.
2 : apply Rle_refl.
apply Rmult_le_compat.
lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rabs_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rabs_pos. 
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rabs_pos.
apply pos_INR.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rle_refl.
apply Rplus_le_compat.
rewrite Rabs_right.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rle_trans with 
   ((16/10)*u*h + (6/10)*eta).
eapply Rle_trans.
apply Rplus_le_compat.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rplus_le_compat_l.
apply Rlt_le.
apply u_lt_cent.
replace (u * (u * (h / 2) + eta * / 2 + h / 2) +
   (u * (h / 2) + eta * / 2)) with 
  ((1 + u)*(u * (h / 2) + eta * / 2) + u * h /2) 
by field.
apply Rplus_le_compat.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rplus_le_compat_l.
apply Rlt_le, u_lt_cent.
apply Rplus_le_compat.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l. 
rewrite Rmult_assoc.
eapply Rle_trans.
repeat apply Rplus_le_compat.
rewrite Rmult_plus_distr_l.
eapply Rle_trans with 
  ((59/100) * (u * h) + (6/10) * eta).
apply Rplus_le_compat.
field_simplify.
apply Rle_trans with ((u*h)*(10201/20000)).
apply Req_le; field.
apply Rle_trans with ((u*h)* (59 / 100)).
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Req_le; field.
field_simplify.
apply Rle_trans with (eta*(10201/20000)).
apply Req_le; field.
apply Rle_trans with (eta* (6 / 10)).
apply Rmult_le_compat_l.
apply bpow_ge_0.
lra.
apply Req_le; field.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
field_simplify.
cut (0 <= u * h).
lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rle_refl.
lra.
rewrite Rabs_right.
repeat apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply pos_INR.
apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rplus_le_compat.
repeat apply Rmult_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rplus_le_compat_l.
apply Rlt_le, u_lt_cent.
apply Rplus_le_compat_r.
apply Rplus_le_compat_r.
apply Rmult_le_compat.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rlt_le, u_lt_cent.
apply Rle_refl.
apply pos_INR.
lra.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
lra.
replace (||| (h / 2) *_sm A |||) with 
  (/2 * h * ||| A |||).
apply Rle_trans with 
  (u + ((1+ 3/100)*(16/10*u*h+6/10*eta) 
            + ((INR d.+1+1+1/100) * u*/2*h)) * ||| A ||| +
       ((1 + 3/100) * ((1 + 1 / 100) * (1 / 100 * (h / 2) 
         + eta * / 2 + h / 2) 
         * (INR d.+1 * / 2) + INR d.+1 * / 2)) * eta
).
apply Req_le; ring.
rewrite Rplus_assoc.
apply Rge_le.
rewrite Rplus_assoc.
apply Rle_ge.
apply Rplus_le_compat_l.
apply Rplus_le_compat. 
unfold CA.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rle_trans with 
  (((1 + 3 / 100) * (16 / 10  * h) 
  + (INR d.+1 + 1 + 1 / 100) * / 2 * h)*u
  + ((1 + 3 / 100) * 6 / 10) * eta).
apply Req_le; field.
apply Rplus_le_compat.
apply Rmult_le_compat_r.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rle_trans with 
  ((1 + 3 / 100) * (16 / 10) * h +
       ((INR d.+1 + 1 + 1 / 100) * / 2) * h).
lra.
apply Rplus_le_compat.
field_simplify.
eapply Rle_trans.
apply Rmult_le_compat_r.
lra.
apply Rmult_le_compat_l; try lra.
apply Hh; lra.
lra.
apply Rmult_le_compat_r; try lra.
apply Rle_trans with ((INR d.+1 + 1) */2 
  + (INR d.+1*1/10 + 1/10)).
2 : apply Req_le; field.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat_l.
rewrite <- (Rplus_0_l (1/100 */2)).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra.
ring_simplify. 
apply pos_INR.
apply Rmult_le_compat_r.
apply bpow_ge_0.
lra.
apply Rmult_le_compat_r.
apply bpow_ge_0.
unfold Ce. 
rewrite Rmult_plus_distr_l.
replace ((1 + 3 / 100) * (INR d.+1 * / 2))
  with (((1 + 3 / 100) */2)*INR d.+1) by field.
apply Rle_trans with 
  (6 / 10 * INR d.+1 + 6 / 10 * INR d.+1).
2 : apply Req_le; field.
apply Rplus_le_compat.
2 : apply Rmult_le_compat_r; 
  try lra; try apply pos_INR.
rewrite <- Rmult_assoc.
rewrite (Rmult_comm (INR d.+1)).
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
apply pos_INR.
cut (eta <= 1). 
revert Hh; lra.
apply Rle_trans with (bpow beta 0).
apply bpow_le; try easy.
apply Rle_refl.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
f_equal; apply functional_extensionality.
intros i; f_equal.
rewrite <- big_Rplus_scal.
f_equal; apply functional_extensionality.
intros j; f_equal.
rewrite !mxE.
rewrite Rabs_mult.
rewrite (Rabs_right (h/2)); try lra.
rewrite Rmult_comm.
reflexivity.
lra.
lra.
lia. 
Qed.


Lemma RK2_loc_FLT : forall n y0 h (A : 'M_d.+1), 0 < h <= 1 ->
  error_loc (RK2 h A) n y0 r_flt
  <= (u + ((INR d.+1 + 5)*u*h 
           + (6*INR d.+1 + 12/100*INR d.+1^2)*eta)*||| A ||| +
          ((6 + 6/10 + 2*INR d.+1)*u*h + eta)*||| A |||^2 +
          (24/10*INR d.+1^2 + 202/100*INR d.+1)*eta)
        *\| meth_iter (RK2 h A) n y0 r_flt \|
     + (6/10*INR d.+1 + 7/10*INR d.+1^2 + INR d.+1*h*|||A|||)* eta.
Proof with auto with typeclass_instances.
intros n y0 h A Hh.
unfold error_loc.
assert (Hff : format_mat (meth_iter (RK2 h A) n y0 r_flt)).
induction n.
simpl; unfold format_mat.
intros i j.
rewrite !mxE.
apply generic_format_round...
simpl; unfold format_mat. 
intros i j.
rewrite !mxE; simpl.
apply generic_format_round...
revert Hff. 
generalize (meth_iter (RK2 h A) n y0 r_flt).
intros y Hyf.
eapply Rle_trans.
unfold RK2.
replace (y (+)_[id]
(h *_sm rnd_mat A id
 (x)_[id] y (+)_[id]
          ((h / 2) *_sm rnd_mat A id
           (x)_[id] y)))
  with ((1%:M + (((h *_sm A)) *m 
      (1%:M + ((h/2) *_sm A) *m 1%:M))) *m y)%R.
pose (A2f := h (x)_s[r_flt] rnd_mat A r_flt).
pose (A2f':= r_flt (h / 2) (x)_s[r_flt] rnd_mat A r_flt).
fold A2f A2f'. 
apply build_bound_mult_loc_wk; try easy.
apply Rle_refl.
3 : apply Rle_refl.
5 : {
repeat rewrite Rmult_0_l.
rewrite Rplus_0_l.
apply Req_le.
rewrite mul1mx.
rewrite GRing.Theory.addrN.
apply vec_norm_def. }
5 : { apply error_mat_const_prod; try easy.
replace (Rabs (h - h)) with 0. 
apply Rle_refl.
rewrite <- Rabs_R0.
f_equal; ring.
instantiate (2 := 1).
instantiate (1 := INR d.+1 * (/2)).
ring_simplify.
unfold matrix_norm.
elim/big_ind2:_ => //.
rewrite Rmult_0_r.
rewrite Rplus_0_l.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
intros x1 x2 y1 y2 H1 H2.
unfold Rmax. 
destruct (Rle_dec x2 y2); 
destruct (Rle_dec x1 y1); try easy.
apply Rle_trans with (1 := H2).
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rle_trans with (1 := H1).
apply Rplus_le_compat_r. 
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0. 
assumption.
intros i _.
rewrite <- big_Rplus_scal.
rewrite Rmult_assoc.
rewrite <- big_Rplus_half_const.
elim/big_ind2:_=>//; try lra. 
intros x1 x2 y1 y2 H1 H2; auto with real.
intros j _.
rewrite !mxE.
apply relative_error_N_FLT_strong...
apply Rmult_le_pos; try lra. 
apply bpow_ge_0. }
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0) at 1.
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0) at 1.
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0) at 1.
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0) at 1.
apply Rplus_le_compat; try lra.
apply Rabs_pos.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0. 
apply Rabs_pos.
apply matrix_norm_pos.
4 : { now apply RK2_loc_FLT_aux. }
rewrite <- (Rplus_0_r 0).
rewrite <- (Rplus_0_r (0+0)).
repeat apply Rplus_le_compat.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat. 
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
ring_simplify.
apply Rabs_pos.
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply pos_INR.
lra.
rewrite mulmx1.
rewrite mulmxDl.
rewrite mul1mx.
rewrite mulmxDr.
rewrite mulmx1.
replace (rnd_mat A id) with A.
2 : {apply/matrixP => i j.
rewrite !mxE.
reflexivity. }
assert (Hp : 
  forall (x y : 'cV_d.+1), x (+)_[id] y = (x + y)%R).
intros.
apply/matrixP=> i j.
rewrite !mxE.
reflexivity.
rewrite 2!Hp.
assert (Hm : 
  forall {m s p} (x :'M_(m,s)) 
   (y : 'M_(s,p)), x (x)_[id] y = (x *m y)%R).
intros. 
apply/matrixP=> i j.
rewrite !mxE.
reflexivity.
rewrite 2!Hm.
rewrite mulmxDr.
f_equal.
rewrite mulmxDl.
f_equal.
rewrite mulmxA.
reflexivity.
assert (Hb1 : 
  ((1 + u) * (u * h) + u *h <= (2 + 1/100)*u*h)).
rewrite Rmult_plus_distr_r.
eapply Rle_trans.
repeat apply Rplus_le_compat.
apply Rle_refl.
apply Rmult_le_compat_r. 
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rlt_le, u_lt_cent.
apply Rle_refl.
apply Req_le; ring.
assert (Hb2 : 
  ||| 1%:M + (h / 2) *_sm A ||| <= 1 + (h/2)*||| A |||).
eapply Rle_trans. 
apply matrix_norm_triang.
rewrite matrix_norm_id.
apply Req_le; f_equal.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
f_equal; apply functional_extensionality.
intros i; f_equal. 
rewrite <- big_Rplus_scal.
simpl.
f_equal; apply functional_extensionality.
intros j; f_equal.
rewrite !mxE.
rewrite Rabs_mult.
rewrite Rabs_right; try lra.
reflexivity. 
lra.
lra.
lia.
pose (K := (u +
 ((17 / 10 + 6 / 10 * (INR d.+1 + 1) * h)
   * u + 7 / 10 * eta) * ||| A ||| +
 12 / 10 * INR d.+1 * eta)).
fold K.
repeat rewrite matrix_norm_id.
repeat rewrite Rmult_0_r.
repeat rewrite Rmult_0_l.
repeat rewrite Rplus_0_l.
repeat rewrite Rplus_0_r.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
apply Rplus_le_compat.
(* \| y \| *)
apply Rmult_le_compat_r. 
apply vec_norm_pos.
eapply Rle_trans.
repeat apply Rplus_le_compat.
rewrite mulmx1.
rewrite Rabs_right.
rewrite Rmult_plus_distr_l. 
apply Rplus_le_compat.
replace (||| h *_sm A |||) with 
    (h * ||| A |||).
apply Rmult_le_compat. 
lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply matrix_norm_pos.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
apply Rle_refl.
repeat apply Rplus_le_compat.
apply Rmult_le_compat.
apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply matrix_norm_pos.
apply matrix_norm_pos.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Hb1.
apply Hb2.
apply Rle_refl.
apply Rmult_le_compat_r.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Hb1.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
f_equal; apply functional_extensionality.
intros i; f_equal. 
rewrite <- big_Rplus_scal.
simpl.
f_equal; apply functional_extensionality.
intros j; f_equal.
rewrite !mxE.
rewrite Rabs_mult.
rewrite (Rabs_right h); try lra.
reflexivity.
lra.
lra. 
apply Rmult_le_compat_l.
lra.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra.
apply pos_INR. 
apply bpow_ge_0.
apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rplus_le_compat. 
apply Rle_refl.
apply Hb2.
apply Rle_trans with 
  ((6/10)*(1+h)* INR d.+1).
eapply Rle_trans.
rewrite Rmult_assoc.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply Rplus_le_compat_l.
apply Rlt_le, u_lt_cent.
eapply Rle_trans.
apply Rplus_le_compat.
instantiate (1 := 6 / 10 * h * INR d.+1).
field_simplify.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
cut (0 <= (h * INR d.+1)).
lra.
apply Rmult_le_pos; try lra. 
apply pos_INR.
instantiate (1 := 6/10 * INR d.+1).
rewrite Rmult_comm.
apply Rmult_le_compat_r; try lra.
apply pos_INR.
apply Req_le; ring.
apply Rle_refl.
lra.
apply Rle_refl.
replace (||| h *_sm A |||) with (h * ||| A |||).
apply Rmult_le_compat.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
apply matrix_norm_pos.
apply matrix_norm_pos.
apply Rle_refl.
rewrite mulmx1.
apply Hb2.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
f_equal; apply functional_extensionality.
intros i; f_equal. 
rewrite <- big_Rplus_scal.
simpl.
f_equal; apply functional_extensionality.
intros j; f_equal.
rewrite !mxE.
rewrite Rabs_mult.
rewrite (Rabs_right h); try lra.
reflexivity.
lra.
lra.
unfold K.
pose (K' := 
  ((17 / 10 + 6 / 10 * (INR d.+1 + 1) * h) * u + 7 / 10 * eta)).
fold K'.
eapply Rle_trans.
repeat apply Rplus_le_compat.
apply Rmult_le_compat_l.
lra.
repeat apply Rplus_le_compat.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
apply Rplus_le_compat.
apply Rle_refl.
apply Rle_trans with 
  ((1 + 1/100) * u * h^2 * ||| A |||^2).
field_simplify.
rewrite 4!Rmult_assoc.
cut (0 <= (u * (h ^ 2 * ||| A ||| ^ 2))).
lra.
repeat apply Rmult_le_pos; try lra; try apply matrix_norm_pos.
apply bpow_ge_0.
apply Rle_refl.
apply Rle_trans with 
  ((u + 12 / 10 * INR d.+1 * eta)*h*||| A ||| 
   + K' * h * ||| A |||^2).
apply Req_le; ring.
apply Rle_refl.
apply Rmult_le_compat.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR. 
apply bpow_ge_0.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rmult_le_compat_r.
lra.
instantiate (1 := 3/100).
eapply Rle_trans.
apply Rmult_le_compat_l.
lra.
apply Rlt_le, u_lt_cent.
lra.
apply Rle_refl.
apply Rmult_le_compat.
lra.
repeat apply Rmult_le_pos; try lra; 
try apply pos_INR; try apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra.  
apply bpow_ge_0.
apply Rmult_le_pos; try apply matrix_norm_pos.
unfold K'.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra; 
try apply bpow_ge_0.
apply pos_INR.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra; 
try apply matrix_norm_pos.
apply Rle_refl.
apply Rmult_le_compat_r. 
apply bpow_ge_0.
apply Rmult_le_compat_r.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR.
repeat apply Rplus_le_compat.
apply Rlt_le, u_lt_cent.
unfold K'.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rplus_le_compat.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rle_refl.
apply Rlt_le, u_lt_cent.
apply Rle_trans with 1.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat; try lra.
apply bpow_ge_0.
replace 1 with (bpow beta 0) by reflexivity.
now apply bpow_le.
apply Rle_refl.
apply Rle_trans with (12 / 10 * INR d.+1).
rewrite <- (Rmult_1_r (12 / 10 * INR d.+1)) at 2.
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra.
apply pos_INR.
replace 1 with (bpow beta 0) by reflexivity.
now apply bpow_le.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
apply Rle_trans with 
  ((INR d.+1 + 1 + 1 / 100) * u * h * ||| A |||
 + /2 *(INR d.+1 + 1 + 1 / 100) * u * (h^2 * ||| A |||^2)).
field_simplify.
lra. 
apply Rle_refl.
unfold K'.
eapply Rle_trans. 
repeat apply Rplus_le_compat.
apply Rmult_le_compat_l; try lra.
fold K'.
apply Rle_trans with 
  (((3 + 4/100)*u*h  + (1+3/100)*(12/10)* INR d.+1 * h * eta)* ||| A ||| 
   + ((101/100)*u*h^2 + (103/100)*K'*h) * ||| A |||^2).
apply Req_le; field.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat_r; try lra.
apply Rmult_le_compat_r; try apply pos_INR.
instantiate (1 := 13/10); lra.
apply Rmult_le_compat_l.
lra.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply matrix_norm_pos.
apply Rmult_le_pos; try lra. 
apply pos_INR.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR.
repeat apply Rplus_le_compat.
apply Rle_refl.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
lra.
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply Hh.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl. 
apply Rmult_le_compat_r.
apply pos_INR.
apply Rmult_le_compat_l.
lra.
apply Rplus_le_compat_l.  
apply Hh.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
eapply Rle_trans.
repeat apply Rplus_le_compat.
rewrite Rmult_plus_distr_l.
rewrite <- Rmult_assoc.
rewrite <- Rmult_assoc.
apply Rplus_le_compat. 
apply Rmult_le_compat_r.
apply matrix_norm_pos. 
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat. 
instantiate (1 := (314/100)*u*h).
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; try lra.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
instantiate (1 := 14/10 * INR d.+1 * h * eta).
rewrite <- 3!Rmult_assoc.
repeat apply Rmult_le_compat_r; try lra.
apply bpow_ge_0.
apply pos_INR.
unfold K'.
apply Rmult_le_compat_r. 
apply Rmult_le_pos. 
apply matrix_norm_pos.
ring_simplify; apply matrix_norm_pos.
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat.
instantiate (1 := (1 + 5/100)*u*h).
rewrite <- Rmult_assoc.
apply Rmult_le_compat.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; try lra.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
rewrite <- (Rmult_1_r).
apply Rmult_le_compat_l; try lra.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
lra.
rewrite 2!Rmult_plus_distr_l.
apply Rplus_le_compat.
rewrite <- Rmult_assoc.
eapply Rle_trans.
instantiate 
  (1 := 2*((17/10 + 6/10 * (INR d.+1 + 1)*h)*u)).
apply Rmult_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
instantiate (1 := 46/10 + 12/10 * INR d.+1 * h).
field_simplify.
apply Rmult_le_compat_r; try lra.
instantiate (1 := eta).
rewrite <- 2!Rmult_assoc.
rewrite <- Rmult_1_l.
apply Rmult_le_compat_r; try lra. 
apply bpow_ge_0.
apply Rmult_le_compat_l; try lra.
apply Rmult_le_compat.
repeat apply Rmult_le_pos; try lra. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply matrix_norm_pos.
apply pos_INR.
apply bpow_ge_0.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply matrix_norm_pos.
apply Rmult_le_pos; try lra. 
apply pos_INR.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply matrix_norm_pos.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR.  
rewrite Rmult_1_r.
repeat apply Rplus_le_compat.
apply Rle_refl.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
instantiate (1 := 1 + 3/100 + 6/100*INR d.+1).
cut (0 <= INR d.+1).
lra.
apply pos_INR.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
instantiate (1 := 12/10 * INR d.+1).
apply Req_le; field.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
instantiate 
 (1 := 6/10*(INR d.+1 + 1)*u*(h^2*|||A|||^2)).
apply Rmult_le_compat_r.
repeat apply Rmult_le_pos; try lra; 
try apply matrix_norm_pos. 
apply Rmult_le_compat_r. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
cut (0 <= INR d.+1). 
lra.
apply pos_INR.
eapply Rle_trans.
repeat apply Rplus_le_compat.
apply Rmult_le_compat_r. 
apply matrix_norm_pos. 
apply Rle_refl.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; try lra. 
apply matrix_norm_pos. 
ring_simplify; apply matrix_norm_pos.
instantiate (1 := 
  (6 + (12/10)*INR d.+1) * u*h + eta).
apply Rle_trans with 
  ((1 + 5 / 100 + 46 / 10) * u * h + 12 / 10 * INR d.+1 * u * h^2 + eta * h).
apply Req_le; ring.
apply Rplus_le_compat.
eapply Rle_trans.
apply Rplus_le_compat.
apply Rmult_le_compat_r; try lra.
apply Rmult_le_compat_r; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
instantiate (1 := 6).
lra.
apply Rmult_le_compat_l; try lra. 
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
instantiate (1 := h).
rewrite <- (Rmult_1_r h) at 2.
apply Rmult_le_compat_l; try lra.
apply Req_le; ring.
rewrite <- Rmult_1_r.
apply Rmult_le_compat_l; try lra. 
apply bpow_ge_0.
apply Rle_trans with 
  ((1+3/100)*(12 / 10 * INR d.+1)
     * (1+1/100 + 12/10*INR d.+1 + 
  (1+ 3/100 + 6/100 * INR d.+1 + h/2)*||| A |||) * eta).
apply Req_le; ring.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat. 
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rmult_le_pos; try lra; 
try apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply pos_INR.
eapply Rle_trans with (2*INR d.+1).
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; try lra. 
apply pos_INR.
apply Rle_refl.
apply Rplus_le_compat.
apply Rle_refl.
apply Rmult_le_compat_r. 
apply matrix_norm_pos.
repeat apply Rplus_le_compat.
apply Rle_refl. 
apply Rle_refl.
apply Rle_refl.
instantiate (1 := 1).
lra.
apply Rle_refl.
apply Rle_refl.
apply Rle_refl.
rewrite <- Rmult_assoc.
field_simplify.
eapply Rle_trans with 
  (u + ((INR d.+1 + (415/100))*u * h  
    + (406/100 + 14/10 * h)*INR d.+1 * eta 
    + 12/100 * (INR d.+1 ^ 2) * eta)
* ||| A |||
    + (6/10*(1+ INR d.+1)* u * h ^ 2 +
        (12/10 * INR d.+1 + 6)*  u * h + eta) * ||| A |||^2 
    + (24/10* INR d.+1 ^ 2 + 202/100 * INR d.+1)*eta).
apply Req_le; field.
eapply Rle_trans.
repeat apply Rplus_le_compat.
apply Rle_refl.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
repeat apply Rplus_le_compat.
apply Rmult_le_compat_r; try lra. 
apply Rmult_le_compat_r; try lra. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rplus_le_compat_l.
instantiate (1:=5); lra.
apply Rmult_le_compat_r.
apply bpow_ge_0.
apply Rmult_le_compat_r. 
apply pos_INR.
eapply Rle_trans.
apply Rplus_le_compat. 
apply Rle_refl.
apply Rmult_le_compat_l; try lra. 
apply Hh.
instantiate (1 := 6); lra.
apply Rle_refl.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; ring_simplify; apply matrix_norm_pos.
apply Rplus_le_compat_r.
apply Rplus_le_compat_r.
rewrite Rmult_plus_distr_l.
apply Rmult_le_compat.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos; lra.
apply Rle_refl.
instantiate (1 := h).
rewrite <- (Rmult_1_r h) at 2.
apply Rmult_le_compat_l; lra.
apply Rle_refl.
eapply Rle_trans. 
repeat apply Rplus_le_compat.
apply Rle_refl.
instantiate (1 := 
 ((INR d.+1 + 5)*u*h 
  + (6*INR d.+1 + 12/100*INR d.+1^2)*eta)*||| A |||).
apply Req_le; ring.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; ring_simplify; apply matrix_norm_pos.
apply Rplus_le_compat_r.
eapply Rle_trans.
instantiate (1 := (6 + 6/10)*u*h + 18/10*INR d.+1*u*h).
apply Req_le; field.
instantiate (1 := ((6 + 6 / 10) + 2 * INR d.+1)*u*h).
rewrite <- Rmult_plus_distr_r.
rewrite <- Rmult_plus_distr_r.
repeat apply Rmult_le_compat_r; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r; try lra. 
apply pos_INR.
apply Rle_refl.
lra.
apply Rmult_le_compat_r.
apply bpow_ge_0.
eapply Rle_trans.
apply Rplus_le_compat.
apply Rmult_le_compat_l.
lra.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply bpow_ge_0.
apply Rabs_pos.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0. 
apply Rabs_pos.
apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rabs_pos.
apply pos_INR.  
repeat apply Rmult_le_pos; try lra.  
apply pos_INR.
apply matrix_norm_pos.
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rplus_le_compat; try lra.
apply Rplus_le_compat; try lra.
apply Rmult_le_compat_r; try lra.
apply matrix_norm_pos.
rewrite Rabs_right; try lra.
apply Hb1.
rewrite Rabs_right; try lra.
apply Rplus_le_compat_r.
instantiate (1 := 6/10 * INR d.+1).
eapply Rle_trans.
apply Rmult_le_compat_r.
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rplus_le_compat_l.
apply Rlt_le, u_lt_cent.
apply Hh.
ring_simplify.
cut (0 <= INR d.+1).
lra.
apply pos_INR.
instantiate (1 := h * ||| A |||).
apply Req_le.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
f_equal; apply functional_extensionality.
intros i; f_equal. 
rewrite <- big_Rplus_scal.
simpl.
f_equal; apply functional_extensionality.
intros j; f_equal.
rewrite !mxE.
rewrite Rabs_mult.
rewrite (Rabs_right h); try lra.
reflexivity.
lra.
lra.
apply Rle_refl.
apply Rle_refl.
eapply Rle_trans. 
instantiate (1 := 
  6/10 * INR d.+1 + 7/10 * INR d.+1^2 
  + INR d.+1*h*|||A|||).
rewrite Rplus_comm.
rewrite Rplus_assoc.
apply Rge_le.
rewrite Rplus_assoc.
apply Rle_ge.
apply Rplus_le_compat_l.
field_simplify ((1 + 3 / 100) *
(((2 + 1 / 100) * u * h * ||| A ||| +
  (6 / 10 * INR d.+1 + INR d.+1 * / 2 +
   h * ||| A |||)) * (6 / 10 * INR d.+1))).
rewrite <- Rmult_plus_distr_r.
rewrite <- Rmult_plus_distr_r.
apply Rle_trans with 
 ((((2484360/2000000) * u * h 
  + (1236000/2000000)*h)*||| A |||*INR d.+1 
    + (1359600/ 2000000) * INR d.+1 ^ 2)).
apply Req_le; field.
rewrite Rplus_comm.
apply Rplus_le_compat.
apply Rmult_le_compat_r.
apply Rmult_le_pos; ring_simplify; apply pos_INR.
lra.
rewrite Rmult_comm.
apply Rge_le.
rewrite Rmult_assoc.
apply Rle_ge.
apply Rmult_le_compat_l.
apply pos_INR.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
rewrite <- Rmult_plus_distr_r.
rewrite <- (Rmult_1_l h) at 2.
apply Rmult_le_compat_r; try lra.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l; try lra.
apply Rlt_le, u_lt_cent.
lra.
apply Rle_refl.
lia. 
Qed. 

 

End Error_loc.

Section Error_glob. 

(** Global error bound for Euler *)

Theorem Euler_glob_FLT : forall N y0 h (A : 'M_d.+1),
  let C := (u + (INR d.+1 + (3 + 1/10))*h*u*||| A ||| 
     + ((508 / 100) * (1 + h) * INR d.+1)*eta) in 
  let K := Rmax (C + |||1%:M + h *_sm A *m 1%:M |||) 1 in
        0 < h -> 0 < ||| A ||| -> 
        error_glob (Euler h A) N y0 r_flt
             <= (C + ||| 1%:M + h *_sm A *m 1%:M |||) ^ N *
                 (\| rnd_mat y0 (round beta (FLT_exp emin prec) ZnearestE) - y0 \| +
                     INR N * C * \| y0 \| /
                  (C + ||| 1%:M + h *_sm A *m 1%:M |||)) +
               INR N*K^N * 6 / 10 * INR d.+1 * eta.
Proof with auto with typeclass_instances.
intros N y0 h A C K Hh HA.
eapply Rle_trans.
apply error_loc_to_glob...
4 : {
intros n.
now apply Euler_loc_FLT.
}
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_compat; try lra.
apply Rmult_lt_0_compat; try lra.
apply bpow_gt_0.
repeat apply Rmult_lt_0_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_compat; try lra.
apply Rle_lt_trans with (INR 0). 
apply Rle_refl. 
apply lt_INR; lia.
apply bpow_gt_0.
repeat apply Rmult_lt_0_compat; try lra.
apply Rle_lt_trans with (INR 0). 
apply Rle_refl. 
apply lt_INR; lia.
apply bpow_gt_0.
repeat apply Rmult_lt_0_compat; try lra.
apply Rle_lt_trans with (INR 0). 
apply Rle_refl.
apply lt_INR; lia.
apply bpow_gt_0. 
intros y.
unfold W_Id, Euler.
Existential 2 := (1%:M + (h *_sm A) *m 1%:M)%R.
rewrite mulmx1.
rewrite mulmxDl.
rewrite mul1mx.
apply/matrixP => i j.
rewrite !mxE.
f_equal.
f_equal; apply functional_extensionality.
unfold rnd_mat; simpl.
intros x; f_equal.
rewrite !mxE.
reflexivity.
apply Req_le.
unfold K, C; lra.
Qed.

(** Global error bound for Euler *)

Theorem RK2_glob_FLT :  forall N y0 h (A : 'M_d.+1),
        let C := (u + ((INR d.+1 + 5)*u*h 
           + (6*INR d.+1 + 12/100*INR d.+1^2)*eta)*||| A ||| +
          ((6 + 6/10 + 2*INR d.+1)*u*h + eta)*||| A |||^2 +
          (24/10*INR d.+1^2 + 202/100*INR d.+1)*eta) in
        let K := Rmax (C + ||| 1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A) |||) 1 in
        0 < h <= 1 -> 0 < ||| A ||| -> 
        error_glob (RK2 h A) N y0 r_flt
             <= (C + ||| 1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A) |||) ^ N *
                 (\| rnd_mat y0 (round beta (FLT_exp emin prec) ZnearestE) - y0 \| +
                     INR N * C * \| y0 \| /
                  (C + ||| 1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A) |||)) +
                INR N*K^N * (6/10*INR d.+1 + 7/10*INR d.+1^2 + INR d.+1*h*|||A|||) * eta.
Proof with auto with typeclass_instances.
intros N y0 h A C K Hh HA.
eapply Rle_trans.
apply error_loc_to_glob...
4 : {
intros n.
now apply RK2_loc_FLT.
}
apply Rlt_le_trans with u.
apply Rmult_lt_0_compat; try lra.
apply bpow_gt_0.
rewrite <- (Rplus_0_r u) at 1.
rewrite 2!Rplus_assoc.
apply Rplus_le_compat_l.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply pos_INR.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra.
apply pos_INR.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply pos_INR.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0. 
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply pos_INR. 
apply Rmult_le_pos; try lra. 
apply pos_INR. 
apply bpow_ge_0.
apply Rmult_lt_0_compat; try lra.
apply Rlt_le_trans with (6 / 10 * INR d.+1); try lra.
apply Rmult_lt_0_compat; try lra.
replace 0 with (INR 0) by reflexivity.
apply lt_INR; lia.
apply Rle_trans with (6 / 10 * INR d.+1 + 0 + 0).
lra.
repeat apply Rplus_le_compat; try lra;
repeat apply Rmult_le_pos; try lra;
apply pos_INR.
apply bpow_gt_0.
intros y.
unfold W_Id, RK2.
Existential 2 := 
  (1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A))%R.
rewrite mulmxDl.
replace (rnd_mat A id) with A.
2 : {apply/matrixP => i j.
rewrite !mxE.
reflexivity. }
assert (Hp : 
  forall (x y : 'cV_d.+1), x (+)_[id] y = (x + y)%R).
intros.
apply/matrixP=> i j.
rewrite !mxE.
reflexivity.
rewrite 2!Hp.
assert (Hm : 
  forall {m s p} (x :'M_(m,s)) 
   (y : 'M_(s,p)), x (x)_[id] y = (x *m y)%R).
intros. 
apply/matrixP=> i j.
rewrite !mxE.
reflexivity.
rewrite 2!Hm.
rewrite mulmxDr.
rewrite mulmxDl.
rewrite mul1mx.
transitivity 
  (y + (h *_sm A *m y + (h ^ 2 / 2) *_sm A *m A *m y))%R.
f_equal.
f_equal.
rewrite mulmxA.
f_equal.
apply/matrixP=> i j.
rewrite !mxE.
f_equal; apply functional_extensionality.
f_equal; intros t.
f_equal.
rewrite !mxE.
rewrite <- Rmult_assoc.
apply Rmult_eq_compat_r.
field.
apply/matrixP=> i j.
rewrite !mxE.
rewrite <- Rplus_assoc.
reflexivity.
unfold K, C; lra.
Qed.

End Error_glob. 

End Error_ana.


