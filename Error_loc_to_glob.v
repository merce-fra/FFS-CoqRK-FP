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
Require Import all_ssreflect ssralg zmodp matrix. 
Require Import Rstruct Compl Norms FP_prel RungeKutta.
From Flocq.Core Require Import Core. 

Set Implicit Arguments.

Section error_glob_loc_flt.

Notation "x ^ y" := (Rpow_def.pow x y).

Variable beta : radix.
Variables emin prec : Z. 

Context { prec_pos : Prec_gt_0 prec }.
Variable choice : Z -> bool. 

Notation r_flt :=
         (round beta (FLT_exp emin prec) (Znearest choice)). 
Notation format := (generic_format beta (FLT_exp emin prec)).
Notation format_mat := (format_mat prec).
Notation rnd_mat_flt := (fun x => rnd_mat x r_flt).

(** From local to global error *)

Variables (d : nat) (C D : R) (Cpos : 0 < C) (Dpos : 0 <= D)
          (meth : Sc d) (y0 : 'cV[R]_d) 
          (Rmeth : 'M_d) (is_RKm : is_RK_lin meth Rmeth).

Notation eps0 := (||| (rnd_mat_flt y0 - y0) |||).

Lemma error_loc_glob_aux (N : nat) (W : R -> R) :
  error_glob meth (S N) y0 W
  <= error_loc meth N y0 W +  (||| Rmeth ||| * error_glob meth N y0 W).
Proof.
unfold error_glob.
replace
  (meth_iter meth (S N) y0 W -  meth_iter meth (S N) y0 id)%Ri
  with
  ((meth_iter meth (S N) y0 W - (meth id (meth_iter meth N y0 W)))
   + ((meth id (meth_iter meth N y0 W) - meth_iter meth (S N) y0 id)))%Ri.
eapply Rle_trans.
apply matrix_norm_triang. 
apply Rplus_le_compat.
apply Rle_refl.
simpl in *; unfold is_RK_lin, W_Id in *.
repeat rewrite is_RKm.
eapply Rle_trans.
2: apply norm_submult. 
apply Req_le; now rewrite mulmxBr.
apply/matrixP=> i j.
rewrite !mxE; Rring_tac; lra.
Qed.


Theorem error_loc_to_glob (N : nat) : 
  let K := Rmax (C + ||| Rmeth |||) 1 in
    (forall n:nat, (error_loc meth n y0 r_flt) <= 
        C * (||| (meth_iter meth n y0 r_flt) ||| ) + D) -> 
        error_glob meth N y0 r_flt <= 
       (C + ||| Rmeth |||)^N * (eps0 + 
         (INR N* ((C*||| y0 |||)/(C+||| Rmeth |||)))) + INR N*K^N*D.
Proof.
intros K Hn.
induction N.
+ unfold INR; ring_simplify.
  unfold error_glob; simpl.
  apply Req_le; repeat f_equal; now apply/matrixP=> i j; rewrite !mxE.
+ assert (H : error_glob meth (S N) y0 r_flt <=
    (C + matrix_norm Rmeth)* error_glob meth N y0 r_flt
   + C*(matrix_norm Rmeth)^N * ||| y0 ||| + D).
  replace ((C + matrix_norm Rmeth) * 
            error_glob meth N y0 r_flt 
           + C * (matrix_norm Rmeth) ^ N * ||| y0 |||) with 
          (C*error_glob meth N y0 r_flt + 
           C * (matrix_norm Rmeth) ^ N * ||| y0 ||| + 
           matrix_norm Rmeth * (error_glob meth N y0 r_flt)) 
  by ring.
  apply Rle_trans with 
    (error_loc meth N y0 r_flt + 
    (matrix_norm Rmeth) * error_glob meth N y0 r_flt).
  apply error_loc_glob_aux.
  assert (H2 : error_loc meth N y0 r_flt 
     <= C* error_glob meth N y0 r_flt +
         C * (matrix_norm Rmeth)^N * ||| y0 ||| + D).
  apply Rle_trans with (C * ((error_glob meth N y0 r_flt) +
          ||| (meth_iter meth N y0 (fun x : R => x)) |||) + D).
  unfold error_glob.
  ring_simplify.
  apply Rle_trans with 
          (C * ||| (meth_iter meth N y0 r_flt) ||| + D).
  apply Hn.
  apply Rplus_le_compat_r.
  apply Rle_trans with (C * (|||
  (meth_iter meth N y0 r_flt -
   meth_iter meth N y0 (fun x : R => x) +
   meth_iter meth N y0 (fun x : R => x)) ||| )).
  apply Rmult_le_compat_l.
  now apply Rlt_le.
  apply Req_le. 
  replace ((meth_iter meth N y0 r_flt) -
     (meth_iter meth N y0 (fun x : R => x)) +
     (meth_iter meth N y0 (fun x : R => x)))%Ri with 
       (meth_iter meth N y0 r_flt).
  ring.
  rewrite GRing.Theory.addrNK.
  reflexivity.
  rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  now apply Rlt_le.
  apply matrix_norm_triang.
  apply Rplus_le_compat_r.
  replace ((C + ||| Rmeth |||) * 
     error_glob meth N y0 r_flt 
     + C * (matrix_norm Rmeth) ^ N * ||| y0 |||) with 
     (C* error_glob meth N y0 r_flt +
     matrix_norm Rmeth * error_glob meth N y0 r_flt +
     C * matrix_norm Rmeth ^ N * ||| y0 |||) by ring.
  rewrite Rmult_plus_distr_l.
  apply Rplus_le_compat_l.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  now apply Rlt_le.
  now apply is_RK_Rmeth.
  apply Rle_trans with (C * error_glob meth N y0 r_flt 
   + C * ||| Rmeth ||| ^ N * ||| y0 ||| +  D + 
   ||| Rmeth ||| * error_glob meth N y0 r_flt).
  2: apply Req_le; ring.
  apply Rplus_le_compat_r.
  trivial.
  (* *)
  apply Rle_trans with (1 := H).
  eapply Rle_trans.
  repeat apply Rplus_le_compat_r.
  apply Rmult_le_compat_l.
  rewrite <- (Rplus_0_r 0).
  apply Rplus_le_compat; try lra. 
  apply matrix_norm_pos.
  apply IHN.
  apply Rle_trans with
    ((C + ||| Rmeth |||) * ((C + ||| Rmeth |||)^N *
    (||| rnd_mat y0 r_flt - y0 ||| + INR N * (C * ||| y0 ||| / (C + ||| Rmeth |||))))
     + C*||| Rmeth |||^N * |||y0||| + ((C+||| Rmeth |||)*INR N*K^N*D+D)).
  apply Req_le; ring.
  apply Rplus_le_compat.
  pose (G := (C * ||| y0 ||| / (C + ||| Rmeth |||))).
  fold G.
  pose (P := C + ||| Rmeth |||); fold P.
  apply Rle_trans with    
    ((P ^ (N+1) * (||| rnd_mat y0 r_flt - y0 ||| + INR N * G)) 
 + C*|||Rmeth|||^N* ||| y0 |||). 
  rewrite <- Rmult_assoc.
  apply Req_le; rewrite Rfunctions.tech_pow_Rmult.
  repeat f_equal.
  now rewrite addn1.
  rewrite addn1.
  apply Rle_trans with 
    (P ^ N.+1 * (||| rnd_mat y0 r_flt - y0 ||| + INR N * G)
      + P^ N.+1 * G).
  2: { rewrite S_INR. apply Req_le; ring. }
  apply Rplus_le_compat_l.
  unfold P, G.
  apply Rle_trans with 
       ((C+|||Rmeth|||) ^ N*(C*|||y0|||)).
  2 : { 
  replace ((C + ||| Rmeth |||) ^ N.+1) with 
    ((C + ||| Rmeth |||)*(C + ||| Rmeth |||) ^ N).
  apply Req_le; field.
  apply Rgt_not_eq. 
  apply Rlt_gt.
  apply Rlt_le_trans with C; try easy.
  rewrite <- Rplus_0_r at 1. 
  apply Rplus_le_compat_l.
  apply matrix_norm_pos.
  rewrite Rfunctions.tech_pow_Rmult.
  ring. }
  apply Rle_trans with 
    (C*(C + ||| Rmeth |||) ^ N *||| y0 |||).
  2 : apply Req_le; ring.
  apply Rmult_le_compat_r.
  apply matrix_norm_pos.
  apply Rmult_le_compat_l.
  lra.
  apply Rfunctions.pow_incr.
  split.
  apply matrix_norm_pos.
  rewrite <- (Rplus_0_l (||| Rmeth |||)) at 1.
  apply Rplus_le_compat_r.
  lra. 
  apply Rle_trans with (K * INR N * K^N * D + K*D).
  apply Rplus_le_compat; try lra.
  apply Rmult_le_compat; try lra.
  repeat apply Rmult_le_pos; try lra.
  apply Rle_trans with C; try lra.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat_l.
  apply matrix_norm_pos.
  apply pos_INR.
  apply Rfunctions.pow_le.
  apply Rle_trans with 1; try lra.
  apply Rmax_r.
  apply Rmult_le_compat_r.
  apply Rfunctions.pow_le; try lra.
  apply Rle_trans with 1; try lra. 
  apply Rmax_r.
  apply Rmult_le_compat_r. 
  apply pos_INR.
  apply Rmax_l.
  rewrite <- (Rmult_1_l D) at 1.
  apply Rmult_le_compat_r; try lra.
  apply Rmax_r.
  apply Rle_trans with (K ^ N.+1 * INR N * D + K * D).
  apply Rle_trans with (K * K ^ N * INR N * D + K * D). 
  apply Req_le; ring.
  apply Req_le; rewrite Rfunctions.tech_pow_Rmult.
  reflexivity.
  apply Rle_trans with (INR N * K ^ N.+1 * D + K * D). 
  apply Req_le; ring.
  rewrite <- Rfunctions.tech_pow_Rmult.
  rewrite <- addn1. 
  rewrite plus_INR.
  auto with real.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  lra.
  apply Rle_trans with ((K * K ^ N) * D).
  2: apply Req_le; unfold INR; ring.
  apply Rmult_le_compat_r; try lra. 
  rewrite <- (Rmult_1_r K) at 1.
  apply Rmult_le_compat_l. 
  apply Rle_trans with 1; try lra.
  apply Rmax_r.
  apply Rfunctions.pow_R1_Rle.
  apply Rmax_r.
Qed.

End error_glob_loc_flt.
