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
Require Import Epsilon FunctionalExtensionality Lra.
From mathcomp 
Require Import all_ssreflect fingroup ssrnum ssralg finalg matrix. 
Require Import Rstruct Compl Norms FP_prel RungeKutta.
From Flocq.Core 
Require Import Core. 
From Flocq.Prop 
Require Import Mult_error Plus_error Relative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

Section error_glob_loc_flt.

Variable beta : radix.
Variables emin prec : Z. 

Context { prec_pos : Prec_gt_0 prec }.
Variable choice : Z -> bool. 
(*
Definition u := bpow beta (-prec).
Definition eta := bpow beta (emin).
*)
Notation r_flt :=
         (round beta (FLT_exp emin prec) (Znearest choice)). 
Notation format := (generic_format beta (FLT_exp emin prec)).
Notation format_mat := (format_mat prec).
Notation rnd_mat_flt := (fun x => rnd_mat x r_flt).
Notation rnd_vec_matrix_product := (mulmx_rnd prec choice). 


(** From local to global error *)

Variables (d : nat) (C D : R) (Cpos : 0 < C) (Dpos : 0 < D)
          (meth : Sc d) (y0 : 'cV[R]_d.+1) 
          (Rmeth : 'M_d.+1) (is_RKm : is_RK_lin meth Rmeth).

Notation eps0 := (\| (rnd_mat_flt y0 - y0) \|).


Lemma error_loc_glob_aux (N : nat) (W : R -> R) :
              error_glob meth (S N) y0 W
           <= error_loc meth N y0 W + 
             (||| Rmeth ||| * error_glob meth N y0 W).
Proof.
unfold error_glob.
replace (meth_iter meth (S N) y0 W - 
         meth_iter meth (S N) y0 (fun x : R => x))%Ri with
        ((meth_iter meth (S N) y0 W - 
          (meth (fun x => x) (meth_iter meth N y0 W))) +
         ((meth (fun x => x) (meth_iter meth N y0 W) -
          meth_iter meth (S N) y0 (fun x : R => x))))%Ri. 
apply Rle_trans with (vec_norm (meth_iter meth (S N) y0 W -
          meth (fun x : R => x) (meth_iter meth N y0 W)) +
             vec_norm (meth (fun x : R => x) (meth_iter meth N y0 W) -
             meth_iter meth (S N) y0 (fun x : R => x))).
apply vec_norm_triang.
apply Rplus_le_compat.
apply Rle_refl.
simpl; replace (vec_norm
     (meth (fun x : R => x) 
          (meth_iter meth N y0 W) -
     meth (fun x : R => x)
          (meth_iter meth N y0 
         (fun x : R => x)))) with 
         (vec_norm
         (Rmeth *m (meth_iter meth N y0 W) -
          Rmeth *m (meth_iter meth N y0 
                                 (fun x : R => x)))).
rewrite <- mulmxBr.
apply mx_vec_norm_submult.
simpl in *; unfold is_RK_lin, W_Id in *.
repeat rewrite is_RKm.
reflexivity.
transitivity ((meth_iter meth N.+1 y0 W -
         meth_iter meth N.+1 y0 ssrfun.id) +
        (meth ssrfun.id (meth_iter meth N y0 W)
        - meth ssrfun.id (meth_iter meth N y0 W)))%Ri.
repeat rewrite GRing.addrA.
rewrite GRing.addrC.
rewrite <- GRing.addrA.
rewrite (GRing.addrC (- meth ssrfun.id 
             (meth_iter meth N y0 W))%Ri _).
rewrite GRing.Theory.addrN.
rewrite GRing.Theory.addr0.
rewrite <- GRing.addrA.
rewrite GRing.Theory.addrN.
rewrite GRing.Theory.addr0.
now rewrite GRing.addrC.
transitivity ((meth_iter meth N.+1 y0 W - 
     meth_iter meth N.+1 y0 ssrfun.id) + 0)%Ri.
f_equal.
now rewrite GRing.Theory.addrN.
now rewrite GRing.Theory.addr0.
Qed.


Theorem error_loc_to_glob (N : nat) : 
  let K := Rmax (C + ||| Rmeth |||) 1 in
    (forall n:nat, (error_loc meth n y0 r_flt) <= 
        C * (vec_norm (meth_iter meth n y0 r_flt)) + D) -> 
        error_glob meth N y0 r_flt <= 
       (C + ||| Rmeth |||)^N * (eps0 + 
         (INR N* ((C*\| y0 \|)/(C+||| Rmeth |||)))) + INR N*K^N*D.
Proof.
intros K Hn.
induction N.
+ unfold INR; ring_simplify.
  unfold error_glob.
  simpl.
  unfold rnd_mat.
  pose (J := \| \matrix_(i, j) r_flt (y0 i j) - y0 \|).
  fold J.
  apply Rle_trans with J.
  unfold J.
  apply Req_le; f_equal.
  f_equal.
  apply/matrixP=> i j.
  rewrite !mxE; reflexivity.
  lra.
+ assert (H : error_glob meth (S N) y0 r_flt <=
    (C + matrix_norm Rmeth)* error_glob meth N y0 r_flt
   + C*(matrix_norm Rmeth)^N * (vec_norm y0) + D).
  replace ((C + matrix_norm Rmeth) * 
            error_glob meth N y0 r_flt 
           + C * (matrix_norm Rmeth) ^ N * vec_norm y0) with 
          (C*error_glob meth N y0 r_flt + 
           C * (matrix_norm Rmeth) ^ N * vec_norm y0 + 
           matrix_norm Rmeth * (error_glob meth N y0 r_flt)) 
  by ring.
  apply Rle_trans with 
    (error_loc meth N y0 r_flt + 
    (matrix_norm Rmeth) * error_glob meth N y0 r_flt).
  apply error_loc_glob_aux.
  assert (H2 : error_loc meth N y0 r_flt 
     <= C* error_glob meth N y0 r_flt +
         C * (matrix_norm Rmeth)^N * vec_norm y0 + D).
  apply Rle_trans with (C * ((error_glob meth N y0 r_flt) +
          vec_norm (meth_iter meth N y0 (fun x : R => x))) + D).
  unfold error_glob.
  ring_simplify.
  apply Rle_trans with 
          (C * vec_norm (meth_iter meth N y0 r_flt) + D).
  apply Hn.
  apply Rplus_le_compat_r.
  apply Rle_trans with (C * (vec_norm
  (meth_iter meth N y0 r_flt -
   meth_iter meth N y0 (fun x : R => x) +
   meth_iter meth N y0 (fun x : R => x)))).
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
  apply vec_norm_triang.
  apply Rplus_le_compat_r.
  replace ((C + matrix_norm Rmeth) * 
     error_glob meth N y0 r_flt 
     + C * (matrix_norm Rmeth) ^ N * vec_norm y0) with 
     (C* error_glob meth N y0 r_flt +
     matrix_norm Rmeth * error_glob meth N y0 r_flt +
     C * matrix_norm Rmeth ^ N * vec_norm y0) by ring.
  rewrite Rmult_plus_distr_l.
  apply Rplus_le_compat_l.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  now apply Rlt_le.
  now apply is_RK_Rmeth.
  apply Rle_trans with (C * error_glob meth N y0 r_flt 
   + C * ||| Rmeth ||| ^ N * \| y0 \| +  D + 
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
    ((C + ||| Rmeth |||) * ((C + ||| Rmeth |||) ^ N * 
    (\| rnd_mat y0 r_flt - y0 \| + INR N * (C * \| y0 \| 
                  / (C + ||| Rmeth |||))))
     + C*||| Rmeth |||^N * \|y0\| + ((C+||| Rmeth |||)*INR N*K^N*D+D)).
  apply Req_le; ring.
  apply Rplus_le_compat.
  pose (G := (C * \| y0 \| / (C + ||| Rmeth |||))).
  fold G.
  pose (P := C + ||| Rmeth |||); fold P.
  apply Rle_trans with    
    ((P ^ (N+1) * (\| rnd_mat y0 r_flt - y0 \| + INR N * G)) 
 + C*|||Rmeth|||^N*\|y0\|). 
  rewrite <- Rmult_assoc.
  apply Req_le; rewrite tech_pow_Rmult.
  repeat f_equal.
  now rewrite addn1.
  rewrite addn1.
  apply Rle_trans with 
    (P ^ N.+1 * (\| rnd_mat y0 r_flt - y0 \| + INR N * G)
      + P^ N.+1 * G).
  2: { rewrite S_INR. apply Req_le; ring. }
  apply Rplus_le_compat_l.
  unfold P, G.
  apply Rle_trans with 
       ((C+|||Rmeth|||) ^ N*(C*\|y0\|)).
  2 : { 
  replace ((C + ||| Rmeth |||) ^ N.+1) with 
    ((C + ||| Rmeth |||)*(C + ||| Rmeth |||) ^ N).
  apply Req_le; field.
  apply Rgt_not_eq. 
  apply Rlt_gt.
  apply Rlt_le_trans with C; try easy.
  rewrite <- (Rplus_0_r C) at 1.
  apply Rplus_le_compat_l.
  apply matrix_norm_pos.
  rewrite tech_pow_Rmult.
  ring. }
  apply Rle_trans with 
    (C*(C + ||| Rmeth |||) ^ N *\| y0 \|).
  2 : apply Req_le; ring.
  apply Rmult_le_compat_r.
  apply vec_norm_pos.
  apply Rmult_le_compat_l.
  lra.
  apply pow_incr.
  split.
  apply matrix_norm_pos.
  rewrite <- (Rplus_0_l (||| Rmeth |||)) at 1.
  apply Rplus_le_compat_r.
  lra. 
  apply Rle_trans with (K * INR N * K^N * D + K*D).
  apply Rplus_le_compat; try lra.
  apply Rmult_le_compat; try lra.
  repeat apply Rmult_le_pos; try lra.
  rewrite <- (Rplus_0_r 0).
  apply Rplus_le_compat; try lra; try apply matrix_norm_pos.
  apply pos_INR.
  apply pow_le.
  apply Rle_trans with 1; try lra.
  apply Rmax_r.
  apply Rmult_le_compat_r.
  apply pow_le; try lra.
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
  apply Req_le; rewrite tech_pow_Rmult.
  reflexivity.
  apply Rle_trans with (INR N * K ^ N.+1 * D + K * D). 
  apply Req_le; ring.
  rewrite <- tech_pow_Rmult.
  rewrite <- addn1. 
  rewrite plus_INR.
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
  apply pow_R1_Rle.
  apply Rmax_r.
Qed.

End error_glob_loc_flt.
