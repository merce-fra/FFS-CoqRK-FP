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


Require Import Reals Lra Lia.

From Flocq.Core 
Require Import Core. 

From mathcomp
Require Import all_ssreflect ssralg matrix.

Require Import Rstruct RungeKutta FP_prel Error_loc_to_glob Compl Norms. 

Set Implicit Arguments.


Variable d : nat. 
Variable choice : Z -> bool. 

Variables (beta : radix) (emin prec : Z).
Context { prec_gt_0_ : Prec_gt_0 prec }.
Notation u := (u beta prec).
Notation eta := (eta beta emin). 

Notation r_flt := (r_flt beta emin prec).

Notation format := (generic_format beta (FLT_exp prec emin)).

Notation format_mat := (format_mat beta emin prec).
Hypothesis Hdu : INR d * u < 1/100.
Hypothesis Hemin : (emin <= 0)%Z.
Hypothesis d_NZ : (1 <= d)%coq_nat.

Lemma u_lt_cent : u < 1 / 100.
Proof.
  apply Rle_lt_trans with (2 := Hdu).
  rewrite <- (Rmult_1_l (u)) at 1.
  apply Rmult_le_compat_r.
  apply Rmult_le_pos; try lra. 
  apply bpow_ge_0.
  clear.
  apply (le_INR 1).
  apply d_NZ.
Qed.

Lemma u_le_cent : u <= 1 / 100.
Proof.
  apply Rlt_le; apply u_lt_cent.
Qed.

Lemma one_plus_u_bnd : 1 + u <= 1.01.
Proof.
  generalize u_le_cent; lra.
Qed.

Lemma u2_le_cent : u^2 <= (1 / 100)*(u).
Proof.
  simpl; rewrite Rmult_1_r.
  apply Rmult_le_compat_r.
  apply Rmult_le_pos; try lra.
  apply bpow_ge_0.
  now apply Rlt_le, u_lt_cent.
Qed.

Lemma eta_le_1 : eta <= 1.
Proof. 
  unfold eta.
  apply Rle_trans with (bpow beta 0); try lra.
  apply bpow_le; auto with real.
  apply Hemin.
  auto with real.
Qed. 
(*
Lemma Rabs_R0_ext :
  forall n f (i j : 'I_n), f i j = 0 -> Rabs (f i j) = 0.
Proof.
  intros n f i j Hx; rewrite Hx; now rewrite Rabs_R0.
Qed.
*)
Lemma meth_iter_format : forall n (M : Sc d) y0,
    (forall x, format_mat x -> format_mat (M r_flt x)) ->
    format_mat (meth_iter M n y0 r_flt).
Proof with auto with typeclass_instances.
  intros n M y0 Hp. 
  induction n.
  simpl; unfold format_mat.
  intros i j.
  rewrite !mxE.
  apply generic_format_round...
  simpl; unfold format_mat. 
  intros i j.
  apply Hp.
  apply IHn.
Qed.


Ltac simpl_arith :=
  repeat rewrite matrix_norm_id;
  repeat rewrite Rplus_0_r;
  repeat rewrite Rplus_0_l; 
  repeat rewrite Rmult_1_r;
  repeat rewrite Rmult_1_l;
  repeat rewrite Rmult_0_l;
  repeat rewrite Rmult_0_r;
  repeat rewrite Rabs_right; try lra.

Lemma subst_le : forall x y (f : R -> R),
    x <= y -> (forall a b, a <= b -> f a <= f b) -> (f x <= f y).  
Proof.
  intros x y f Hxy Hf.
  now apply Hf.
Qed.

Ltac subst_le g H low :=
  let f' := fresh "f" in
  set (f' := fun x:R => g x);
  apply Rle_trans with (f' low);
  [ unfold f' |
    apply subst_le;
    [ apply H | 
      unfold f'; intros a b Hab;
      repeat apply Rplus_le_compat; try auto with real;
      repeat apply Rmult_le_compat_r; try lra]];
  try lra.

Lemma sum_2_le_pos : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
  intros x y Hx Hy.
  lra.
Qed.

Lemma sum_3_le_pos : forall x y z, 0 <= x -> 0 <= y -> 0 <= z -> 0 <= x + y + z.
Proof.
  intros x y z Hx Hy Hz.
  lra.
Qed.
  
Ltac autosolve :=
  try repeat apply Rmult_le_pos;
  try lra; try auto with real;
  try ring;
  try apply bpow_ge_0;
  try apply matrix_norm_pos;
  try apply pos_INR.

Ltac pos_auto :=
  match goal with
  | |- 0 <= ?a + ?b => apply sum_2_le_pos; try autosolve
  | |- 0 <= ?a + ?b + ?c => apply sum_3_le_pos; try autosolve
  end.

Ltac format_meth M n y0 Hff:=
  assert (Hff : format_mat (meth_iter M n y0 r_flt)); 
  [ apply meth_iter_format;
  intros x Hx;
  unfold format_mat; intros i j; rewrite !mxE;
    apply generic_format_round; auto with typeclass_instances | ].

Ltac preproc_meth M h A n y0 H ThRK :=
  unfold error_loc, W_plus, W_mult;
  generalize (ThRK _ h A);
  intros Hc; 
  format_meth (M _ h A) n y0 H; revert H;
  generalize (meth_iter (M _ h A) n y0 r_flt);
  intros y Hyf; eapply Rle_trans; unfold M;
  specialize (Hc y);
  unfold W_Id, M in Hc;
  try rewrite Hc; 
  try apply build_vec_mult_error_wk.

Ltac pattern_error_bound :=
  try apply Rplus_le_compat;
  try apply Rmult_le_compat_r;
  try lra;
  try apply matrix_norm_pos;
  try apply bpow_ge_0.

Section RK_def.

Variable d : nat.

Notation "a *_sm A" := (map_mx (fun x => (a*x)) A) (at level 40).
Notation "a (x)_s[ W ] A" := (map_mx (fun x => W (a*x)) A) (at level 40).

(** À la Horner implementations of Euler and RK2 *)
  
Definition Euler (h : R) (A : 'M_d) : Sc d := fun (W : R -> R) =>
    let A_2 := h (x)_s[ W ] (rnd_mat A W) in
    (fun y => (y (+)_[ W ] (A_2 (x)_[ W ] y))).

Lemma Euler_RK_lin (h : R) (A : 'M_d) :
  is_RK_lin (Euler h A) (1%:M + ((h *_sm A) *m 1%:M)).
Proof.
  intros y.
  unfold W_Id; unfold Euler.
  rewrite mulmx1.
  rewrite mulmxDl.
  rewrite mul1mx.
  apply/matrixP => i j.
  rewrite !mxE; unfold dot_product.
  f_equal; apply eq_bigr; intros; rewrite !mxE; auto with real.
Qed.


Definition RK2 (h : R) (A : 'M_d) : Sc d := fun (W : R -> R) =>
    let A_21 := h (x)_s[ W ] (rnd_mat A W) in
    let A_22 := (W (h/2)) (x)_s[ W ] (rnd_mat A W) in
    (fun y => (y (+)_[ W ] (A_21 (x)_[ W ] (y (+)_[ W ] (A_22 (x)_[ W ] y))))).

Lemma RK2_RK_lin (h : R) (A : 'M_d) :
  is_RK_lin (RK2 h A) ((1%:M + (((h *_sm A)) *m (1%:M + ((h/2) *_sm A) *m 1%:M)))).
Proof.
  intros y.
  unfold W_Id; unfold RK2.
  rewrite mulmx1 mulmxDl mul1mx mulmxDr mulmx1.
  replace (rnd_mat A id) with A.
  assert (Hp : forall x y : 'cV_d, x (+)_[id] y = (x + y)%R).
  intros.
  apply/matrixP=> i j.
  now rewrite !mxE.
  rewrite 2!Hp.
  assert (Hm :  forall {m s p} (x :'M_(m,s)) (y : 'M_(s,p)),
             x (x)_[id] y = (x *m y)%R).
  intros. 
  apply/matrixP=> i j.
  rewrite !mxE.
  unfold dot_product.
  apply eq_bigr; intros k _; now rewrite !mxE.
  now rewrite 2!Hm mulmxDr mulmxDl mulmxA.
  simpl. 
  apply/matrixP => i j.
  now rewrite !mxE.
Qed. 
            
End RK_def.

Section Error_loc. 

Lemma euler_loc : forall n y0 h (A : 'M_d), 0 < h ->
  error_loc (Euler h A) n y0 r_flt
  <= (u + (INR d + (3 + 1/10))*u*h*||| A ||| 
     + ((508 / 100) * (1 + h) * INR d)*eta)
        *||| meth_iter (Euler h A) n y0 r_flt |||
     + ((6/10)* INR d * eta).
Proof with auto with typeclass_instances.
  intros n y0 h A Hh.
  preproc_meth Euler h A n y0 Hff Euler_RK_lin...
  11:apply Hemin.
  (* C1 = 0 *)
  apply Rle_refl.
  (* C2 = 2.01h  ||| A ||| *)
  instantiate (1 := 2.01*u*h*|||A|||).
  repeat apply Rmult_le_pos; autosolve.
  (* C3 = 0 *)
  apply Rle_refl.
  (* D1 = 0 *)
  apply Rle_refl.
  (* D2 = (6/10)*(1 + h)* INR d *)
  instantiate (1 := (6/10)* (1+h)*INR d).
  repeat apply Rmult_le_pos; autosolve.
  (* D3 = 0 *)
  apply Rle_refl.
  (* ||| X1 - A1 y ||| *)
  apply Req_le.
  ring_simplify.
  etransitivity.
  2: apply (@matrix_norm_def d 1).
  rewrite mul1mx.
  f_equal; apply/matrixP => i j.
  rewrite !mxE.
  autosolve.                                       
  (* ||| A2~ - A2 ||| *)
  eapply Rle_trans.
  apply mat_coeffs_error...
  replace (Rabs (h - h)) with 0. 
  apply Rle_refl.
  rewrite <- Rabs_R0.
  f_equal; ring.
  instantiate (2 := 1).
  instantiate (1 := INR d * (/2)).
  ring_simplify.
  apply rnd_matrix_error...
  pattern_error_bound.
  rewrite Rmult_plus_distr_r.
  simpl_arith.
  rewrite <- Rmult_assoc.
  eapply Rle_trans.
  replace (u * u) with (u ^ 2) by ring.
  subst_le (fun x => u*h + x*h + u*h) u2_le_cent (u^2).
  lra.
  simpl_arith.
  eapply Rle_trans.
  set (x := u);
    subst_le (fun x => (1+x)*h * (INR d*/2) + INR d */2)
           (Rlt_le u (1/100) u_lt_cent) x.
  apply Rmult_le_pos; autosolve.
  unfold f.
  rewrite <- Rmult_assoc.
  rewrite Rmult_comm.
  rewrite <- 2!Rmult_assoc.
  rewrite (Rmult_comm _ (/2)).
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; autosolve.
  (* ||| X3 - A3 y ||| *)
  apply Req_le.
  repeat simpl_arith.
  etransitivity.
  2: apply (@matrix_norm_def d 1).
  rewrite mul1mx.
  f_equal; apply/matrixP => i j.
  rewrite !mxE; autosolve.
  apply Rlt_le; apply Hdu.
  
  (* Bound simplification *)
  destruct d.
    rewrite /matrix_norm !big_ord0.
    repeat simpl_arith.
  rewrite matrix_norm_id matrix_norm_scal_l.
  repeat simpl_arith.
  pattern_error_bound; autosolve.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  rewrite <- Rmult_assoc.
  rewrite 3!Rplus_assoc.
  pattern_error_bound.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rplus_assoc.
  pattern_error_bound.
  rewrite <- Rplus_assoc.
  rewrite <- Rmult_assoc.
  rewrite <- 2!Rmult_assoc. 
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r.
  apply matrix_norm_pos.
  rewrite <- 2!Rmult_plus_distr_r.
  repeat apply Rmult_le_compat_r; autosolve.
  rewrite <- 3!Rmult_assoc.
  repeat apply Rmult_le_compat_r; autosolve.
Qed. 

Lemma rk2_loc : forall n y0 h (A : 'M_d), 0 < h <= 1 ->
  error_loc (RK2 h A) n y0 r_flt
  <= (u + ((INR d + 5)*u*h 
           + (6*INR d + 12/100*INR d^2)*eta)*||| A ||| +
          ((4 + 1.5*INR d)*u*h + eta)*||| A |||^2 +
          (24/10*INR d^2 + 202/100*INR d)*eta)
        *||| meth_iter (RK2 h A) n y0 r_flt |||
     + (6/10*INR d + 7/10*INR d^2 + INR d*h*|||A|||)* eta.
Proof with auto with typeclass_instances.
  intros n y0 h A Hh.
  preproc_meth RK2 h A n y0 Hff RK2_RK_lin...
  11:apply Hemin.
  (* C1 = 0 *)
  apply Rle_refl.
  (* C2 = 2.01h  ||| A ||| *)
  instantiate (1 := 2.01*u*h*|||A|||).
  repeat apply Rmult_le_pos; autosolve.
  (* C3 = u + (((1.7 + 0.6*(d + 1)*h)*u) + 0.7*eta)*|||A||| + 2.2*d*eta*)
  instantiate (1 :=
                 u + (((1.7 + 0.6*(INR d + 1)*h)*u)
                  + 0.7*eta)*|||A||| + 2.2*INR d*eta).
  rewrite <- (Rplus_0_r 0).
  apply Rplus_le_compat; autosolve.
  repeat (rewrite <- (Rplus_0_r 0);
          apply Rplus_le_compat; autosolve).
  (* D1 = 0 *)
  apply Rle_refl.
  (* D2 = 0.505*(1+h)*d *)
  instantiate (1 := 0.505*(1+h)* INR d). 
  autosolve.
  (* D3 = 0.6*d *)
  instantiate (1 := 0.6*INR d).
  autosolve.
  (* ||| X1 - A1 y ||| *)
  apply Req_le.
  ring_simplify.
  etransitivity.
  2: apply (@matrix_norm_def d 1).
  rewrite mul1mx.
  f_equal; apply/matrixP => i j.
  rewrite !mxE.
  autosolve.                                       
  (* ||| A2~ - A2 ||| *)
  eapply Rle_trans.
  apply mat_coeffs_error...
  replace (Rabs (h - h)) with 0. 
  apply Rle_refl.
  rewrite <- Rabs_R0.
  f_equal; ring.
  instantiate (2 := 1).
  instantiate (1 := INR d * (/2)).
  ring_simplify.
  apply rnd_matrix_error...
  pattern_error_bound.
  rewrite Rmult_plus_distr_r.
  simpl_arith.
  rewrite <- Rmult_assoc.
  eapply Rle_trans.
  replace (u * u) with (u ^ 2) by ring.
  subst_le (fun x => u * h + x * h + u * h) u2_le_cent (u^2).
  lra.
  simpl_arith.
  eapply Rle_trans.
  set (x := u);
    subst_le (fun x => (1+x)*h * (INR d*/2) + INR d */2)
           (Rlt_le u (1/100) u_lt_cent) x.
  apply Rmult_le_pos; autosolve.
  unfold f.
  rewrite <- Rmult_assoc.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/2)).
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; autosolve.
  (* ||| X3 - A3 y ||| *)
  eapply Rle_trans.
  apply build_vec_mult_error_wk...
  (* C1 sub = 0 *)
  apply Rle_refl.
  (* C2 sub = (1.6*h*u + 0.6*eta)*||| A ||| + 0.6*eta *)
  instantiate (1 := (1.6*h*u + 0.6*eta)*||| A ||| + 0.6*eta).
  repeat pos_auto.
  (* C3 sub = 0 *)
  apply Rle_refl.
  (* D1 sub = 0 *)
  apply Rle_refl.
  (* D2 sub = 1.52*d *)
  instantiate (1 := 1.52*INR d).
  autosolve.
  (* D3 sub = 0 *)
  apply Rle_refl.
   (* ||| X1 - A1 y ||| sub *)
  apply Req_le.
  ring_simplify.
  etransitivity.
  2: apply (@matrix_norm_def d 1).
  rewrite mul1mx.
  f_equal; apply/matrixP => i j.
  rewrite !mxE.
  autosolve.                                       
  (* ||| A2~ - A2 ||| sub *)
  eapply Rle_trans.
  apply mat_coeffs_error...  
  instantiate (1 := u *(h/2) + eta */2).
  rewrite <- (Rabs_right (h/2)) at 3.
  eapply Rle_trans.
  apply relative_error_N_FLT_strong...
  apply Req_le; ring.
  lra.
  eapply Rle_trans.
  apply rnd_matrix_error...
  pattern_error_bound; autosolve.
  simpl_arith.
  rewrite (Rplus_assoc _ (0.6*eta)).
  replace (INR d */2) with (0.5*INR d) by autosolve. 
  pattern_error_bound; autosolve.
  apply Rle_trans with (1.1*h*u +0.6*eta+0.5*h*u); autosolve.
  apply Rplus_le_compat; autosolve.
  apply Rle_trans with
    (1.01*(0.01*0.5*u*h + 0.01*0.5*eta+u*0.5*h + u *h* 0.5 + 0.5*eta)).
  pattern_error_bound; autosolve.
  apply Rmult_le_compat; autosolve.
  repeat pos_auto.
  repeat pos_auto.
  apply one_plus_u_bnd.
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat.
  2: autosolve.
  rewrite Rmult_plus_distr_l.
  apply Rplus_le_compat.
  2: autosolve.
  rewrite Rmult_plus_distr_l.
  repeat apply Rplus_le_compat.
  rewrite 2!Rmult_assoc.
  apply Rmult_le_compat; autosolve. 
  apply u_le_cent.
  rewrite Rmult_assoc.
  apply Rmult_le_compat; autosolve.
  apply u_le_cent.
  rewrite Rmult_assoc.
  apply Rmult_le_compat; autosolve.
  apply Rle_trans with
    (1.01 * (0.01 * 0.5 * u * h + u * 0.5 * h + u * h * 0.5)
     + 1.01*(0.5 + 0.01*0.5)*eta); autosolve.
  pattern_error_bound.
  repeat rewrite Rmult_plus_distr_l.
  apply Rle_trans with
    ((1.01 * (0.01 * 0.5) + 1.01 * 0.5 + 1.01 * 0.5) *(u*h)); autosolve.
  rewrite Rmult_assoc.
  apply Rmult_le_compat; autosolve.
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (0.6+1.02*INR d + 0.5*INR d); autosolve.
  apply Rplus_le_compat_r.
  apply Rle_trans with (1.01*(u*0.5* h + 0.5*eta + 0.5*h) * (0.5*INR d)); autosolve.
  apply Rmult_le_compat_r; autosolve.
  apply Rmult_le_compat; autosolve.
  repeat pos_auto.
  repeat pos_auto.
  apply one_plus_u_bnd.
  apply Rle_trans with (1.01 * (0.01*0.5*1 + 0.5*1 + 0.5*1) * (0.5 * INR d)); autosolve.
  apply Rmult_le_compat_r, Rmult_le_compat_l; autosolve.
  repeat apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat; autosolve.
  apply Rmult_le_compat_r; autosolve.
  apply u_le_cent.
  apply Rmult_le_compat_l; autosolve.
  apply eta_le_1. 
  simpl_arith.
  rewrite <- Rplus_0_l at 1.
  apply Rplus_le_compat; autosolve.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rmult_assoc.
  apply Rmult_le_compat_r; autosolve.
 
  (* ||| X3 - A3 y ||| sub *)
  apply Req_le.
  repeat simpl_arith.
  etransitivity.
  2: apply (@matrix_norm_def d 1).
  rewrite mul1mx.
  f_equal; apply/matrixP => i j.
  rewrite !mxE; autosolve.
  apply Rlt_le; apply Hdu. 
  apply Hemin. 
  (* Bound simplification sub *)
  repeat simpl_arith.
    destruct d as [|d'].
    rewrite /matrix_norm !big_ord0.
    repeat simpl_arith.
  repeat rewrite matrix_norm_scal_l.
  repeat rewrite matrix_norm_id.
  repeat simpl_arith.
  repeat rewrite Rabs_right; autosolve.
  pattern_error_bound; autosolve.
  rewrite 2!Rplus_assoc.
  rewrite Rplus_comm.
  rewrite 3!Rplus_assoc.
  apply Rplus_le_compat; autosolve.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rplus_assoc.
  pattern_error_bound; autosolve.
  autosolve.
  rewrite <- 2!Rmult_assoc.
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (((INR d'.+1 + 1.01) *0.5 + 1.03*1.6)*h*u
                        +1.03*0.6*eta); autosolve.
  apply Rplus_le_compat.
  2: apply Rmult_le_compat_r;autosolve.
  apply Rmult_le_compat_r; autosolve.
  rewrite Rmult_plus_distr_r.
  rewrite Rplus_comm.
  apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat_r; autosolve.
  rewrite Rmult_comm.
  repeat rewrite Rmult_plus_distr_l.
  apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat; autosolve.
  cut (eta <= INR d'.+1*eta).
  intros Hde; eapply Rle_trans.
  set e := eta.
  subst_le (fun x => (1 + 3 / 100) * (0.6 *x + 1.52 * (INR d'.+1 * eta))) Hde e.
  rewrite (Rmult_assoc _ (INR d'.+1) e); unfold e; autosolve.
  rewrite Rmult_assoc.
  set g := INR d'.+1*eta.
  repeat rewrite Rmult_plus_distr_l.
  rewrite <- !Rmult_assoc.
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; autosolve.
  rewrite <- Rmult_1_l at 1.
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (INR 1); autosolve.
  apply le_INR; autosolve.
  auto with arith.
  apply Rlt_le, Hdu.
  (* Bound simplification *)
    destruct d as [|d'].
    rewrite /matrix_norm !big_ord0.
    rewrite pow_i; try lia.
    repeat simpl_arith.
  simpl_arith.
  replace (1 + 3/100) with 1.03 by autosolve.
  replace (h/2) with (0.5*h) by autosolve. 
  repeat rewrite matrix_norm_scal_l.
  simpl_arith.
  eapply Rle_trans.
  repeat apply Rplus_le_compat.
  2: apply Rle_refl.    
  apply Rmult_le_compat_r.
  apply matrix_norm_pos.
  repeat apply Rplus_le_compat.
  2: apply Rle_refl.
  apply Rmult_le_compat_l.
  autosolve.
  repeat apply Rplus_le_compat. 
  apply Rmult_le_compat_l. 
  autosolve.
  apply matrix_norm_triang.
  apply Rle_refl.
  apply Rle_refl.
  apply Rmult_le_compat_r.
  autosolve.
  apply Rmult_le_compat_r.
  autosolve.
  repeat apply Rplus_le_compat.
  apply Rle_refl.
  apply Rle_refl.
  apply Rle_refl.
  apply matrix_norm_triang.
  apply Rmult_le_compat_l.
  autosolve.
  apply Rle_trans with (INR d'.+1); autosolve.
  apply matrix_norm_triang.
  repeat rewrite mulmx1.
  repeat rewrite matrix_norm_scal_l.
  simpl_arith.
  rewrite <- !Rplus_assoc.
  pattern_error_bound.
  rewrite 10!Rplus_assoc.
  rewrite Rplus_comm.
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  set K1 := ((INR d'.+1 + (1+1/100)) * u*h).
  set K2 := ((INR d'.+1 + (1+1/100)) * u*h*0.5*h).
  assert (Ht1:
           (INR d'.+1 + (1+1/100)) * u*(h*||| A |||)*(1+0.5*h*||| A |||)
         = K1*||| A ||| + K2*||| A |||^2).
  unfold K1, K2; autosolve.
  rewrite Ht1.
  set K3 := 2.01*u*h.
  set K4 := 2.01*u*h*0.5*h.
  assert (Ht2: 2.01 * u * h * ||| A ||| * (1 + 0.5 * h * ||| A |||) =
                 K3*||| A ||| + K4*||| A |||^2).
  unfold K3, K4; autosolve.
  rewrite Ht2.
  rewrite Rmult_plus_distr_l.
  rewrite <- Rplus_assoc.
  rewrite Rmult_plus_distr_l.
  rewrite <- 3!Rplus_assoc.
  rewrite <- 2!Rmult_assoc.
  assert (Hb1 : K1*||| A ||| + K2*||| A |||^2
                + 1.03*K3 *||| A ||| + 1.03*K4*||| A |||^2 =
                  (K1 + 1.03*K3)*||| A ||| + (K2+1.03*K4)*||| A |||^2).
  autosolve.
  rewrite Hb1.
  rewrite 8!Rmult_plus_distr_l.
  simpl_arith.
  set K5 := (1.03* (u*h + 2.2 * INR d'.+1 * eta * h)).
  set K6 := (1.03*((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u + 0.7 * eta)*h). 
  assert (Ht3:
           1.03 *
             ((u +
                 ((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u + 0.7 * eta) *
                   ||| A ||| + 2.2 * INR d'.+1 * eta) *  (h * ||| A |||)) =
             K5*||| A ||| + K6*||| A ||| ^ 2).
  unfold K5,K6; autosolve.
  rewrite Ht3.
  rewrite <- 5!Rplus_assoc.
  replace ((K1 + 1.03 * K3) * ||| A ||| + (K2 + 1.03 * K4) * ||| A ||| ^ 2 +
           K5 * ||| A ||| + K6 * ||| A ||| ^ 2)
    with
    ((K1 + 1.03 *K3 + K5) * ||| A ||| +
       (K2 + 1.03 * K4 + K6)* ||| A ||| ^ 2)
  by autosolve. 
  replace ((K1 + 1.03 * K3 + K5) * ||| A ||| + (K2 + 1.03 * K4 + K6) * ||| A ||| ^ 2 +
       1.03 * (K3 * ||| A ||| * u) +
       1.03 * (K3 * ||| A ||| *
         (((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u + 0.7 * eta) * ||| A |||)) +
       1.03 * (K3 * ||| A ||| * (2.2 * INR d'.+1 * eta))) with
    ((K1+ 1.03*K3 + K5 + 1.03*K3*u + 1.03*K3*2.2*INR d'.+1*eta)* ||| A |||
     + (K2+1.03*K4+K6 + 1.03*K3*((1.7 + (0.6 * INR d'.+1 + 0.6)*h)*u + 0.7*eta))*||| A |||^2)
    by autosolve.
  set J1 := ((0.505 + 0.505 * h) * INR d'.+1).
  set J2 := (1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u + 0.7 * eta.
  set Keta := 1.03*(u*J1 + (2.2*INR d'.+1*eta + 1)*J1).
  set KA := 1.03*(J2*J1*eta + 0.5*h*J1*eta).
  eapply Rle_trans.
  apply Rplus_le_compat_l.
  apply Rle_trans with (KA * ||| A ||| + Keta * eta).
  eapply Rle_trans.
  apply Rmult_le_compat_l.
  autosolve.
  repeat apply Rmult_le_compat_r.
  autosolve.
  autosolve.
  apply Rplus_le_compat_l.
  apply Rle_trans with ((J2 + 0.5*h)*||| A ||| + 2.2 * INR d'.+1 * eta + 1).
  rewrite Rmult_plus_distr_r.
  rewrite 2!Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite <- Rplus_assoc.
  autosolve.
  apply Rle_refl.
  unfold KA, Keta; autosolve.
  apply Rle_refl.
  rewrite <- 2!Rplus_assoc.
  pattern_error_bound.
  apply Rle_trans with
    ((K1+1.03*K3 + K5 + 1.03*K3*u + 1.03*K3*2.2 * INR d'.+1*eta + KA)*|||A|||
     + (K2 + 1.03 * K4 + K6 + 1.03 * K3 * J2) * ||| A ||| ^ 2).
  autosolve. 
  pattern_error_bound.
  unfold K1, K3, K5, KA, J1, J2.
  replace (1 + 1/100) with 1.01 by autosolve.
  replace (12/100) with 0.12 by autosolve.
  set M1 := (INR d'.+1 + 1.01) + 1.03 * (2.01) +1.03*(1+2.01*u).
  set M2 := (1.03 * (2.01 * u * h) * 2.2 * INR d'.+1
             + 1.03 * (2.2 * INR d'.+1 * h + 0.5 * h * ((0.505 + 0.505 * h) * INR d'.+1))
             +1.03 *
          (((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u + 0.7 * eta) *
             ((0.505 + 0.505 * h) * INR d'.+1))).
  apply Rle_trans with (M1*(u*h) + M2*eta).
  unfold M1, M2; autosolve.
  pattern_error_bound; autosolve.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_r; autosolve.
  unfold M1; rewrite 2!Rplus_assoc; apply Rplus_le_compat_l.
  generalize u_lt_cent; intros Hcu.
  autosolve.
  unfold M2.
  apply Rle_trans with
    (1.03 * (2.01 * 0.01 * 1) * 2.2 * INR d'.+1 +
        1.03 * (2.2 * INR d'.+1 * 1 + 0.5 * 1 * ((0.505 + 0.505 * 1) * INR d'.+1)) +
        1.03 * (((1.7 + (0.6 * INR d'.+1 + 0.6) * 1) * 0.01 + 0.7 * 1) *
                  ((0.505 + 0.505 * 1) * INR d'.+1))).
  generalize u_lt_cent; intros Hcu; apply Rlt_le in Hcu.
  cut (eta <= 1).
  intros Heta.
  repeat apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat_r; autosolve.
  apply Rmult_le_compat_r; autosolve.
  apply Rmult_le_compat_l; autosolve.
  rewrite 2!Rmult_assoc.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat; autosolve.
  apply Rmult_le_compat_l; autosolve.
  repeat apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat_l; autosolve.
  rewrite 2!Rmult_assoc.
  apply Rmult_le_compat_l; autosolve.
  rewrite <- 2!Rmult_assoc. 
  apply Rmult_le_compat_r; autosolve.
  apply Rmult_le_compat; autosolve.
  apply Rmult_le_compat_l; autosolve.
  rewrite <- 2!Rmult_assoc.
  apply Rmult_le_compat_r; autosolve.
  apply Rmult_le_compat; autosolve.
  rewrite <- Rplus_0_r at 1.
  repeat apply Rplus_le_compat; autosolve.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat; autosolve.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat; autosolve.
  repeat apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat; autosolve.
  repeat pos_auto.
  apply Rplus_le_compat_l; autosolve.
  apply Rmult_le_compat_l; autosolve.
  pos_auto.
  apply eta_le_1.
  apply Rle_trans with
    ((0.0455466 + 2.78615 + 1.03*1.01*0.723)* INR d'.+1 +
       1.03*1.01*0.006*INR d'.+1 ^ 2); autosolve.
  pattern_error_bound; autosolve.
  autosolve.
  unfold K2, K4, K6, K3, J2.
  replace (1+1/100) with 1.01 by autosolve.
  replace (6+6/10) with 6.6 by autosolve.
  apply Rle_trans with
    ((INR d'.+1 + 1.01) * u * h * 0.5 * h + 1.03 * (2.01 * u * h * 0.5 * h) +
       1.03 * ((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u) * h +
       1.03 * (2.01 * u * h) * ((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u)
     + (1.03 * (2.01 * u * h) * 0.7 + 0.7*1.03*h)*eta); autosolve.
  apply Rplus_le_compat.
  apply Rle_trans with (
   (((INR d'.+1 + 1.01) * 0.5 * h)  + (1.03 * (2.01 * 0.5 * h)) +
  (1.03 * ((1.7 + (0.6 * INR d'.+1 + 0.6) * h)))  +
    (1.03 * 2.01 * ((1.7 + (0.6 * INR d'.+1 + 0.6) * h) * u)))* (u*h)).
  autosolve.
  rewrite <- Rmult_assoc.
  apply Rmult_le_compat_r; autosolve.
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (
      (1.01* 0.5 * h + 1.03 * 2.01 * 0.5 * h + 1.03*(1.7+0.6*h) + 1.03*2.01*(1.7*u + 0.6*h*u))
      +
        ((0.5*h) + 1.03*0.6*h + 1.03*2.01*0.6*h*u)*INR d'.+1); autosolve.
  apply Rplus_le_compat.
  apply Rle_trans with
    (1.01 * 0.5 * 1 + 1.03 * 2.01 * 0.5 * 1 + 1.03 * (1.7 + 0.6 * 1) +
       1.03 * 2.01 * (1.7 * 0.01 + 0.6 * 1 * 0.01)).  
  repeat apply Rplus_le_compat.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat_l; autosolve.
  apply Rplus_le_compat; autosolve.
  apply Rmult_le_compat_l; autosolve.
  apply Rlt_le, u_lt_cent.
  rewrite 2!Rmult_assoc.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat; autosolve.
  apply Rlt_le, u_lt_cent.
  autosolve.
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (0.5 * 1 + 1.03 * 0.6 * 1 + 1.03 * 2.01 * 0.6 * 1 * 0.01).
  repeat apply Rplus_le_compat; autosolve.
  rewrite 6!Rmult_assoc.
  repeat apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat; autosolve.
  apply Rlt_le, u_lt_cent.
  autosolve. 
  rewrite <- Rmult_1_l.
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (1.03 * (2.01 * 0.01 * 1) * 0.7 + 0.7 * 1.03 * 1).
  pattern_error_bound; autosolve.
  rewrite 2!Rmult_assoc.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat_l; autosolve.
  apply Rmult_le_compat; autosolve.
  apply Rlt_le, u_lt_cent.
  autosolve.
  unfold Keta.
  unfold J1.
  apply Rle_trans with
    ((1.03*0.505*(1+h)*(1+u))*(INR d'.+1)
     + (1.03*0.505*2.2*(1+h)*eta*(INR d'.+1)^2)).
  autosolve.
  rewrite Rplus_comm.
  pattern_error_bound; autosolve.
  apply Rle_trans with (1.03*0.505*2.2*2*eta).
  apply Rmult_le_compat_r; autosolve.
  apply Rle_trans with (1.03 * 0.505 * 2.2 * 2 * 1).
  repeat apply Rmult_le_compat_l; autosolve.
  apply eta_le_1.
  autosolve.
  apply Rle_trans with (1.03 * 0.505 * (1 + 1) * (1 + 0.01)).
  repeat apply Rmult_le_compat; autosolve.
  apply Rle_trans with u; autosolve.
  apply Rplus_le_compat_l.
  apply Rlt_le, u_lt_cent.
  autosolve.
  rewrite 2! Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_l.
  rewrite Rplus_comm.
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite 2!Rmult_plus_distr_l.
  apply Rle_trans with (
      (1.03 * (2.01 * u * h  * (0.6 * INR d'.+1) + h*(0.6 * INR d'.+1)))*||| A ||| +
        1.03 * ((0.505 * 1 + 0.505 * h) * INR d'.+1 * (0.6 * INR d'.+1))).
  autosolve.
  rewrite Rplus_comm.
  pattern_error_bound.
  simpl_arith.
  apply Rle_trans with
    ((1.03 * ((0.505 + 0.505 * h) * 0.6) * (INR d'.+1 ^2))).  
  autosolve.
  apply Rmult_le_compat_r.
  autosolve.
  ring_simplify.
  apply Rle_trans with (1.03 * 0.505*0.6 + 1.03 * 0.505*0.6).
  simpl_arith.
  autosolve.
  ring_simplify.
  rewrite <- Rmult_plus_distr_r.
  apply Rmult_le_compat_r; autosolve.
  rewrite <- Rmult_plus_distr_r.
  apply Rle_trans with (((1.03*2.01*0.01 + 1.03)*h)*0.6); autosolve.
  generalize u_lt_cent; intros Huc.
  repeat apply Rmult_le_compat_r; autosolve.
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_r; autosolve.
Qed.

End Error_loc. 

Section Error_glob. 
 
(** Global error bound for Euler *)

Theorem euler_glob : forall N y0 h (A : 'M_d), 
  let C := (u + (INR d + (3 + 1/10))*u*h*||| A ||| 
     + ((508 / 100) * (1 + h) * INR d)*eta) in 
  let K := Rmax (C + |||1%:M + h *_sm A *m 1%:M |||) 1 in
        0 < h -> 0 < ||| A ||| -> 
        error_glob (Euler h A) N y0 r_flt
             <= (C + ||| 1%:M + h *_sm A *m 1%:M |||) ^ N *
                 (||| rnd_mat y0 (round beta (FLT_exp emin prec) ZnearestE) - y0 ||| +
                     INR N * C * ||| y0 ||| /
                  (C + ||| 1%:M + h *_sm A *m 1%:M |||)) +
               INR N*K^N * 6 / 10 * INR d * eta.
Proof with auto with typeclass_instances.
  intros N y0 h A C K Hh HA.
assert (d_NZ : (0 < d)%coq_nat).
  destruct d; try lia.
  rewrite /matrix_norm big_ord0 /GRing.zero /= in HA.
  lra.
assert (Hu : 0 < u) by 
  (apply Rdiv_lt_0_compat; try apply bpow_gt_0; now auto with real).
assert (Hrd : 0 <= INR d) by (apply: (le_INR 0); lia). 
assert (Heta : 0 < eta) by apply: bpow_gt_0. 
eapply Rle_trans.
apply error_loc_to_glob...
4 : {
  intros n.
  now apply euler_loc.
}
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_lt_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra.
repeat apply Rmult_le_pos; try lra.
repeat apply Rmult_lt_0_compat; try lra.
intros y.
unfold W_Id, Euler.
instantiate (1 := (1%:M + (h *_sm A) *m 1%:M)%R). 
rewrite mulmx1.
rewrite mulmxDl.
rewrite mul1mx.
apply/matrixP => i j.
rewrite !mxE.
f_equal.
simpl.
unfold dot_product.
apply eq_bigr.
intros x; f_equal.
rewrite !mxE.
reflexivity.
apply Req_le.
unfold K, C; lra.
Qed.

(** Global error bound for Euler *)

Theorem rk2_glob :  forall N y0 h (A : 'M_d),
        let C := (u + ((INR d + 5)*u*h 
           + (6*INR d + 12/100*INR d^2)*eta)*||| A ||| +
          ((4 + 1.5*INR d)*u*h + eta)*||| A |||^2 +
          (24/10*INR d^2 + 202/100*INR d)*eta) in
        let K := Rmax (C + ||| 1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A) |||) 1 in
        0 < h <= 1 -> 0 < ||| A ||| -> 
        error_glob (RK2 h A) N y0 r_flt
             <= (C + ||| 1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A) |||) ^ N *
                 (||| rnd_mat y0 (round beta (FLT_exp emin prec) ZnearestE) - y0 ||| +
                     INR N * C * ||| y0 ||| /
                  (C + ||| 1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A) |||)) +
                INR N*K^N * (6/10*INR d + 7/10*INR d^2 + INR d*h*|||A|||) * eta.
Proof with auto with typeclass_instances.
intros N y0 h A C K Hh HA.
assert (d_NZ : (0 < d)%coq_nat).
  destruct d; try lia.
  rewrite /matrix_norm big_ord0 /GRing.zero /= in HA.
  lra.
eapply Rle_trans.
apply error_loc_to_glob...
4 : {
  intros n.
  now apply rk2_loc.
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
apply Rmult_le_pos; try lra.
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
apply Rlt_le. apply Rmult_lt_0_compat; try lra.
apply Rlt_le_trans with (6 / 10 * INR d); try lra.
apply Rmult_lt_0_compat; try lra.
replace 0 with (INR 0) by reflexivity.
apply lt_INR; lia.
apply Rle_trans with (6 / 10 * INR d + 0 + 0).
lra.
repeat apply Rplus_le_compat; try lra;
repeat apply Rmult_le_pos; try lra;
apply pos_INR.
apply bpow_gt_0.
intros y.
unfold W_Id, RK2.
instantiate (1 := 
  (1%:M + (h *_sm A) + (((h^2)/2) *_sm A *m A))%R).
rewrite mulmxDl.
replace (rnd_mat A id) with A.
2 : {apply/matrixP => i j.
rewrite !mxE.
reflexivity. }
assert (Hp : 
  forall (x y : 'cV_d), x (+)_[id] y = (x + y)%R).
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
unfold dot_product.
apply eq_bigr; intros; now rewrite !mxE.
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
apply eq_bigr; intros t _; rewrite !mxE.
Rring_tac.
replace (h ^ 2) with (h * h) by lra.
rewrite <- Rmult_assoc.
f_equal; lra.
Rring_tac.
apply matrixP=> i j.
rewrite !mxE.
rewrite <- Rplus_assoc.
reflexivity.
unfold K, C; lra. 
Qed.

End Error_glob.
