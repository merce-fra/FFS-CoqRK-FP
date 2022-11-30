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

From mathcomp
Require Import all_ssreflect ssralg matrix zmodp.
Require Import Rstruct Compl Norms.

From Flocq.Core
Require Import Core. 
From Flocq.Prop
Require Import Mult_error Plus_error Relative.

Open Scope R_scope.

(* Prerequisites for automation tactics *)
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

(* Preliminary definitions *)
Definition rnd_mat {m n} (A : 'M[R]_(m,n)) (W : R -> R) := map_mx W A.

Definition W_plus {n m}
  (W : R -> R) (A : 'M[R]_(m,n)) (B : 'M[R]_(m,n)) : 'M[R]_(m,n)
  := rnd_mat (A + B) W.

Notation "A (+)_[ W ]  B" := (W_plus W A B) (at level 40).

(** Rounded dot product *)
Definition dot_product {d} (a b : 'cV[R]_d) W :=
  \big[(fun x y => W (x + y)) / 0%R]_(i < d)
    (W ((a i ord0)*(b i ord0))).

Definition W_mult {n m p}
  (W : R -> R) (A : 'M[R]_(m,p)) (B : 'M[R]_(p,n)) : 'M[R]_(m,n)
  :=  \matrix_(i, j)
        dot_product (row i A)^T (col j B) W.

Lemma W_mult_spec : forall d W (A B : 'M_d), W_mult W A B =
           \matrix[mulmx_key]_(i, j)
        (\big[(fun x y => W (x + y)) / 0%R]_k (W (A i k * B k j))).
Proof.
  intros d W A B.
  unfold W_mult.
  apply/matrixP => i j.
  rewrite !mxE.
  unfold dot_product; simpl.
  apply eq_bigr; intros x _; now rewrite !mxE. 
Qed.

Notation "A (x)_[ W ] B" := (W_mult W A B) (at level 45).

Notation "a *_sm A" := (map_mx (fun x => (a*x)) A) (at level 40).

Section Opt_rel_error.

Variable beta : radix.
Variable emin prec : Z.
Variable choice : Z -> bool.
Context { prec_gt_0_ : Prec_gt_0 prec }.

Notation format := (generic_format beta (FLT_exp emin prec)).

Notation round_flt :=(round beta (FLT_exp emin prec) (Znearest choice)).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation cexp := (cexp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

Notation u := (bpow (1-prec) / 2).

Lemma opt_le_u : (u / (1 + u)) < u.
Proof.
  apply Rmult_lt_reg_r with (1 + u).
  apply Rlt_le_trans with 1; try lra.
  rewrite <- (Rplus_0_r 1) at 1.
  apply Rplus_le_compat_l.
  unfold u; apply Rmult_le_pos; try apply bpow_ge_0; try lra.
  apply Rle_lt_trans with u. 
  apply Req_le; field.
  apply Rgt_not_eq, Rlt_gt.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_lt_le_compat; autosolve.
  rewrite <- Rmult_1_r at 1.
  apply Rmult_lt_compat_l.
  unfold u.
  apply Rmult_lt_0_compat.
  apply bpow_gt_0; try lra.
  auto with real.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_0_compat; autosolve.
  apply bpow_gt_0.
Qed. 

(** Optimal bound on relative error (Jeannerod-Rump) *)

Lemma error_le_opt_FLT : forall x,
    bpow (emin+prec-1) <= Rabs x ->
    Rabs (round_flt x -x) <= (u/(1+u)) * Rabs x.
Proof with auto with typeclass_instances.
intros x Hx.
case_eq (mag beta x); intros e He1 He2.
assert (Y1 : x <> 0).
intros K; contradict Hx; apply Rlt_not_le.
rewrite K Rabs_R0; apply bpow_gt_0.
assert (Y2 : 0 < u).
apply Rdiv_lt_0_compat; try apply bpow_gt_0; now auto with real.
assert (Y3 : 0 < u / (1 + u)).
apply Rdiv_lt_0_compat; try easy.
apply Rplus_lt_0_compat; try easy; now auto with real.
assert (Y4:(emin+prec-1 < e)%Z).
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=Hx).
apply He1...
(* *)
case (Rle_or_lt ((1+u)*bpow (e-1)) (Rabs x)); intros H.
(* big mantissa *)
apply Rle_trans with (/2*ulp beta (FLT_exp emin prec) x).
apply error_le_half_ulp...
rewrite ulp_neq_0...
unfold cexp, FLT_exp; rewrite He2.
simpl (mag_val _ _ (Build_mag_prop beta x e He1)).
rewrite Z.max_l.
apply Rle_trans with (u*bpow (e - 1)).
unfold u; rewrite (Rmult_comm _ (/2)).
rewrite Rmult_assoc; right; f_equal.
rewrite <- bpow_plus; f_equal; ring.
apply Rle_trans with 
 ((u / (1 + u))*((1 + u) * bpow (e - 1))).
right; field.
apply Rgt_not_eq, Rlt_gt.
apply Rplus_lt_0_compat.
auto with real.
apply bpow_gt_0.
apply Rmult_le_compat_l; try easy.
now left.
lia.
(* small mantissa *)
apply Rle_trans with (Rabs x - bpow (e-1)).
(* . *)
assert (T: Rabs (round_flt x) = bpow (e - 1)).
apply Rle_antisym.
assert (T: exists c, Rabs (round_flt x) =
    round beta (FLT_exp emin prec) (Znearest c) (Rabs x)).
case (Rle_or_lt 0 x); intros Zx.
exists choice.
rewrite Rabs_right; try easy.
rewrite Rabs_right; try easy.
now apply Rle_ge.
apply Rle_ge, round_ge_generic...
apply generic_format_0...
exists (fun t : Z => negb (choice (- (t + 1))%Z)).
rewrite <- (Ropp_involutive (round _ _ _ (Rabs x))).
rewrite <- round_N_opp...
rewrite Rabs_left1.
rewrite Rabs_left; try easy.
f_equal; f_equal; ring.
apply round_le_generic...
apply generic_format_0...
now left.
destruct T as (c,Hc); rewrite Hc.
apply round_N_le_midp...
apply generic_format_bpow...
unfold FLT_exp; rewrite Z.max_l; try lia.
unfold Prec_gt_0 in prec_gt_0_; lia.
apply Rlt_le_trans with (1:=H).
rewrite succ_eq_pos.
2: apply bpow_ge_0.
rewrite ulp_bpow.
unfold FLT_exp; rewrite Z.max_l; try lia.
replace (e-1+1-prec)%Z with ((e-1)+(1-prec))%Z by ring.
rewrite bpow_plus.
right; unfold u; field.
apply abs_round_ge_generic...
apply generic_format_bpow...
unfold FLT_exp.
rewrite Z.max_l; try lia.
unfold Prec_gt_0 in prec_gt_0_; lia.
apply He1...
case (Rle_or_lt 0 x); intros Zx.
(* . *)
rewrite Rabs_minus_sym.
rewrite Rabs_right in T.
rewrite Rabs_right; try easy.
rewrite Rabs_right; try easy.
rewrite T; right; ring.
auto with real.
apply Rle_ge.
apply Rle_0_minus.
rewrite T. 
rewrite <- (Rabs_right x).
apply He1...
auto with real.
apply Rle_ge, round_ge_generic...
apply generic_format_0...
(* . *)
rewrite Rabs_left1 in T.
rewrite Rabs_right.
rewrite Rabs_left; try easy.
rewrite <- T; right; ring.
apply Rle_ge.
apply Rle_0_minus.
apply Ropp_le_cancel.
rewrite T. 
rewrite <- (Rabs_left x); try easy.
apply He1...
apply round_le_generic...
apply generic_format_0...
now left.
(* . *)
apply Rplus_le_reg_l with 
 (bpow (e - 1) - ((u / (1 + u) * Rabs x))).
apply Rle_trans with (bpow (e-1));[idtac|right;ring].
apply Rle_trans with (Rabs x * (1-u/(1+u)));[right; ring|idtac].
apply Rmult_le_reg_l with (1+u).
apply Rplus_lt_0_compat; try easy; now auto with real.
left; apply Rle_lt_trans with (2:=H).
right; field.
apply Rgt_not_eq, Rlt_gt.
apply Rplus_lt_0_compat.
auto with real.
apply bpow_gt_0.
Qed.

Lemma error_le_plus_opt: forall x y, format x -> format y ->
  (Rabs (round_flt (x+y) - (x+y)) <= (u/(1+u))*Rabs (x+y)).
Proof with auto with typeclass_instances.
intros x y Fx Fy.
case (Rle_or_lt (Rabs (x+y)) (bpow (prec+emin))); intros H.
rewrite round_generic...
replace (x + y - (x + y)) with 0 by ring.
rewrite Rabs_R0.
apply Rmult_le_pos.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra; try apply bpow_ge_0.
lra. apply Rabs_pos.
apply FLT_format_plus_small...
apply error_le_opt_FLT.
apply Rle_trans with (bpow (prec + emin)).
apply bpow_le; lia.
auto with real.
Qed.


Lemma error_le_plus_1: forall x y, format y ->
  (Rabs (round_flt (x+y) - (x+y)) <= Rabs x).
Proof with auto with typeclass_instances.
intros x y Fy.
apply Rle_trans with (Rabs (y - (x+y))).
apply round_N_pt...
rewrite <- Rabs_Ropp.
right; apply f_equal.
ring.
Qed.

End Opt_rel_error.

(** FP preliminaries *)
Section FP_loc_err.

Variable beta : radix.
Variable emin prec : Z. 

Context { prec_pos : Prec_gt_0 prec }.
Variable choice : Z -> bool. 

Definition u := (bpow beta (1-prec) / 2).
Definition eta := bpow beta emin.

Notation r_flt :=
         (round beta (FLT_exp emin prec) (Znearest choice)). 
Notation format := (generic_format beta (FLT_exp emin prec)).

Definition format_mat {m n} (A : 'M[R]_(m,n)) := 
                             forall i j, format (A i j).


Definition Rnd_Rplus (a b : R) := r_flt (a + b).
Definition Rnd_Rmult (a b : R) := r_flt (a*b). 

Notation "a (+) b" := (Rnd_Rplus a b).
Notation "a (x) b" := (Rnd_Rmult a b) (at level 44).

Notation "A (+)_m B" := (rnd_mat (A + B) r_flt) (at level 50). 

Notation "X (x)_m Y" := (W_mult r_flt X Y) (at level 50).

Notation "a (x)_sm A" := (map_mx (fun x => r_flt (a*x)) A) (at level 50).

Lemma INR_succ_minus : forall d, INR d.+1 - 1 = INR d.
Proof.
  intros d.
  rewrite S_INR.
  lra.
Qed.

  
Section MatrixRndError. 

(** Optimal bound on summation (with vectors/bigops) *)

Theorem error_sum_n_opt_bigop : forall {d} (v : 'cV_d),
    format_mat v -> 
    let e:= \sum_(i < d) (v i ord0) in 
    let f:= \big[(fun x y => x (+) y) / 0%R]_(i < d) (v i ord0) in 
    let a:= \sum_(i < d) Rabs (v i 0) in 
      Rabs (f-e) <= (INR d - 1)*(u/(1+u))*a.
Proof with auto with typeclass_instances.
destruct d; intros v Hv.
  rewrite !big_ord0 /= !(Rminus_0_r, Rmult_0_r) Rabs_R0; auto with real.
set l := index_enum _.
replace (INR d.+1) with (INR (size l)).
2 : now rewrite /l /index_enum unlock -enumT size_enum_ord.
elim: l.
rewrite !big_nil.
simpl.
rewrite Rminus_0_r Rabs_R0 Rmult_0_r.
auto with real.
intros i l.
rewrite !big_cons.
intros IH e' f' ab'.
pose e := \sum_(i <- l) v i 0 .
pose f := \big[Rnd_Rplus/0]_(i <- l) v i ord0.
pose ab := \sum_(i <- l) Rabs (v i 0).
pose a := v i ord0.
replace f' with ((v i ord0 (+) f)) by reflexivity.
replace e' with (v i ord0  +e) by reflexivity.
replace (v i ord0 (+) f - (v i ord0 + e)) with
    ((f-e) + ((a (+) f)-(a +f))) by (rewrite /a; ring).
apply Rle_trans with (1:=Rabs_triang _ _).
assert (Rabs (f - e) <= (INR (size l) - 1) * (u/(1+u)) * ab).
apply IH.
eapply Rle_trans.
apply Rplus_le_compat.
apply H.
2: replace ab' with (Rabs a + ab) by reflexivity.
2: replace (size (i::l)) with ((size l).+1) by reflexivity.
2: rewrite S_INR.
2: apply Rle_trans with 
  ((INR (size l) - 1) * (u/(1+u)) * ab + (u/(1+u))*
       (Rabs a +(ab +(INR (size l)-1)*Rabs a))).
3: right; ring.
2: apply Rle_refl.
apply Rle_trans with 
  ((u/(1+u)) * (ab + INR (size l) * Rabs a)).
2: right; ring.
(* . assertions *)
assert (Ff: format f).
unfold f; case l; simpl.
rewrite big_nil.
apply generic_format_0...
intros; rewrite big_cons.
apply generic_format_round...
assert (Fa: format a).
now apply: Hv.
assert (Y:Rabs e <= ab).
clear; induction l.
unfold e, ab; rewrite !big_nil.
rewrite Rabs_R0; apply Rle_refl.
unfold e, ab; rewrite !big_cons.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l.
apply IHl.
(* . end of assertions *)
case (Rle_or_lt (Rabs a) ((u/(1+u))*ab)).
(* . *)
intros M1.
apply Rle_trans with (Rabs a).
apply error_le_plus_1; try assumption.
apply Rle_trans with (1:=M1).
apply Rmult_le_compat_l.
repeat apply Rmult_le_pos; autosolve.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_trans with u.
apply Rmult_le_pos; autosolve.
lra. 
apply Rplus_le_reg_l with (-ab); ring_simplify.
apply Rmult_le_pos; autosolve.
apply Rabs_pos.
(* . *)
intros M1.
case_eq l.
(* .. case l = nil *)
intros V; unfold f, ab; rewrite V !big_nil.
rewrite Rplus_0_r !Rplus_0_l Rmult_0_l Rmult_0_r.
rewrite /Rnd_Rplus /= Rplus_0_r.
rewrite round_generic...
rewrite Rminus_diag_eq; try reflexivity.
rewrite Rabs_R0.
apply Rle_refl.
(* .. case l != nil *)
intros r l' Hl; rewrite <- Hl.
case (Rle_or_lt ab ((u/(1+u))*(Rabs a))).
intros M2.
apply Rle_trans with (Rabs f).
rewrite /Rnd_Rplus Rplus_comm.
apply error_le_plus_1; try assumption.
replace f with (e+(f-e)) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rle_trans with ((u/(1+u))*Rabs a+(INR (length l) - 1) * (u/(1+u)) * ab).
apply Rplus_le_compat; try assumption.
apply Rle_trans with ab; assumption.
apply Rle_trans with ((u/(1+u))*((INR (length l) - 1)*ab+Rabs a)).
right; ring.
apply Rmult_le_compat_l.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra; try apply bpow_ge_0.
lra.
apply Rle_trans with (INR (length l) * Rabs a).
apply Rplus_le_reg_l with (-Rabs a).
apply Rle_trans with ((INR (length l) - 1) * ab);[right; ring|idtac].
apply Rle_trans with ((INR (length l) - 1) * Rabs a);[idtac|right; ring].
apply Rmult_le_compat_l.
rewrite Hl.
replace (length (r::l')) with (S (length l')) by reflexivity.
rewrite S_INR.
ring_simplify.
apply pos_INR.
apply Rle_trans with (1:=M2).
apply Rle_trans with (bpow beta 0 *Rabs a).
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rmult_le_reg_r with (1+u).
apply Rle_lt_trans with u.
apply Rmult_le_pos.
apply bpow_ge_0.
lra.
lra.
replace (bpow beta 0) with 1 by reflexivity.
replace (u / (1 + u) * (1 + u)) with u. 
ring_simplify.
lra.
field.
apply Rgt_not_eq, Rlt_gt.
apply Rle_lt_trans with (0 + 0); try lra.
apply Rplus_lt_compat; try lra.
apply: Rdiv_lt_0_compat; auto with real.
apply: bpow_gt_0.
replace (bpow beta 0) with 1 by reflexivity.
ring_simplify. 
apply Rle_refl.
rewrite <- (Rplus_0_l (INR (length l)*Rabs a)) at 1.
apply Rplus_le_compat_r.
apply Rle_trans with (2:=Y).
apply Rabs_pos.
(* . *)
intros M2.
apply Rle_trans with ((u/(1+u))*Rabs (a+f)).
apply error_le_plus_opt; try assumption.
apply Rmult_le_compat_l.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra; try apply bpow_ge_0.
lra. 
apply Rle_trans with (1:=Rabs_triang _ _).
replace f with (e+(f-e)) by ring.
apply Rle_trans with (Rabs a +(Rabs e +(INR (size l) - 1) * (u/(1+u)) * ab)).
apply Rplus_le_compat_l.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l; assumption.
apply Rle_trans with (Rabs a + (ab + (INR (size l) - 1) * (u/(1+u)) * ab)).
apply Rplus_le_compat_l, Rplus_le_compat_r; assumption.
apply Rle_trans with (Rabs a+(ab+(INR (size l) - 1)*Rabs a)).
2: right; ring.
apply Rplus_le_compat_l,Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
rewrite Hl.
replace (size (r::l')) with (S (size l')) by reflexivity.
rewrite S_INR.
ring_simplify.
apply pos_INR.
left; assumption.
Qed.


Lemma relative_error_N_FLT_strong :
  forall x,
  (Rabs (round beta (FLT_exp emin prec) (Znearest choice) x - x) 
   <= u * Rabs x + /2 * eta)%Re.
Proof. 
intros x.
destruct (error_N_FLT beta emin prec prec_pos choice x)
   as (eps,(eta,(Heps,(Heta,(H1,H2))))).
rewrite H2.
eapply Rle_trans with (Rabs (x * (1 + eps) - x) + Rabs eta).
replace (x * (1 + eps) + eta - x) with ((x * (1 + eps) - x) + eta)
  by ring.
apply Rabs_triang.
apply Rplus_le_compat; try easy.
replace (x * (1 + eps) - x) with (x*eps) by ring.
rewrite Rabs_mult.
rewrite Rmult_comm.
apply Rmult_le_compat_r; try easy.
apply Rabs_pos.
unfold u.
eapply Rle_trans. 
apply Heps.
apply Req_le.
rewrite Rmult_comm.
unfold Rdiv.
f_equal.
f_equal.
lia.
Qed. 


(** Bound on dot product *)
Lemma dot_product_error : forall {d} (a b : 'cV_d), 
           Rabs (dot_product a b r_flt - dot_product a b  (fun x => x)) 
       <= INR d * u * (\sum_(i < d) (Rabs (a i 0) * Rabs (b i 0))) 
        +  ((INR d)*(INR d) * u + INR d) */2 * eta.
Proof with auto with typeclass_instances.
destruct d; intros a b.
  rewrite /dot_product !big_ord0 !(Rplus_0_l, Rmult_0_l, Rminus_0_r, Rabs_R0).
  auto with real.
apply Rle_trans with
  (Rabs (dot_product a b r_flt  - \sum_i (r_flt (a i 0 * b i 0))) 
 + Rabs (\sum_i (r_flt (a i 0 * b i 0))  - dot_product a b  (fun x => x))).
eapply Rle_trans. 
2 : eapply Rabs_triang.
apply Req_le; f_equal; ring.
eapply Rle_trans.
eapply Rplus_le_compat.
unfold dot_product.
eapply Rle_trans.
2 : apply (@error_sum_n_opt_bigop 
       _ (\col_i (r_flt (a i ord0 * b i ord0)))).
2 : intros i j; rewrite !mxE; apply generic_format_round...
apply Req_le; f_equal.
unfold dot_product; f_equal;
  apply eq_bigr; intros; now rewrite !mxE.
(* *)
instantiate (1 := 
   (u * (\sum_i (Rabs (a i 0) * Rabs (b i 0))) + (INR d.+1) */2*eta)).
unfold dot_product.
eapply Rle_trans.
instantiate (1 := Rabs (\sum_i(r_flt(a i 0*b i 0) - a i 0*b i 0))).
apply Req_le.
repeat f_equal.
rewrite big_Rplus_sub.
auto with real.
apply Rge_le; under eq_bigr => i do rewrite <- Rabs_mult.
apply Rle_ge.
eapply Rle_trans.
apply big_triang_le.
rewrite big_Rplus_scal_fun1.
eapply Rle_trans. 
apply big_Rplus_le.
intros i; apply relative_error_N_FLT_strong.
rewrite big_Rplus_half_const.
apply Req_le; auto with real.
rewrite 2!Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc. 
apply Rplus_le_compat_r.
assert
  (H : \sum_i Rabs ((\col_i0 r_flt (a i0 ord0 * b i0 ord0)) i 0)
       <= (1 + u) * (\sum_i (Rabs (a i 0) * Rabs (b i 0))) + INR d.+1 * /2 * eta).
eapply Rle_trans.
apply big_Rplus_le.
intros i.
rewrite !mxE.
replace (r_flt (a i ord0 * b i ord0)) with
  ((r_flt (a i ord0 * b i ord0) - a i ord0 * b i ord0) + a i ord0 * b i ord0) by ring.
apply Rabs_triang.
rewrite big_Rplus_scal_fun1.
rewrite Rmult_assoc. 
rewrite <- big_Rplus_half_const.
apply big_Rplus_le.
intros i.
Rring_tac; rewrite Rmult_plus_distr_r.
ring_simplify.
rewrite Rplus_assoc.
rewrite (Rplus_comm _ (/2*eta)).
rewrite <- Rplus_assoc.
apply Rplus_le_compat.
eapply Rle_trans.
apply relative_error_N_FLT_strong...
apply Rplus_le_compat_r.
rewrite Rmult_comm.
apply Rmult_le_compat_r; autosolve.
rewrite Rabs_mult; apply Rle_refl. 
rewrite Rabs_mult; apply Rle_refl.
eapply Rle_trans.
apply Rplus_le_compat_r, Rmult_le_compat_l.
repeat apply Rmult_le_pos; autosolve.
rewrite INR_succ_minus; autosolve.
apply Rlt_le, Rinv_0_lt_compat.
rewrite <- Rplus_0_r at 1.
apply Rplus_lt_compat; autosolve.
apply Rmult_lt_0_compat; autosolve.
apply bpow_gt_0.
apply H. 
pose (s := \sum_i (Rabs (a i 0) * Rabs (b i 0))).
replace (\sum_(i < d.+1) Rabs (a i 0) * Rabs (b i 0)) with s by easy. 
fold s.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rle_trans with ((INR d.+1 - 1)*(u*s) + (INR d.+1 - 1)*(u/(1+u)) * INR d.+1 */2* eta).
apply Req_le.
field.
apply Rgt_not_eq, Rlt_gt.
rewrite <- Rplus_0_r at 1.
apply Rplus_lt_compat; autosolve.
apply Rmult_lt_0_compat; autosolve.
apply bpow_gt_0.
apply Rle_refl.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
autosolve.
apply Rmult_le_compat_r.
lra.
apply Rmult_le_compat_r.
apply pos_INR.
apply Rmult_le_compat_l.
rewrite INR_succ_minus; autosolve.
apply Rlt_le.
apply opt_le_u.
fold u.
cut ((INR d.+1 - 1)*u * INR d.+1*/ 2 * eta <= INR d.+1 * INR d.+1 *  u * / 2 * eta).
intros Hc.
lra.
apply Rmult_le_compat_r; autosolve.
apply Rmult_le_compat_r; try lra.
rewrite Rmult_comm.
rewrite <- !Rmult_assoc.
apply Rmult_le_compat_r; autosolve.
apply Rmult_le_compat_l; autosolve.
Qed.

(** Bound on matrix-vector product *)

Lemma mx_vec_prod_error : forall {d} (A : 'M_d) (v : 'cV_d), 
           ||| A (x)_m v - A *m v ||| <=  INR d * u * ||| A ||| * ||| v ||| 
         + ((INR d) * (INR d) * u + INR d)* /2 * eta.
Proof.
  destruct d; intros A v.
  rewrite /matrix_norm big_ord0 !(Rplus_0_l, Rplus_0_r, Rmult_0_l).
  auto with real.
  unfold W_mult, matrix_norm at 1.
  under eq_bigr => i do under eq_bigr => j do rewrite !mxE.
  eapply Rle_trans.
  apply big_Rmax_le.
  intros i; apply big_Rplus_le.
  intros j; repeat rewrite ord1.
  apply Rle_trans with
    (Rabs (dot_product (row i A)^T v r_flt 
          - dot_product (row i A)^T v (fun x => x))).
  apply Req_le.
  f_equal; Rring_tac.
  unfold Rminus; f_equal.
  unfold dot_product.
  apply eq_bigr.
  intros x _; repeat f_equal.
  now rewrite col_id. 
  apply Ropp_eq_compat.
  unfold dot_product; apply eq_bigr. 
  intros y _; repeat f_equal.
  now rewrite !mxE.
  eapply Rle_trans.
  apply dot_product_error.
  instantiate (1 :=
                 fun k => INR d.+1*u*(\sum_(i0 < d.+1) Rabs ((row i A)^T i0 k)*Rabs (v i0 k)) +
                         (INR d.+1*INR d.+1*u + INR d.+1)*/2*eta).
  simpl; apply Rle_refl.
  under eq_bigr => i do rewrite Rplus_comm big_Rplus_half_const.
  rewrite big_Rmax_half_const.
  apply Rplus_le_compat.
  under eq_bigr => i do rewrite <- big_Rplus_scal_fun1.
  rewrite big_Rmax_scal; autosolve.
  repeat rewrite Rmult_assoc;
  repeat apply Rmult_le_compat_l; autosolve.
  eapply Rle_trans.
  under eq_bigr => i do under eq_bigr => j do under eq_bigr => k do rewrite !mxE. 
  apply big_Rmax_le.
  intros i; apply big_Rplus_le.
  intros j; apply big_Rplus_le.
  intros k.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply (leq_bigmax (fun l => Rabs (v l j))). 
  simpl.
  under eq_bigr => i do under eq_bigr => j do under eq_bigr => k do rewrite Rmult_comm.
  eapply Rle_trans.
  apply big_Rmax_le.
  intros i.
  apply big_Rplus_le.
  intros j.
  apply Rle_trans with (\sum_(k < d.+1) (||| v ||| * Rabs (A i k))).
  apply big_Rplus_le.
  intros k.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply big_Rmax_le. intros s; rewrite big_ord1 ord1; apply Rle_refl. 
  apply Rle_refl.
  under eq_bigr => i do under eq_bigr => j do (rewrite <- big_Rplus_scal_fun2).
  under eq_bigr => i do (rewrite <- big_Rplus_scal_fun1).
  rewrite big_Rmax_scal; autosolve.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r; autosolve.
  apply big_Rmax_le.
  intros i; rewrite big_ord1; apply Rle_refl.
  replace (INR 1) with 1.
  lra.
  auto with real.
  intros i; apply big_Rplus_pos.
  intros j; repeat apply Rmult_le_pos; autosolve.
  apply big_Rplus_pos.
  intros k; apply Rmult_le_pos; apply Rabs_pos.
  autosolve.
  rewrite <- (Rplus_0_r 0).
  apply Rplus_le_compat; autosolve.
Qed.

End MatrixRndError.

Section FP_prel.

Notation "X (x)_m Y" := (W_mult r_flt X Y) (at level 50).

Notation "a (x)_sm A" := (map_mx (fun x => r_flt (a*x)) A) (at level 50).

Section Const_prod_mat_aux. 

(** Bounds on the matrix coefficients *)
Variables a a' B : R.

Lemma mat_coeffs_error_aux d (A : 'M[R]_d) : Rabs (a' - a) <= B ->
     ||| a' (x)_sm A -  a *_sm A |||
   <= (B +  u* (B + Rabs a)) * ||| A ||| + INR d * /2 * eta.
Proof.
destruct d as [|d] ; intros Ha.
rewrite /matrix_norm !big_ord0 !(Rmult_0_r, Rmult_0_l); auto with real.
rewrite Rmult_plus_distr_r Rplus_assoc Rplus_comm.
apply Rle_trans with
  (||| a' (x)_sm A - a' *_sm A ||| + ||| a' *_sm A - a *_sm A |||).
eapply Rle_trans.
2 : apply matrix_norm_triang.
unfold matrix_norm.
apply Req_le; apply eq_bigr; intros x _; apply eq_bigr; intros y _; f_equal.
rewrite !mxE.
Rring_tac; lra.
unfold Rminus; auto with real.
apply Rplus_le_compat.
unfold matrix_norm at 1.
eapply Rle_trans.
apply big_Rmax_le.
intros i; apply big_Rplus_le.
intros j; rewrite !mxE.
apply relative_error_N_FLT_strong.
under eq_bigr => i do rewrite big_Rplus_half_const.
rewrite big_Rmax_half_const.
apply Rplus_le_compat; try lra.
under eq_bigr => i do under eq_bigr => j do (rewrite Rabs_mult; rewrite <- Rmult_assoc).
under eq_bigr => i do rewrite <- big_Rplus_scal_fun2.
rewrite big_Rmax_scal.
simpl.
unfold matrix_norm.
apply Rmult_le_compat_r.
apply big_Rmax_pos.
apply Rmult_le_compat_l.
autosolve.
apply Rplus_le_reg_r with (-Rabs a).
ring_simplify.
eapply Rle_trans.
now apply Rabs_triang_inv; autosolve.
assumption.
repeat apply Rmult_le_pos; autosolve.
apply Rabs_pos.
intros i; apply big_Rplus_pos.
intros j; repeat apply Rmult_le_pos; autosolve.
apply Rabs_pos.
repeat apply Rmult_le_pos; unfold eta; autosolve.
unfold matrix_norm at 1.
under eq_bigr => i do under eq_bigr => j do rewrite !mxE.
unfold matrix_norm.
rewrite <- big_Rmax_scal.
apply big_Rmax_le.
intros i.
rewrite big_Rplus_scal_fun2.
apply big_Rplus_le.
intros j.
simpl.
Rring_tac.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
rewrite Rabs_mult.
apply Rmult_le_compat_r.
apply Rabs_pos.
auto with real.
eapply Rle_trans.
2: apply Ha.
apply Rabs_pos.
Qed.

End Const_prod_mat_aux. 

Section Const_prod_mat.

Variables a a' B : R.

Variable C D : R. 
Hypothesis HC : 0 <= C.
Hypothesis HD : 0 <= D. 

Lemma mat_coeffs_error d (A A' : 'M[R]_d) : Rabs (a' - a) <= B 
     -> ||| A' - A ||| <= C * u  * ||| A ||| + D * eta
      -> ||| a' (x)_sm A' -  a *_sm A ||| 
       <= ((1 + C*u)*(u*(B + Rabs a)+B) + C*u*Rabs a)*||| A |||
          + ((1 + u) * (B + Rabs a) * D + INR d * /2) * eta. 
Proof.
destruct d as [|d].
  rewrite /matrix_norm !big_ord0 !(Rmult_0_l, Rmult_0_r, Rplus_0_l, Rplus_0_r).
  intros Ha HA. 
  rewrite Rmult_assoc.
 apply Rmult_le_pos; auto with real.
 apply Rmult_le_pos; repeat apply Rplus_le_le_0_compat; try lra.
  now apply Rlt_le; apply Rdiv_lt_0_compat; try apply bpow_gt_0; auto with real.
  apply Rle_trans with (2 := Ha); apply Rabs_pos.
  apply Rabs_pos.
intros Ha HA.
apply Rle_trans with 
   (||| a' (x)_sm A' -  a *_sm A' ||| +
    ||| a *_sm A' -  a *_sm A |||).
eapply Rle_trans.
2 : apply matrix_norm_triang.
unfold matrix_norm.
apply Req_le; apply eq_bigr; intros i _; apply eq_bigr;
intros j _; f_equal; rewrite !mxE.
Rring_tac; ring.
eapply Rle_trans. 
apply Rplus_le_compat.
apply mat_coeffs_error_aux. 
apply Ha. 
instantiate (1 := 
 (Rabs a * (C * u * ||| A ||| + D * eta))).
eapply Rle_trans. 
2 : { apply Rmult_le_compat_l.
apply Rabs_pos.
apply HA. }
unfold matrix_norm.
rewrite <- big_Rmax_scal.
apply big_Rmax_le.
intros i; simpl. 
rewrite big_Rplus_scal_fun2.
apply big_Rplus_le.
intros j.
rewrite !mxE.
Rring_tac.
rewrite Ropp_mult_distr_r.
rewrite <- Rabs_mult.
apply Req_le; f_equal.
auto with real. 
apply Rabs_pos.
assert (HA' : ||| A' ||| <= (1+C*u)*||| A ||| + D*eta).
apply Rle_trans with (|||A' - A||| + |||A|||).
eapply Rle_trans. 
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP. 
intros i j; rewrite !mxE.
Rring_tac.
rewrite Rplus_assoc Rplus_opp_l. 
auto with real.
eapply Rle_trans. 
apply Rplus_le_compat.
apply HA.
apply Rle_refl.
apply Req_le; ring.
eapply Rle_trans. 
repeat apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
eapply Rle_trans. 
2 : { apply Rplus_le_compat.
apply Rle_trans with (2:=Ha).
apply Rabs_pos.
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
eapply Rle_trans.   
2 : {apply Rplus_le_compat. 
apply Rle_trans with (2:=Ha).
apply Rabs_pos.
apply Rabs_pos. }
auto with real. }
auto with real.
apply HA'.
apply Req_le; ring.
Qed. 

Lemma rnd_matrix_error d (A A' : 'M[R]_d) :
    ||| rnd_mat A r_flt - A ||| <= u * ||| A ||| + INR d * / 2 * eta.
Proof with auto with typeclass_instances.
  destruct d as [|d].
    rewrite /matrix_norm !big_ord0 !(Rmult_0_l, Rmult_0_r); auto with real.
    unfold matrix_norm.
    rewrite <- big_Rmax_scal.
    rewrite <- big_Rmax_half_const.
    apply big_Rmax_le.
    intros i.
    rewrite big_Rplus_scal_fun2.
    rewrite Rmult_assoc.
    generalize (big_Rplus_half_const _
                  (fun l => u * Rabs (A i l)) (/ 2 *eta)).
    intros Hc.
    apply Req_le in Hc.
    eapply Rle_trans.
    2: apply Hc.
    apply big_Rplus_le.
    intros j.
    rewrite !mxE.
    apply relative_error_N_FLT_strong...
    intros i; repeat apply Rmult_le_pos; try lra.
    apply bpow_ge_0.
    apply big_Rplus_pos.
    intros j; apply Rabs_pos.
    unfold eta; repeat apply Rmult_le_pos; try lra.
    apply pos_INR.
    apply bpow_ge_0.
    repeat apply Rmult_le_pos; try apply bpow_ge_0; lra.
Qed.

End Const_prod_mat.

Section bounds_plus_flt.

(** Generic results to bound local errors *)

Variable d : nat. 
Variable y : 'cV[R]_d.
Variables A1 A2 : 'M[R]_d.
Variables X1 X2 : 'cV[R]_d.
Variables C1 C2 : R. 
Variables D1 D2 : R. 

Hypothesis Hx1 : format_mat X1.
Hypothesis Hx2 : format_mat X2.

Lemma build_vec_plus_error : 
    ||| X1 - A1 *m y ||| <= C1 * ||| y ||| + D1*eta ->
    ||| X2 - A2 *m y ||| <= C2 * ||| y ||| + D2*eta -> 
    ||| X1 (+)_m X2 - (A1 + A2) *m y |||
         <= (C1 + C2 + u* (||| A1 ||| + ||| A2 ||| + C1 + C2))*||| y |||
            + (1+u)*(D1 + D2)*eta. 
Proof with auto with typeclass_instances.
destruct d as [|d'].
  rewrite /matrix_norm !big_ord0 !(Rmult_0_l, Rmult_0_r, Rplus_0_l).
  intros H1 H2.
  rewrite Rmult_assoc.
  apply: Rmult_le_pos.
    suff : 0 <= u by lra.
    now apply Rlt_le; apply Rdiv_lt_0_compat; try apply bpow_gt_0; auto with real.
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_le_0_compat; auto with real.
intros H1 H2.
eapply Rle_trans.
instantiate
  (1 := (||| X1 (+)_m X2 - (X1 + X2) ||| + ||| X1 + X2 - (A1 + A2) *m y |||)).
eapply Rle_trans. 
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP=> i j. 
repeat (rewrite mat_apply_add_distr mat_apply_opp_distr mat_apply_add_distr).
Rring_tac; rewrite !mxE; lra. 
eapply Rle_trans. 
apply Rplus_le_compat.
instantiate
  (1 := (u *(||| A1 ||| + ||| A2 ||| + C1 + C2)*||| y ||| + u*(D1 + D2)*eta)).
eapply Rle_trans.
instantiate (1 := (u *||| X1 + X2 |||)).
unfold matrix_norm.
rewrite <- big_Rmax_scal; autosolve.
apply big_Rmax_le.
intros i.
rewrite big_Rplus_scal_fun2.
repeat rewrite big_ord1.
rewrite !mxE.
eapply Rle_trans.
apply error_le_plus_opt...
fold u.
Rring_tac.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rlt_le; apply opt_le_u.
eapply Rle_trans.
apply Rmult_le_compat_l.
autosolve.
apply matrix_norm_triang.
eapply Rle_trans.
apply Rmult_le_compat_l.
repeat apply Rmult_le_pos; autosolve.
apply Rplus_le_compat.
instantiate (1 :=
  (|||A1||| + C1)*||| y ||| + D1*eta).
apply Rle_trans with 
   (||| X1 - A1 *m y ||| + ||| A1 *m y |||). 
eapply Rle_trans.
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra.
eapply Rle_trans.
apply Rplus_le_compat.
apply H1.
apply norm_submult. 
apply Req_le; ring.
instantiate (1 :=
  (|||A2||| + C2)*||| y ||| + D2*eta).
apply Rle_trans with 
   (||| X2 - A2 *m y ||| + ||| A2 *m y |||). 
eapply Rle_trans.
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra.
eapply Rle_trans.
apply Rplus_le_compat.
apply H2.
apply norm_submult. 
apply Req_le; ring.
apply Req_le; ring.
instantiate (1:= (C1+C2)*||| y ||| + (D1+D2)*eta).
apply Rle_trans with (||| X1 - A1 *m y ||| + ||| X2 - A2 *m y |||).
eapply Rle_trans. 
2: apply matrix_norm_triang.
unfold matrix_norm.
apply big_Rmax_le.
intros i; apply big_Rplus_le.
intros j; rewrite !mxE.
Rring_tac. 
simpl; apply Req_le; f_equal.
  repeat rewrite Rplus_assoc. 
  f_equal. 
  symmetry.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  f_equal.
  rewrite <- Ropp_plus_distr.
  f_equal.
  symmetry;
  under eq_bigr => k do (Rring_tac; rewrite mat_apply_add_distr Rmult_plus_distr_r). 
  rewrite big_Rplus_add Rplus_comm; f_equal.
  lra. 
  apply Req_le; ring.
Qed.

End bounds_plus_flt.

Section bounds_mult_flt. 

Variable d : nat. 
Variable y : 'cV[R]_d.
Variables A1 A2 A3 A2f : 'M[R]_d.
Variables X1 X2 X3 : 'cV[R]_d.
Variables C1 C2 C3 D1 D2 D3 : R. 

Hypothesis C3pos : 0 <= C3.
Hypothesis D3pos : 0 <= D3.

Hypothesis Hx1 : format_mat X1.

Lemma build_vec_mult_error :
  let K := C2*|||A3||| + C3*|||A2||| + C2*C3 + (C3 + |||A3|||)*D2*eta
  in
  let D:= (1 + u) * (D1 + (1 + INR d*u)*(C2 + D2*eta + |||A2|||)*D3
                     + (INR d * INR d *u + INR d) */2)
  in
  ||| X1 - A1 *m y ||| <= C1 * ||| y ||| + D1 * eta ->
  ||| A2f - A2 ||| <= C2 + D2 * eta ->
  ||| X3 - A3 *m y ||| <= C3 * ||| y ||| + D3 * eta ->
  ||| (X1 (+)_m (A2f (x)_m X3)) - (A1 + A2 *m A3) *m y |||
  <= ((1+u)*(C1 + (1 + INR d*u)*K) + u * ||| A1 ||| + ((INR d + 1)*u
    + (INR d * u *u))* |||A2||| * |||A3|||) * ||| y ||| + D * eta.
Proof with auto with typeclass_instances.
intros K D H1 H2 H3.
pose (CC := ((1 + INR d*u)*(C2*|||A3||| + C3*|||A2||| + C2*C3 
      + (C3 + |||A3|||)*D2*eta) + (INR d*u*|||A2|||*|||A3|||))). 
pose (DD := (1 + INR d*u)*(C2 + D2*eta + |||A2|||)*D3
           + (INR d * INR d *u + INR d) */2).
assert (H : ||| A2f (x)_m X3 - (A2 *m A3) *m y ||| 
          <= CC * ||| y ||| + DD * eta).
apply Rle_trans with 
  (||| A2f (x)_mX3 - (A2f *m A3) *m y ||| + 
   ||| A2f *m A3 *m y - (A2 *m A3) *m y |||).
eapply Rle_trans.
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP=> i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra. 
apply Rle_trans with 
  (||| A2f (x)_m X3 - A2f *m X3 ||| + 
   ||| A2f *m X3 - (A2f *m A3) *m y ||| + 
   ||| A2f *m A3 *m y - (A2 *m A3) *m y |||).
eapply Rle_trans.
2 : { apply Rplus_le_compat_r.
apply matrix_norm_triang. }
apply Rplus_le_compat_r.
apply Req_le; f_equal.
apply/matrixP=> i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra.
eapply Rle_trans.
apply Rplus_le_compat.
eapply Rle_trans. 
apply Rplus_le_compat.
apply mx_vec_prod_error.
rewrite <- mulmxA, <- (mulmxBr A2f).
apply norm_submult.
repeat apply Rplus_le_compat.
apply Rmult_le_compat_l.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
apply matrix_norm_pos.
instantiate (1 := 
  (C3 + ||| A3 |||) * ||| y ||| + D3 * eta).
eapply Rle_trans.
instantiate (1:= 
  ||| X3 - A3 *m y ||| + ||| A3 *m y |||).
eapply Rle_trans.
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra.
rewrite Rmult_plus_distr_r.
rewrite Rplus_assoc. 
rewrite (Rplus_comm _ (D3*eta)). 
rewrite <- !Rplus_assoc.
apply Rplus_le_compat.
apply H3.
apply norm_submult.
apply Rle_refl. 
apply Rmult_le_compat.
apply matrix_norm_pos.
apply matrix_norm_pos.
apply Rle_trans with 
  ((C2 + D2 * eta) + |||A2|||).
eapply Rle_trans.
instantiate (1 := 
  (||| A2f - A2 ||| + |||A2|||)).
eapply Rle_trans.
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra.
apply Rplus_le_compat; try easy.
apply Rle_refl.
apply Req_le; reflexivity. 
apply H3.
instantiate (1:= 
  (C2 + D2 * eta)*(|||A3|||*|||y|||)).
eapply Rle_trans. 
2 : apply Rmult_le_compat.
4 : apply H2.
2 : apply matrix_norm_pos.
instantiate (1 := ||| A3 *m y |||).
2 : apply matrix_norm_pos.
2 : apply norm_submult.
rewrite <- 2!mulmxA, <- mulmxBl.
apply norm_submult.
eapply Rle_trans.
repeat apply Rplus_le_compat.
2,3,4 : apply Req_le; reflexivity.
repeat apply Rmult_le_compat; try lra.
repeat apply Rmult_le_pos; autosolve.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try apply matrix_norm_pos; autosolve.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try apply matrix_norm_pos; try easy. 

autosolve.
autosolve.
apply matrix_norm_pos.
autosolve.
autosolve.
apply Req_le; reflexivity.
apply bpow_ge_0.
apply Req_le; reflexivity. 
apply Req_le; reflexivity. 
instantiate (1:=
  (C2 + D2 * eta) + |||A2|||).
eapply Rle_trans. 
2 : { apply Rplus_le_compat. 
apply H2.
apply Req_le; reflexivity. }
eapply Rle_trans. 
2 : apply matrix_norm_triang. 
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
lra.
apply Req_le; reflexivity.
replace (bpow beta (1 - prec) * / 2)
   with u by reflexivity.
unfold CC, DD.
apply Req_le; ring.
eapply Rle_trans.
apply build_vec_plus_error; try easy.
intros i j.
rewrite !mxE.
unfold dot_product; elim/big_ind:_=> //.
apply generic_format_0.
intros a b Ha Hb.
apply generic_format_round...
intros x _.
apply generic_format_round...
apply H1.
apply H.
eapply Rle_trans. 
apply Rplus_le_compat.
2 : apply Req_le; reflexivity.
apply Rmult_le_compat_r.  
apply matrix_norm_pos.
repeat apply Rplus_le_compat.
1,2,3: apply Req_le; reflexivity.
apply Rmult_le_compat_l. 
autosolve. 
repeat apply Rplus_le_compat.
apply Req_le; reflexivity.
apply norm_submult.
1,2,3:apply Req_le; reflexivity.
unfold D, CC, DD; apply Req_le.
f_equal.
apply Rmult_eq_compat_r.
pose (B := (1 + INR d * u)); fold B.
pose (G := INR d * u); fold G.
pose (N := ||| A2 ||| * ||| A3 |||);fold N. 
transitivity 
  (C1 + (B * K + G * N) + u * (||| A1 ||| + N + C1 + (B * K + G * N))). 
unfold N, K; ring. 
transitivity ((1 + u) * (C1 + B * K) +  u * ||| A1 ||| + ((G + u) + G * u) * N);
  try (unfold N; ring).
unfold G, N.
1,2: ring.
Qed.

End bounds_mult_flt.


Section bounds_mult_flt_wk.

Variable d : nat. 
Variable y : 'cV[R]_d.
Variables A1 A2 A3 A2f : 'M[R]_d.
Variables X1 X3 : 'cV[R]_d.
Variables C1 C2 C3 D1 D2 D3 : R. 

Hypothesis C1pos : 0 <= C1.
Hypothesis C2pos : 0 <= C2.
Hypothesis C3pos : 0 <= C3.
Hypothesis D1pos : 0 <= D1.
Hypothesis D2pos : 0 <= D2.
Hypothesis D3pos : 0 <= D3.

Hypothesis Hx1 : format_mat X1.

Lemma build_vec_mult_error_wk :
  let K := C2*|||A3||| + C3*|||A2||| + C2*C3 + (C3 + |||A3|||)*D2*eta
    in
  ||| X1 - A1 *m y ||| <= C1 * ||| y ||| + D1 * eta ->
  ||| A2f - A2 ||| <= C2 + D2 * eta ->
  ||| X3 - A3 *m y ||| <= C3 * ||| y ||| + D3 * eta ->
  INR d * u <= 1/100 -> (emin <= 0)%Z ->
  ||| (X1 (+)_m (A2f (x)_m X3)) - (A1 + A2 *m A3) *m y |||
    <= ((1 +3/100)*(C1 + K) + u*||| A1 |||
        + ((INR d + 1 + 1/100)*u)* |||A2|||*|||A3|||) * ||| y |||
  + ((1+3/100)* (D1 + (C2 + D2 + |||A2|||)*D3) + (6/10*INR d))* eta.
Proof.
destruct d as [|d'].
  rewrite /matrix_norm !big_ord0 !(Rmult_0_l, Rmult_0_r, Rplus_0_l, Rplus_0_r).
  intros H1 H2 H3 Hdu He.
  rewrite Rmult_assoc.
  apply Rmult_le_pos.
  lra.
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_le_0_compat; try easy.
  rewrite Rmult_assoc.
  apply Rmult_le_pos; try easy.
  apply Rplus_le_le_0_compat; easy.
intros K H1 H2 H3 Hdu He.
assert (H01 : u <= 1/100).
apply Rle_trans with (INR d'.+1 * u).
rewrite <- (Rmult_1_l u) at 1.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; autosolve.
apply (le_INR 1); lia. 
easy.
eapply Rle_trans.
apply: build_vec_mult_error H1 H2 H3; try easy.
apply Rplus_le_compat.
fold K.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rplus_le_compat. 
apply Rplus_le_compat_r.
apply Rle_trans with 
  ((1 + 1/100) * (C1 + (1 + 1/100) * K)).
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; autosolve. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; autosolve.
unfold K.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat. 
rewrite <- (Rplus_0_r 0). 
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0). 
apply Rplus_le_compat.
apply Rmult_le_pos; try easy.
apply matrix_norm_pos. 
apply Rmult_le_pos; try easy.
apply matrix_norm_pos.
now apply Rmult_le_pos.
repeat apply Rmult_le_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply matrix_norm_pos.
easy.
apply bpow_ge_0.
lra.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
unfold K.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat. 
rewrite <- (Rplus_0_r 0). 
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0). 
apply Rplus_le_compat.
apply Rmult_le_pos; try easy.
apply matrix_norm_pos. 
apply Rmult_le_pos; try easy.
apply matrix_norm_pos.
now apply Rmult_le_pos.
repeat apply Rmult_le_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply matrix_norm_pos.
easy.
apply bpow_ge_0.
lra.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat.
lra.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
unfold K.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat. 
rewrite <- (Rplus_0_r 0). 
apply Rplus_le_compat.
rewrite <- (Rplus_0_r 0). 
apply Rplus_le_compat.
apply Rmult_le_pos; try easy.
apply matrix_norm_pos. 
apply Rmult_le_pos; try easy.
apply matrix_norm_pos.
now apply Rmult_le_pos.
repeat apply Rmult_le_pos; autosolve.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply matrix_norm_pos.
lra.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rmult_le_compat_r.
apply matrix_norm_pos.
rewrite <- Rmult_plus_distr_r.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rplus_le_compat_l; try easy.
apply Rmult_le_compat_r.
apply bpow_ge_0.
eapply Rle_trans.
apply Rmult_le_compat_r.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
repeat apply Rmult_le_pos; try easy; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra; try easy. 
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_pos.
apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra; 
try (apply pos_INR).
apply bpow_ge_0.
apply pos_INR.
instantiate (1:= 1 + 1/100).
apply Rplus_le_compat_l; try easy.
rewrite Rmult_plus_distr_l.
apply Rplus_le_compat.
apply Rle_trans with 
  ((1+1/100)*(D1 + (1+1/100)*(C2 + D2 + |||A2|||)*D3)).
apply Rmult_le_compat_l; try lra.
apply Rplus_le_compat_l.
repeat apply Rmult_le_compat; try lra.
apply Rmult_le_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; autosolve.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy; try lra.
apply Rmult_le_pos; autosolve. 
apply matrix_norm_pos. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; autosolve.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply Rmult_le_pos; autosolve.
apply matrix_norm_pos.
repeat apply Rplus_le_compat; try apply Rle_refl.
rewrite <- Rmult_1_r. 
apply Rmult_le_compat_l; try easy.
replace 1 with (bpow beta 0).
apply bpow_le.
easy.
reflexivity.
rewrite Rmult_plus_distr_l.
rewrite (Rmult_plus_distr_l (1 + 3/100)).
apply Rplus_le_compat.
apply Rmult_le_compat_r; try easy.
lra.
rewrite <- Rmult_assoc.
rewrite <- (Rmult_assoc _ _ D3).
apply Rmult_le_compat_r; try easy.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply matrix_norm_pos.
lra.
apply Rle_trans with 
  ((1 + 1 / 100)/2 * ((INR d'.+1 * INR d'.+1 * u + INR d'.+1))).
apply Req_le; lra.
apply Rle_trans with 
  ((1 + 1 / 100) / 2 * (1+1/100)*INR d'.+1).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_le_compat_l; try lra.
rewrite Rmult_plus_distr_r.
rewrite (Rplus_comm (1*INR d'.+1)).
apply Rplus_le_compat.
rewrite Rmult_comm.
apply Rmult_le_compat_r; autosolve. 
auto with real.
apply Rmult_le_compat_r.
apply pos_INR.
lra.
Qed.

End bounds_mult_flt_wk. 

End FP_prel.

End FP_loc_err.
