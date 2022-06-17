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
Require Import Epsilon FunctionalExtensionality Lra Lia.

From mathcomp 
Require Import all_ssreflect ssralg finalg matrix. 
Require Import Rstruct Compl Norms.

From Flocq.Core 
Require Import Core. 
From Flocq.Prop 
Require Import Mult_error Plus_error Relative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

From Flocq Require Import Core Plus_error Sterbenz Operations.

Require Import List.

Open Scope R_scope.

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

(** Optimal bound on summation (with lists) *)

Theorem error_sum_n_opt: forall l: list R,
    Forall format l ->
    let e:= fold_right Rplus 0 l in
    let f:= fold_right (fun x y => round_flt (x+y)) 0 l in
    let a:= fold_right Rplus 0 (map Rabs l) in
      Rabs (f-e) <= (INR (length l) -1)*(u/(1+u))*a.
Proof with auto with typeclass_instances.
intros l; induction l.
intros _; simpl.
unfold Rminus; rewrite Ropp_0 Rplus_0_l Rabs_R0 Rmult_0_r.
apply Rle_refl.
intros H e' f' ab'.
pose (e:= fold_right Rplus 0 l).
pose (f:= fold_right (fun x y => round_flt (x+y)) 0 l).
pose (ab:= fold_right Rplus 0 (map Rabs l)).
replace f' with (round_flt (a+f)) by reflexivity.
replace e' with (a+e) by reflexivity.
replace (round_flt (a + f) - (a + e)) with
    ((f-e)+(round_flt(a+f)-(a+f))) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
assert (Rabs (f - e) <= (INR (length l) - 1) * (u/(1+u)) * ab).
apply IHl.
now inversion H.
eapply Rle_trans.
apply Rplus_le_compat.
apply H0.
2: replace ab' with (Rabs a + ab) by reflexivity.
2: replace (length (a::l)) with (S (length l)) by reflexivity.
2: rewrite S_INR.
2: apply Rle_trans with 
  ((INR (length l) - 1) * (u/(1+u)) * ab + (u/(1+u))*
       (Rabs a +(ab+(INR (length l)-1)*Rabs a))).
3: right; ring.
2: apply Rle_refl.
apply Rle_trans with 
  ((u/(1+u)) * (ab + INR (length l) * Rabs a)).
2: right; ring.
(* . assertions *)
assert (Ff: format f).
unfold f; case l; simpl.
apply generic_format_0...
intros; apply generic_format_round...
assert (Fa: format a).
now inversion H.
assert (Y:Rabs e <= ab).
clear; induction l.
unfold e, ab; simpl.
rewrite Rabs_R0; apply Rle_refl.
unfold e, ab; simpl.
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
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rlt_le, Rinv_0_lt_compat.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra; try apply bpow_ge_0.
lra. 
apply Rplus_le_reg_l with (-ab); ring_simplify.
apply Rmult_le_pos.
apply pos_INR.
apply Rabs_pos.
(* . *)
intros M1.
case_eq l.
(* .. case l = nil *)
intros V; unfold f, ab; rewrite V; simpl.
rewrite Rplus_0_r.
rewrite round_generic...
rewrite Rminus_diag_eq; try reflexivity.
rewrite Rabs_R0.
rewrite Rmult_0_l Rplus_0_l Rmult_0_r.
apply Rle_refl.
(* .. case l != nil *)
intros r l' Hl; rewrite <- Hl.
case (Rle_or_lt ab ((u/(1+u))*(Rabs a))).
intros M2.
apply Rle_trans with (Rabs f).
rewrite Rplus_comm.
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
apply Rle_trans with (bpow 0*Rabs a).
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rmult_le_reg_r with (1+u).
apply Rle_lt_trans with u.
apply Rmult_le_pos.
apply bpow_ge_0.
lra.
lra.
replace (bpow 0) with 1 by reflexivity.
replace (u / (1 + u) * (1 + u)) with u. 
ring_simplify.
lra.
field.
apply Rgt_not_eq, Rlt_gt.
apply Rle_lt_trans with (0 + 0); try lra.
apply Rplus_lt_compat; try lra.
apply bpow_gt_0.
replace (bpow 0) with 1 by reflexivity.
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
apply Rle_trans with (Rabs a +(Rabs e +(INR (length l) - 1) * (u/(1+u)) * ab)).
apply Rplus_le_compat_l.
apply Rle_trans with (1:=Rabs_triang _ _).
apply Rplus_le_compat_l; assumption.
apply Rle_trans with (Rabs a + (ab + (INR (length l) - 1) * (u/(1+u)) * ab)).
apply Rplus_le_compat_l, Rplus_le_compat_r; assumption.
apply Rle_trans with (Rabs a+(ab+(INR (length l) - 1)*Rabs a)).
2: right; ring.
apply Rplus_le_compat_l,Rplus_le_compat_l.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
rewrite Hl.
replace (length (r::l')) with (S (length l')) by reflexivity.
rewrite S_INR.
ring_simplify.
apply pos_INR.
left; assumption.
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

Definition rnd_mat {m n} (A : 'M[R]_(m,n)) (W : R -> R) :=
                                 (\matrix_(i, j) (W (A i j)))%R.

Definition Rnd_Rplus (a b : R) := r_flt (a + b).
Definition Rnd_Rmult (a b : R) := r_flt (a*b). 

Notation "a (+) b" := (Rnd_Rplus a b).
Notation "a (x) b" := (Rnd_Rmult a b) (at level 44).

Notation "A (+)_m B" := (rnd_mat (A + B) r_flt) (at level 50). 

Section MatrixRndError. 

(** Optimal bound on summation (with vectors/bigops) *)

Theorem error_sum_n_opt_bigop : forall {d} (v : 'cV_d.+1),
    format_mat v -> 
    let e:= \sum_(i < d.+1) (v i ord_max) in 
    let f:= \big[Rnd_Rplus / 0%R]_(i < d.+1) (v i ord_max) in 
    let a:= \sum_(i < d.+1) Rabs (v i ord_max) in 
      Rabs (f-e) <= (INR d.+1 -1)*(u/(1+u))*a.
Proof. 
intros d v H e f a.
generalize (error_sum_n_opt); intros Hg.
assert (Hf : Forall format (vec_to_list v)).
now apply vec_to_list_format.
specialize (Hg beta emin prec choice prec_pos (vec_to_list v) Hf).
unfold e, f, a.
assert (Hd : length (vec_to_list v) = d.+1).
apply vec_to_list_length; try easy.
pose (f' := fold_right (fun x y : R => 
                 r_flt (x + y)) 0 (vec_to_list v)).
pose (e' := fold_right Rplus 0 (vec_to_list v)).
replace (Rabs (\big[Rnd_Rplus/0]_(i < d.+1) v i ord_max 
             - \sum_(i < d.+1) v i ord_max))%R
   with (Rabs (f' - e')).
rewrite <- Hd at 1.
fold u in Hg.
apply Rle_trans with ((INR (length (vec_to_list v)) - 1) 
    * (u/(1+u)) * fold_right Rplus 0 (map Rabs (vec_to_list v))).
unfold f', e'.
unfold e, f in Hg.
apply Hg.
apply Req_le.
f_equal.
assert (Hy : forall i, Rabs (v i ord_max) 
           = nth i (map Rabs (vec_to_list v)) 0).
intros i.
replace 0 with (Rabs 0) by (apply Rabs_R0).
rewrite map_nth.
f_equal.
symmetry; apply vec_to_list_corr; try easy.
transitivity (\sum_(i < d.+1) 
     (nth i (map Rabs (vec_to_list v)) 0)).
symmetry; apply list_fold_right_sum'.
now rewrite map_length.
f_equal; apply functional_extensionality.
intros x; f_equal.
now rewrite Hy.
repeat f_equal.
transitivity 
   (\big[Rnd_Rplus/0]_(i < d.+1) (nth i (vec_to_list v) 0)).
symmetry; now apply list_fold_right_rnd_sum'.
elim/big_ind2:_=> //.
intros x1 x2 y1 y2 Hx Hy; now rewrite Hx Hy.
intros i _; apply vec_to_list_corr; try easy.
transitivity 
   (\sum_(i < d.+1) (nth i (vec_to_list v) 0)).
symmetry; now apply list_fold_right_sum'.
elim/big_ind2:_=> //.
intros x1 x2 y1 y2 Hx Hy; now rewrite Hx Hy.
intros i _; now apply vec_to_list_corr.
Qed.

(** Rounded dot product *)
Definition dot_product {d} (a b : 'cV[R]_d) W := 
           \big[(fun x y => W (x + y)) / 0%R]_(i < d) (W ((a i ord_max) * (b i ord_max))).

Fact mulmx_rnd_key : unit. Proof. by []. Qed.

Definition mulmx_rnd {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) W : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) 
     \big[(fun x y => W (x + y)) / 0%R]_j (W (A i j * B j k)).

Notation "X (x)_m Y" := (mulmx_rnd X Y r_flt) (at level 50).

Notation "a (x)_sm A" := (map_mx (fun x => r_flt (a*x)) A) (at level 50).

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
Lemma dot_product_error : forall {d} (a b : 'cV_d.+1), 
           Rabs (dot_product a b r_flt - dot_product a b  (fun x => x)) 
       <= INR d.+1 * u * (\sum_(i < d.+1) (Rabs (a i ord_max) * Rabs (b i ord_max))) 
        +  ((INR d.+1)*(INR d.+1) * u + INR d.+1) */2 * eta.
Proof with auto with typeclass_instances.
intros d a b. 
apply Rle_trans with 
  (Rabs (dot_product a b r_flt 
        - \sum_i (r_flt (a i ord_max * b i ord_max))) 
 + Rabs (\sum_i (r_flt (a i ord_max * b i ord_max)) 
        - dot_product a b  (fun x => x))).
eapply Rle_trans. 
2 : eapply Rabs_triang.
apply Req_le; f_equal; ring.
eapply Rle_trans.
eapply Rplus_le_compat.
eapply Rle_trans.
2 : apply (@error_sum_n_opt_bigop 
       _ (\col_i (r_flt (a i ord_max * b i ord_max)))).
2 : intros i j; rewrite !mxE; apply generic_format_round...
apply Req_le; f_equal.
unfold dot_product; f_equal; (f_equal; 
apply functional_extensionality;
intros x; f_equal; now rewrite !mxE).
(* *)
instantiate (1 := 
   (u * (\sum_i (Rabs (a i ord_max) * Rabs (b i ord_max))) 
    + (INR d.+1) */2*eta)).
unfold dot_product.
eapply Rle_trans.
instantiate (1 := 
   (Rabs (\sum_i(r_flt(a i ord_max*b i ord_max) - a i ord_max*b i ord_max)))).
apply Req_le.
repeat f_equal.
elim/big_ind3:_ => //; try auto with real.
intros x1 x2 x3 y1 y2 y3 H1 H2.
rewrite <- H1. 
rewrite <- H2.
transitivity ((x3 - x1) + (y3 - y1)); 
auto with real.
transitivity ((x3 + y3) - (x1 + y1));
auto with real.
lra.
apply Rle_trans with 
   (\sum_i (u * (Rabs (a i ord_max * b i ord_max)) + /2 * eta)).
elim/big_ind2:_=> //.
rewrite Rabs_R0; auto with real.
intros x1 x2 y1 y2 Hx Hy.
eapply Rle_trans. 
apply Rabs_triang.
auto with real.
intros i _.
apply relative_error_N_FLT_strong.
rewrite big_Rplus_half_const.
apply Rplus_le_compat.
elim/big_ind2:_=>//.
rewrite Rmult_0_r; apply Rle_refl.
intros x1 x2 y1 y2 Hx Hy.
apply Rle_trans with (x1 + y1);  
auto with real.
apply Rle_trans with (u*(x2 + y2)); 
auto with real.
lra.
intros i _.
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite Rabs_mult; auto with real.
auto with real.
eapply Rle_trans. 
apply Rplus_le_compat_r.
instantiate (1 := 
  ((INR d.+1 - 1) * (u/(1+u)) *
     (\sum_(i < d.+1) ((1 + u)*Rabs (a i ord_max * b i ord_max) 
     + /2*eta)))).
apply Rmult_le_compat_l.
apply Rmult_le_pos.
clear a b; induction d.
simpl; apply Req_le; ring.
apply Rle_trans with (1 := IHd).
apply Rplus_le_compat_r.
apply le_INR; auto with real.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
eapply Rle_trans.
apply (Fourier_util.Rle_mult_inv_pos 1).
lra.
instantiate (1:= 1+u).
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
lra.
apply Req_le; field.
apply Rgt_not_eq.
apply Rlt_gt.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
lra.
elim/big_ind2:_=>//.
apply Rle_refl.
intros x1 x2 y1 y2 H1 H2.
auto with real.
intros i _.
apply Rle_trans with 
 (Rabs (a i ord_max * b i ord_max) + 
  (u * Rabs (a i ord_max * b i ord_max) 
  + / 2 * eta)).
apply Rle_trans with 
  (Rabs (((\col_i0 r_flt (a i0 ord_max * b i0 ord_max)) i ord_max) 
  - a i ord_max*b i ord_max)
 + Rabs (a i ord_max*b i ord_max)).
eapply Rle_trans. 
2 : apply Rabs_triang.
apply Req_le; f_equal; lra.
rewrite Rplus_comm.
apply Rplus_le_compat_l.
rewrite !mxE.
apply relative_error_N_FLT_strong.
rewrite <- Rplus_assoc.
apply Rplus_le_compat; auto with real.
rewrite <- (Rmult_1_l (Rabs (a i ord_max * b i ord_max))) at 1.
rewrite <- Rmult_plus_distr_r; auto with real.
rewrite big_Rplus_half_const.
rewrite Rmult_plus_distr_l.
rewrite Rplus_assoc.
rewrite (Rplus_comm 
  ((INR d.+1-1)*(u/(1+u))*(INR d.+1*(/2*eta))%Ri)).
rewrite Rplus_assoc.
rewrite <- Rplus_assoc.
apply Rplus_le_compat.
apply Rle_trans with
 ((INR d.+1 - 1) * u * 
  (\sum_(i < d.+1) Rabs (a i ord_max * b i ord_max)) 
  + u * (\sum_i Rabs (a i ord_max) * Rabs (b i ord_max))).
apply Rplus_le_compat_r.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
clear a b; induction d.
simpl; apply Req_le; ring.
apply Rle_trans with (1:=IHd).
apply Rplus_le_compat_r.
apply le_INR; auto with real.
elim/big_ind2:_=> //.
repeat rewrite Rmult_0_r.
apply Rle_refl.
intros x1 x2 y1 y2 H1 H2.
repeat rewrite Rmult_plus_distr_l; lra.
intros i _.
apply Req_le.
rewrite <-Rmult_assoc.
f_equal.
rewrite Rmult_assoc.
rewrite Rmult_comm.
rewrite (Rmult_comm (/ (1 + u))).
apply Rinv_r_simpl_r. 
apply Rgt_not_eq.
apply Rlt_gt.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
lra.
replace (INR d.+1) with ((INR d.+1 - 1) + 1) at 2.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_r.
apply Rplus_le_compat.
apply Req_le.
repeat f_equal.
apply functional_extensionality; intros x.
f_equal.
now rewrite Rabs_mult.
rewrite Rmult_1_l.
apply Rle_refl.
clear a b; induction d; simpl; ring.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_r.
rewrite Rplus_comm.
apply Rplus_le_compat_r.
apply Rle_trans with 
 (INR d.+1*u*(INR d.+1*(/2*eta))).
apply Rmult_le_compat. 
apply Rmult_le_pos. 
clear a b; induction d.
simpl; apply Req_le; ring.
apply Rle_trans with (1 := IHd).
apply Rplus_le_compat_r.
apply le_INR; auto with real.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply Rle_lt_trans with u; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_pos.
apply pos_INR.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rmult_le_compat.
clear a b; induction d.
simpl; apply Req_le; ring.
apply Rle_trans with (1 := IHd).
apply Rplus_le_compat_r.
apply le_INR; auto with real.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply Rle_lt_trans with u; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rmult_le_reg_r with (1+u).
apply Rle_lt_trans with u.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
lra.
auto with real.
replace (u / (1 + u) * (1 + u)) with u.
rewrite Rmult_plus_distr_l.
ring_simplify.
apply Rle_trans with (0 + u).
apply Req_le; ring.
apply Rplus_le_compat_r.
apply Ratan.pow2_ge_0.
field.
apply Rgt_not_eq. 
apply Rlt_gt.
apply Rle_lt_trans with u.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
auto with real.
apply Req_le. 
ring.
Qed.

(** Bound on matrix-vector product *)

Lemma mx_vec_prod_error : forall {d} (A : 'M_d.+1) (v : 'cV_d.+1), 
           ||| A (x)_m v - A *m v ||| <=  INR d.+1 * u * ||| A ||| * ||| v ||| 
         + ((INR d.+1) * (INR d.+1) * u + INR d.+1)* /2 * eta.
Proof.
intros d A v.
unfold mulmx_rnd, matrix_norm at 1.
apply Rle_trans with 
   (\big[Rmax/0]_(i < d.+1) ((INR d.+1 * u) * 
        (\big[Rplus / 0%R]_(k < d.+1) 
            (Rabs (A i k) * Rabs (v k ord_max))) 
 + ((INR d.+1)*(INR d.+1) * u + INR d.+1) * /2 * eta)).
elim/big_ind2: _ => //; try lra; try auto with real.
intros x1 x2 y1 y2 Hx Hy.
apply Rle_trans with (Rmax x2 y1).
now apply Rle_max_compat_l.
now apply Rle_max_compat_r.
intros i _.
apply Rle_trans with 
   ((INR d.+1 * u) * \big[Rplus/0]_(i0 < d.+1) 
        (Rabs ((row i A)^T i0 ord_max) * Rabs (v i0 ord_max)) 
   + ((INR d.+1)  * (INR d.+1)* u + INR d.+1) * /2 * eta).
apply Rle_trans with 
  (Rabs (dot_product (row i A)^T v r_flt 
    - dot_product (row i A)^T v (fun x => x))).
unfold dot_product.
rewrite big_ord_recr big_ord0; simpl.
rewrite Rplus_0_l.
rewrite mat_apply_add_distr.
rewrite mat_apply_opp_distr.
apply Req_le.
f_equal.
unfold Rminus.
f_equal.
rewrite !mxE.
f_equal; apply functional_extensionality.
intros x; f_equal.
rewrite !mxE.
reflexivity.
unfold Rminus.
f_equal. 
unfold mulmx.
rewrite !mxE.
elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
now rewrite Hx Hy.
intros j _.
now rewrite !mxE.
f_equal; now apply dot_product_error.
apply Rplus_le_compat_r, Rmult_le_compat_l.
apply Rmult_le_pos.
replace 0 with (INR 0) by reflexivity.
apply le_INR; lia.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Req_le.
apply eq_bigr.
intros k _; repeat f_equal; now rewrite !mxE.
apply Rle_trans with 
  (\big[Rmax/0]_(i < d.+1) ((INR d.+1 * u) *
    \big[Rplus/0]_(k < d.+1) 
         (Rabs (A i k) * Rabs (v k ord_max))) 
  + ((INR d.+1)*(INR d.+1) * u + INR d.+1) * /2 * eta).
apply Req_le.
rewrite big_Rmax_half_const; try easy.
auto with real.
intros x. 
repeat apply Rmult_le_pos; try lra; try lia.
replace 0 with (INR 0) by reflexivity.
apply le_INR; lia.
apply bpow_ge_0.
elim/big_rec:_=>//.
apply Rle_refl.
intros i y _ Hy.
apply Rle_trans with (0 + 0). 
auto with real. 
apply Rplus_le_compat; try easy.
apply Rmult_le_pos; now apply Rabs_pos.
repeat apply Rmult_le_pos;
replace 0 with (INR 0) by reflexivity; 
try (apply le_INR; lia).
simpl (INR 0).
apply Rle_trans with (0 + 0). 
auto with real.
apply Rplus_le_compat.
apply Rmult_le_pos.
generalize (Ratan.pow2_ge_0 (INR d.+1)); intros H.
unfold Rpow_def.pow in H.
rewrite Rmult_1_r in H.
apply H. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply pos_INR.
simpl; lra.
apply bpow_ge_0.
apply Rplus_le_compat_r.
apply Rle_trans with 
   ((INR d.+1 * u) * 
   \big[Rmax/0]_(i < d.+1)
     (\big[Rplus/0]_(k < d.+1) 
       (Rabs (A i k) * Rabs (v k ord_max)))).
apply Req_le.
rewrite big_endo ?mulm0 //.
intros x y; rewrite RmaxRmult//.
apply Rmult_le_pos.
replace 0 with (INR 0) by reflexivity.
apply le_INR; lia.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
ring.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
replace 0 with (INR 0) by reflexivity.
apply le_INR; lia.
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rle_trans with 
     (\big[Rmax/0]_(i < d.+1) 
          \big[Rplus/0]_(k < d.+1) 
            (Rabs (A i k) * (\big[Rmax/0]_(z < d.+1) Rabs (v z ord_max)))).
elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
apply Rle_trans with (Rmax x2 y1).
now apply Rle_max_compat_l.
now apply Rle_max_compat_r.
intros i _.
elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
lra.
intros k _. 
apply Rmult_le_compat_l.
apply Rabs_pos.
apply (@leq_bigmax _ (fun z => Rabs (v z ord_max))).
intros x; apply Rabs_pos.
apply Rle_trans with 
   (\big[Rmax/0]_(i < d.+1) 
         ((\big[Rmax/0]_(z < d.+1) Rabs (v z ord_max)) 
       * \big[Rplus/0]_(k < d.+1) (Rabs (A i k)))).
apply Req_le.
elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
now rewrite Hx Hy.
intros i _.
rewrite Rmult_comm.
elim/big_ind2: _ => //; try lra.
intros x1 x2 y1 y2 Hx Hy.
rewrite Hx Hy.
ring.
unfold  matrix_norm.
apply Req_le.
elim/big_ind2: _ => //; try lra; try auto with real.
intros x1 x2 y1 y2 Hx Hy.
rewrite Rmult_comm.
rewrite Rmult_comm in Hx.
rewrite Rmult_comm in Hy.
rewrite Hx Hy.
rewrite RmaxRmult.
ring.
elim/big_ind: _ => //; try lra; try auto with real.
intros x y Hx0 Hy0.
apply Rle_trans with x; try easy.
apply Rmax_l.
intros i _.
rewrite big_ord_recr big_ord0.
simpl.
rewrite Rplus_0_l.
apply Rabs_pos.
intros i _.
symmetry. 
rewrite Rmult_comm. 
under eq_bigr => i0 do rewrite big_ord_recr big_ord0.
f_equal. 
f_equal; apply functional_extensionality.
intros; try auto with real.
Qed. 

End MatrixRndError.

Section FP_prel.

Notation rnd_vec_matrix_product := mulmx_rnd.

Notation "X (x)_m Y" := (mulmx_rnd X Y r_flt) (at level 50).

Notation "a *_sm A" := (map_mx (fun x => (a*x)) A) (at level 40).
Notation "a (x)_sm A" := (map_mx (fun x => r_flt (a*x)) A) (at level 50).

Section Const_prod_mat_aux. 

(** Bounds on the matrix coefficients *)
Variable d : nat. 
Variables a a' B : R.
Variable A : 'M[R]_d.+1.


Lemma mat_coeffs_error_aux : Rabs (a' - a) <= B -> 
     ||| a' (x)_sm A -  a *_sm A ||| 
   <= (B +  u* (B + Rabs a)) * ||| A ||| + INR d.+1 * /2 * eta.
Proof.
intros Ha.
apply Rle_trans with 
   ((u*(B+Rabs a)*|||A|||+INR d.+1*/2*eta) + B*|||A|||). 
apply Rle_trans with (||| a' (x)_sm A - a' *_sm A ||| 
                      + ||| a' *_sm A - a *_sm A |||).
eapply Rle_trans. 
2 : apply matrix_norm_triang.
unfold matrix_norm.
apply Req_le; f_equal; apply functional_extensionality.
intros x; f_equal.
f_equal; apply functional_extensionality.
intros y; f_equal.
rewrite !mxE.
f_equal.
transitivity (r_flt (a'*A x y)-(a*A x y)); auto with real.
transitivity (r_flt (a' * A x y) - (a' * A x y) 
  + a'* A x y - a * A x y); auto with real.
lra.
unfold Rminus; auto with real.
apply Rplus_le_compat.
unfold matrix_norm at 1.
apply Rle_trans with 
  (\big[Rmax/0]_(i < d.+1) 
    \big[Rplus/0]_(j < d.+1) 
      (u * Rabs a' * Rabs (A i j) + /2*eta)).
apply big_Rmax_le.
intros i. 
elim/big_ind2:_=>//; try auto with real.
intros j _.
rewrite !mxE.
rewrite Rmult_assoc.
rewrite <- Rabs_mult.
apply relative_error_N_FLT_strong.
eapply Rle_trans.
apply big_Rmax_le.
intros i.
apply Req_le; apply big_Rplus_half_const.
rewrite big_Rmax_half_const.
apply Rplus_le_compat; try auto with real.
elim/big_ind:_=>//.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rle_trans with (Rabs (a' - a) + Rabs a).
eapply Rle_trans.
2 : apply Rplus_le_compat; apply Rabs_pos.
auto with real.
apply Rplus_le_compat; try easy.
apply Rle_refl.
apply matrix_norm_pos.
intros x y Hx Hy.
unfold Rmax; now destruct (Rle_dec x y).
intros i _.
apply Rle_trans with 
  (\sum_(i0 < d.+1) (u*(B+Rabs a)*Rabs (A i i0))).
elim/big_ind2:_=>//; try auto with real.
intros j _.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rle_trans with (Rabs (a' - a) + Rabs a). 
eapply Rle_trans. 
2 : apply Rabs_triang. 
apply Req_le; f_equal; ring.
auto with real.
apply Rle_trans with (u * (B + Rabs a) 
      *(\sum_(i0 < d.+1) Rabs (A i i0))).
apply Req_le. 
rewrite big_Rplus_scal.
auto with real. 
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rle_trans with (Rabs (a' - a) + Rabs a). 
eapply Rle_trans. 
2 : apply Rplus_le_compat; apply Rabs_pos.
auto with real.
apply Rplus_le_compat; try easy; try apply Rle_refl.
apply Rmult_le_compat_l.
repeat apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply Rle_trans with (Rabs (a' - a) + Rabs a). 
eapply Rle_trans. 
2 : apply Rplus_le_compat; apply Rabs_pos.
auto with real.
apply Rplus_le_compat; try easy; try apply Rle_refl.
unfold matrix_norm.
eapply Rle_trans. 
2 : {apply leq_bigmax.
intros j. 
elim/big_ind:_=>//; try auto with real.
intros x y Hx Hy; lra. 
intros; apply Rabs_pos. }
apply Req_le; auto with real.
intros x.  
elim/big_ind:_=>//; try auto with real.
intros x0 y0 Hx Hy; try lra.
eapply Rle_trans. 
2 : { apply Rplus_le_compat.
apply Hx. 
apply Hy. }
auto with real.
intros i _. 
repeat apply Rmult_le_pos; try lra; try apply bpow_ge_0; 
try apply Rabs_pos.
repeat apply Rmult_le_pos; try lra; try apply bpow_ge_0; 
try apply Rabs_pos.
apply pos_INR.
eapply Rle_trans. 
2 : { apply Rmult_le_compat_r. 
apply matrix_norm_pos.
apply Ha. }
unfold matrix_norm.
rewrite <- big_Rmax_scal.
apply big_Rmax_le.
intros i; rewrite <- big_Rplus_scal.
elim/big_ind2:_=>//; try auto with real.
intros j _.
rewrite <- Rabs_mult.
rewrite !mxE.
apply Req_le. 
f_equal; rewrite Rmult_plus_distr_r.
auto with real.
apply Rabs_pos.
apply Rabs_pos.
apply Req_le; ring.
Qed.

End Const_prod_mat_aux. 

Section Const_prod_mat.

Variable d : nat. 
Variables a a' B : R.
Variable A A' : 'M[R]_d.+1.

Variable C D : R. 
Hypothesis HC : 0 <= C.
Hypothesis HD : 0 <= D. 

Lemma mat_coeffs_error : Rabs (a' - a) <= B 
     -> ||| A' - A ||| <= C * u  * ||| A ||| + D * eta
      -> ||| a' (x)_sm A' -  a *_sm A ||| 
       <= ((1 + C*u)*(u*(B + Rabs a)+B) + C*u*Rabs a)*||| A |||
          + ((1 + u) * (B + Rabs a) * D + INR d.+1 * /2) * eta. 
Proof. 
intros Ha HA.
apply Rle_trans with 
   (||| a' (x)_sm A' -  a *_sm A' ||| +
    ||| a *_sm A' -  a *_sm A |||).
eapply Rle_trans.
2 : apply matrix_norm_triang.
unfold matrix_norm.
apply Req_le; f_equal; apply functional_extensionality.
intros i; f_equal.
f_equal; apply functional_extensionality.
intros j; f_equal.
f_equal; rewrite !mxE.
transitivity (r_flt (a' * A' i j) - (a * A i j)); 
auto with real. 
transitivity (r_flt (a' * A' i j) - (a * A' i j) +
                 (a * A' i j) - (a * A i j)); 
unfold Rminus; auto with real.
ring.      
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
intros i. 
rewrite <- big_Rplus_scal.
elim/big_ind2:_=> //; try apply Rle_refl.
intros x1 x2 y1 y2 Hx Hy; auto with real.
intros j _.
rewrite !mxE.
rewrite <- Rabs_mult.
apply Req_le.
f_equal.
transitivity (a * A' i j - a * A i j); 
auto with real.
transitivity (a * (A' i j - A i j)); 
auto with real. 
lra.
apply Rabs_pos.
apply Rabs_pos.
assert (HA' : ||| A' ||| <= (1+C*u)*||| A ||| + D*eta).
apply Rle_trans with (|||A' - A||| + |||A|||).
eapply Rle_trans. 
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP. 
intros i j;
rewrite !mxE.
transitivity (A' i j - A i j + A i j).
lra.
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

Lemma rnd_matrix_error :
    ||| rnd_mat A r_flt - A ||| <= u * ||| A ||| + INR d.+1 * / 2 * eta.
Proof with auto with typeclass_instances.
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
  auto with real.
  intros j _.
  rewrite !mxE.
  apply relative_error_N_FLT_strong...
  apply Rmult_le_pos.
  apply bpow_ge_0.
  lra.
Qed.

End Const_prod_mat.

Section bounds_plus_flt.

(** Generic results to bound local errors *)

Variable d : nat. 
Variable y : 'cV[R]_d.+1.
Variables A1 A2 : 'M[R]_d.+1.
Variables X1 X2 : 'cV[R]_d.+1.
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
intros H1 H2.
eapply Rle_trans.
instantiate (1 := (||| X1 (+)_m X2 - (X1 + X2) ||| +
                   ||| X1 + X2 - (A1 + A2) *m y |||)).
eapply Rle_trans. 
2 : apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP=> i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
repeat rewrite mat_apply_add_distr.
transitivity ((X1 (+)_m X2) i j - (X1 i j + X2 i j) +
 (X1 i j + X2 i j - ((A1 + A2) *m y) i j)).
auto with arith.
transitivity ((X1 (+)_m X2) i j - ((A1+A2) *m y) i j).
auto with arith.
lra.
auto with real.
eapply Rle_trans. 
apply Rplus_le_compat.
instantiate (1 := 
   (u *(||| A1 ||| + ||| A2 ||| + C1 + C2)*||| y |||
    + u*(D1 + D2)*eta)).
eapply Rle_trans.
instantiate (1 := (u *||| X1 + X2 |||)).
unfold matrix_norm.
elim/big_ind2:_=>//.
auto with real.
intros x1 x2 y1 y2 Hx Hy.
unfold Rmax; destruct (Rle_dec x2 y2); 
destruct (Rle_dec x1 y1); try easy.
apply Rle_trans with (1:=Hy).
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
apply Rle_trans with (1:=Hx).
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
lra.
intros i _.
rewrite big_ord_recr big_ord0; simpl; rewrite Rplus_0_l.
rewrite !mxE.
eapply Rle_trans.
apply error_le_plus_opt...
rewrite big_ord_recr big_ord0.
fold u.  
simpl; rewrite Rplus_0_l. 
simpl.
rewrite !mxE. 
apply Rmult_le_compat_r.
apply Rabs_pos.
fold u; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
replace 1 with (/1) at 2 by field.
apply Rinv_le; try auto with real.
apply Rle_trans with (1 + 0); try lra.
apply Rplus_le_compat_l.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
eapply Rle_trans. 
instantiate (1:= (u*||| X1 ||| + u*||| X2 |||)).
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply matrix_norm_triang.
eapply Rle_trans.
apply Rplus_le_compat.
instantiate (1 :=
  (u*(|||A1||| + C1)*||| y ||| + u*D1*eta)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rle_trans with 
   (||| X1 - A1 *m y ||| + ||| A1 *m y |||). 
eapply Rle_trans.
2 : apply matrix_norm_triang. 
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
repeat rewrite mat_apply_add_distr.
transitivity (X1 i j - (A1 *m y) i j + (A1 *m y) i j).
lra.
auto with real.
eapply Rle_trans.
apply Rplus_le_compat.
apply H1.
instantiate (1:= (||| A1 ||| * ||| y |||)).
apply norm_submult.
apply Req_le; ring.
instantiate (1:= 
  (u*(|||A2||| + C2)* ||| y ||| + u*D2*eta)).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
apply Rle_trans with 
   (||| X2 - A2 *m y ||| + ||| A2 *m y |||). 
eapply Rle_trans.
2 : apply matrix_norm_triang. 
apply Req_le; f_equal.
apply/matrixP => i j.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
repeat rewrite mat_apply_add_distr.
transitivity (X2 i j - (A2 *m y) i j + (A2 *m y) i j).
lra.
auto with real.
eapply Rle_trans.
apply Rplus_le_compat.
apply H2.
instantiate (1:= (||| A2 ||| * ||| y |||)).
apply norm_submult.
apply Req_le; ring.
apply Req_le; ring.
instantiate (1:= (C1+C2)*||| y ||| + (D1+D2)*eta).
apply Rle_trans with (||| X1 - A1 *m y ||| + ||| X2 - A2 *m y |||).
eapply Rle_trans. 
2: apply matrix_norm_triang.
apply Req_le; f_equal.
apply/matrixP=> i j.
rewrite mulmxDl.
repeat rewrite mat_apply_add_distr.
repeat rewrite mat_apply_opp_distr.
repeat rewrite mat_apply_add_distr.
transitivity ((X1 i j + X2 i j 
 - ((A1 *m y) i j + (A2 *m y) i j))).
auto with real.
transitivity ((X1 i j - (A1 *m y) i j 
    + (X2 i j - (A2 *m y) i j)));
auto with real.
lra.
apply Rle_trans with 
   ((C1* ||| y ||| + D1*eta) + (C2*||| y ||| + D2*eta)).
now apply Rplus_le_compat.
apply Req_le; ring.
apply Req_le; ring.
Qed. 

End bounds_plus_flt.

Section bounds_mult_flt. 

Variable d : nat. 
Variable y : 'cV[R]_d.+1.
Variables A1 A2 A3 A2f : 'M[R]_d.+1.
Variables X1 X2 X3 : 'cV[R]_d.+1.
Variables C1 C2 C3 D1 D2 D3 : R. 

Hypothesis C1pos : 0 <= C1.
Hypothesis C2pos : 0 <= C2.
Hypothesis C3pos : 0 <= C3.
Hypothesis D1pos : 0 <= D1.
Hypothesis D2pos : 0 <= D2.
Hypothesis D3pos : 0 <= D3.

Hypothesis Hx1 : format_mat X1.
Hypothesis Hx2 : format_mat X2.
Hypothesis Hx3 : format_mat X3.

Lemma build_vec_mult_error : 
     let K := C2*|||A3||| + C3*|||A2||| + C2*C3 + (C3 + |||A3|||)*D2*eta
     in 
     let D:= (1 + u) * (D1 + (1 + INR d.+1*u)*(C2 + D2*eta + |||A2|||)*D3
           + (INR d.+1 * INR d.+1 *u + INR d.+1) */2)
      in 
      ||| X1 - A1 *m y ||| <= C1 * ||| y ||| + D1 * eta ->
      ||| A2f - A2 ||| <= C2 + D2 * eta -> 
      ||| X3 - A3 *m y ||| <= C3 * ||| y ||| + D3 * eta ->
      ||| (X1 (+)_m (A2f (x)_m X3)) - (A1 + A2 *m A3) *m y ||| 
        <= ((1+u)*(C1 + (1 + INR d.+1*u)*K) + u * ||| A1 ||| + ((INR d.+1 + 1)*u 
                + (INR d.+1 * u *u))* |||A2||| * |||A3|||) * ||| y ||| + D * eta. 
Proof with auto with typeclass_instances.
intros K D H1 H2 H3.
pose (CC := ((1 + INR d.+1*u)*(C2*|||A3||| + C3*|||A2||| + C2*C3 
      + (C3 + |||A3|||)*D2*eta) + (INR d.+1*u*|||A2|||*|||A3|||))). 
pose (DD := (1 + INR d.+1*u)*(C2 + D2*eta + |||A2|||)*D3
           + (INR d.+1 * INR d.+1 *u + INR d.+1) */2).
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
repeat rewrite mat_apply_add_distr.
transitivity ((A2f (x)_mX3) i j 
   - (A2 *m A3 *m y) i j); auto with real.
transitivity ((A2f (x)_mX3) i j - (A2f *m A3 *m y) i j +
 ((A2f *m A3 *m y) i j - (A2 *m A3 *m y) i j)); auto with real.
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
repeat rewrite mat_apply_add_distr.
transitivity ((A2f (x)_mX3) i j 
  - (A2f *m A3 *m y) i j); auto with real.
transitivity ((A2f (x)_mX3) i j - (A2f *m X3) i j +
 ((A2f *m X3) i j - (A2f *m A3 *m y) i j)); auto with real.
lra.
eapply Rle_trans.
apply Rplus_le_compat.
eapply Rle_trans. 
apply Rplus_le_compat.
apply mx_vec_prod_error.
rewrite <- mulmxA.
rewrite <- (mulmxBr A2f).
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
repeat rewrite mat_apply_add_distr.
transitivity (X3 i j - (A3 *m y) i j + (A3 *m y) i j); 
auto with real. 
lra.
rewrite Rmult_plus_distr_r.
apply Rle_trans with 
  ((C3*||| y ||| + D3*eta) + |||A3|||*||| y |||).
apply Rplus_le_compat.
apply H3.
apply norm_submult.
apply Req_le; ring.
apply Req_le; reflexivity.
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
repeat rewrite mat_apply_add_distr.
transitivity (A2f i j - A2 i j + A2 i j);
auto with real.
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
rewrite <- mulmxA.
rewrite <- mulmxA.
rewrite <- mulmxBl.
apply norm_submult.
eapply Rle_trans.
repeat apply Rplus_le_compat.
2 : apply Req_le; reflexivity.
2 : apply Req_le; reflexivity.
2 : apply Req_le; reflexivity.
repeat apply Rmult_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
apply matrix_norm_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat.
repeat apply Rmult_le_pos; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply matrix_norm_pos.
apply matrix_norm_pos. 
apply Rmult_le_pos; try easy.
apply bpow_ge_0.
repeat apply Rmult_le_pos; try lra. 
apply pos_INR. 
apply bpow_ge_0.
apply matrix_norm_pos.
apply pos_INR. 
repeat apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
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
repeat rewrite mat_apply_add_distr.
transitivity (A2f i j - A2 i j + A2 i j);
auto with real.
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
elim/big_ind:_=> //.
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
apply Req_le; reflexivity.
apply Req_le; reflexivity. 
apply Req_le; reflexivity.
apply Rmult_le_compat_l. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
repeat apply Rplus_le_compat.
apply Req_le; reflexivity.
apply norm_submult.
apply Req_le; reflexivity.
apply Req_le; reflexivity.
apply Req_le; reflexivity. 
unfold K, D, CC, DD; apply Req_le.
f_equal.
apply Rmult_eq_compat_r.
fold K.
pose (B := (1 + INR d.+1 * u)). 
fold B.
pose (G := INR d.+1 * u). 
fold G.
pose (N := ||| A2 ||| * ||| A3 |||).
fold N. 
transitivity 
  (C1 + (B * K + G * N) +
u * (||| A1 ||| + N + C1 + (B * K + G * N))). 
unfold N; ring.
transitivity ((1 + u) * 
  (C1 + B * K) + 
   u * ||| A1 ||| + ((G + u) + G * u) * N); 
try (unfold N; ring). unfold G, N.
ring.
ring. 
Qed. 

Lemma build_vec_mult_error_wk : 
  let K := C2*|||A3||| + C3*|||A2||| + C2*C3 + (C3 + |||A3|||)*D2*eta
    in 
  ||| X1 - A1 *m y ||| <= C1 * ||| y ||| + D1 * eta ->
  ||| A2f - A2 ||| <= C2 + D2 * eta -> 
  ||| X3 - A3 *m y ||| <= C3 * ||| y ||| + D3 * eta ->
  INR d.+1 * u <= 1/100 -> (emin <= 0)%Z -> 
  ||| (X1 (+)_m (A2f (x)_m X3)) - (A1 + A2 *m A3) *m y ||| 
    <= ((1 +3/100)*(C1 + K) + u*||| A1 ||| 
        + ((INR d.+1 + 1 + 1/100)*u)* |||A2|||*|||A3|||) * ||| y ||| 
  + ((1+3/100)* (D1 + (C2 + D2 + |||A2|||)*D3) + (6/10*INR d.+1))* eta.
Proof.
intros K H1 H2 H3 Hdu He.
assert (H01 : u <= 1/100).
apply Rle_trans with (INR d.+1 * u).
rewrite <- (Rmult_1_l u) at 1.
apply Rmult_le_compat_r. 
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
clear.
induction d.
apply Rle_refl.
apply Rle_trans with (1:=IHn).
apply le_INR.
lia.
easy.
eapply Rle_trans. 
apply build_vec_mult_error; try easy.
apply Rplus_le_compat.
fold K.
(* *)
apply Rmult_le_compat_r.
apply matrix_norm_pos.
apply Rplus_le_compat. 
apply Rplus_le_compat_r.
apply Rle_trans with 
  ((1 + 1/100) * (C1 + (1 + 1/100) * K)).
apply Rmult_le_compat.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
repeat apply Rmult_le_pos; try lra.
apply pos_INR.
apply bpow_ge_0.
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
repeat apply Rmult_le_pos.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply matrix_norm_pos.
easy.
apply bpow_ge_0.
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
apply Rmult_le_pos. 
apply pos_INR.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy; try lra.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy; try lra.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
apply matrix_norm_pos. 
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try lra.
apply Rmult_le_pos; try lra. 
apply pos_INR.
apply Rmult_le_pos; try lra.
apply bpow_ge_0.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
rewrite <- (Rplus_0_r 0).
apply Rplus_le_compat; try easy.
apply Rmult_le_pos; try easy. 
apply bpow_ge_0.
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
  ((1 + 1 / 100)/2 * ((INR d.+1 * INR d.+1 * u + INR d.+1))).
apply Req_le; lra.
apply Rle_trans with 
  ((1 + 1 / 100) / 2 * (1+1/100)*INR d.+1).
rewrite Rmult_assoc.
rewrite Rmult_assoc.
apply Rmult_le_compat_l; try lra.
rewrite Rmult_plus_distr_r.
rewrite (Rplus_comm (1*INR d.+1)).
apply Rplus_le_compat.
rewrite Rmult_comm.
apply Rmult_le_compat_r; try easy.
apply pos_INR.
auto with real.
apply Rmult_le_compat_r.
apply pos_INR.
lra.
Qed.

End bounds_mult_flt. 
End FP_prel.

End FP_loc_err.
