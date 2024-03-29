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

From mathcomp
  Require Import all_ssreflect ssralg matrix.

From Flocq.Core 
Require Import Core. 

Require Import Rstruct Compl Norms.

Set Implicit Arguments.

Section Def_schemes. 


Variables (beta : radix) 
          (emin prec : Z) 
          (choice : Z -> bool).

Definition r_flt := (round beta 
    (FLT_exp emin prec) (ZnearestE)).

Variable d : nat. 

(** Type Sc of schemes : fun W => fun y(n) => y(n+1) *)
Definition Sc : Type := (R -> R) -> 'cV[R]_d -> 'cV[R]_d.

(* Roundings and schemes : 
   W_Id : exact R(h,l)
   W_FLT : FLT format on scheme R~(h~,l~,y~) *)

Definition W_Id := (fun meth : Sc => meth ssrfun.id).
Definition W_FLT := (fun meth : Sc => meth r_flt).

(** Mathematical equivalence between schemes *)
Definition eq_math_Sc (meth1 meth2 : Sc) : Prop := 
               forall x, W_Id meth1 x = W_Id meth2 x.

(** Stability property *)
Definition stable (meth : Sc) : Prop := 
               forall x, ||| (W_Id meth x) ||| <= ||| x |||.


Definition meth_iter (meth : Sc) n (y0 : 'cV_d) (W : R -> R)  
                     := Nat.iter n (meth W) (\matrix_(i,j) (W (y0 i j))).

(** global roundoff error of the scheme after N iteration 
   == En *)
Definition error_glob (meth : Sc) (n : nat) (y0 : 'cV_d) (W : R -> R) 
  := ||| (meth_iter meth n y0 W - meth_iter meth n y0 id) |||.

(** local roundoff error of the scheme at iteration n 
   == epsilon n+1 *)
Definition error_loc (meth : Sc) (n : nat) (y0 : 'cV_d) (W : R -> R) 
  := ||| (meth W (meth_iter meth n y0 W)  - meth id (meth_iter meth n y0 W)) |||.

Notation "S1 ≡ S2" := (eq_math_Sc S1 S2) (at level 35).

(** Characterization of RK + linear systems, i.e. R(h,A) *)
Definition is_RK_lin (meth : Sc) (Rmeth : 'M_d) := 
      forall y, W_Id meth y = (Rmeth *m y)%R. 

Notation "x ^ y" := (Rpow_def.pow x y).

(** Simplification of exact n-th iteration *)
Lemma is_RK_Rmeth meth Rm (is_RKm : is_RK_lin meth Rm) y0 : 
   forall N, ||| (meth_iter meth N y0 (fun x : R => x)) |||
           <= ||| Rm ||| ^ N * ||| y0 |||.
Proof. 
induction 0.
+ simpl. 
  rewrite Rmult_1_l.
  apply Req_le.
  f_equal.
  apply matrixP=> i j.
  rewrite !mxE.
  reflexivity. 
+ simpl; unfold W_Id in *. 
  unfold W_Id in *.
  simpl; unfold is_RK_lin in is_RKm.
  unfold W_Id in *.
  rewrite is_RKm.
  apply Rle_trans with (||| Rm |||*||| (meth_iter meth N y0 id) |||).
  apply norm_submult.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  apply matrix_norm_pos.
  apply IHN.
Qed.

End Def_schemes.
