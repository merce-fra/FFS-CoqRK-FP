
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



Require Import Rdefinitions Raxioms RIneq Rbasic_fun Epsilon FunctionalExtensionality ProofIrrelevance Lra.


From mathcomp
Require Import all_ssreflect finalg ssrnum ssralg finalg matrix.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.



Record Rpos := mk_Rpos {
                   toR : R ; 
                   Hpos : 0 <= toR
}.
            

Definition Rmax_pos_aux (x y : Rpos) := Rmax (toR x) (toR y).

Lemma Rmax_pos_aux_pos : forall x y, 0 <= Rmax_pos_aux x y.
Proof. 
intros x y.
unfold Rmax_pos_aux.
destruct x; destruct y.
simpl; unfold Rmax; now destruct (Rle_dec toR0 toR1).
Qed.

Definition Rmax_pos (x y : Rpos) := mk_Rpos (Rmax_pos_aux_pos x y).

Lemma Rpos_ext : forall (x y : Rpos), toR x = toR y -> x = y.
Proof. 
intros x y Ht.
destruct x as (x,Hx).
destruct y as (y,Hy).
simpl in Ht.
generalize Hx Hy.
rewrite Ht.
intros Hx0 Hy0.
f_equal.
apply proof_irrelevance.
Qed.  

Fact Rmax_posA : associative (Rmax_pos).
Proof. 
intros x y z.
destruct x as (x,Hx).
destruct y as (y,Hy).
destruct z as (z,Hz).
unfold Rmax_pos; simpl.
apply Rpos_ext.
simpl.
unfold Rmax_pos_aux.
simpl.
apply Rmax_assoc.
Qed. 

Definition Rpos_0 : Rpos := mk_Rpos (Rle_refl 0).

Fact Rmax_pos_0_l : forall x : Rpos, Rmax_pos (Rpos_0) x = x.
Proof. 
intros x; unfold Rmax_pos.
destruct x as (x,Hx).
apply Rpos_ext; simpl.
unfold Rmax_pos_aux.
simpl.
now rewrite Rmax_right.
Qed.

Fact Rmax_pos_0_r : forall x : Rpos, Rmax_pos x (Rpos_0) = x. 
Proof. 
intros x; unfold Rmax_pos.
destruct x as (x,Hx).
apply Rpos_ext; simpl.
unfold Rmax_pos_aux.
simpl.
now rewrite Rmax_left.
Qed.

Import Monoid.


Canonical Rmax_monoid := Law Rmax_posA Rmax_pos_0_l Rmax_pos_0_r.
