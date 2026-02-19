(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*    David Knothe, FZI Research Center for Information Technology     *)
(*        Xavier Leroy, INRIA Paris-Rocquencourt                       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Tools for big-step semantics and their behaviors *)

Require Import Classical.
Require Import Coqlib.
Require Import Events.
Require Import Tracex.
Require Import Globalenvs.
Require Import Integers.
Require Import Equality.
Require Import Behaviors.

(** The general form of a big-step semantics. *)

Record semantics : Type := Bigstep_semantics {
  genvtype: Type;
  globalenv: genvtype;
  symbolenv: Senv.t;
  terminates: trace -> int -> Prop;
  forever: tracex -> Prop;
  partial: trace -> Prop
}.

Definition Semantics {funtype vartype: Type}
                     (terminates: trace -> int -> Prop)
                     (forever: tracex -> Prop)
                     (partial: trace -> Prop)
                     (globalenv: Genv.t funtype vartype) :=
  {| genvtype := Genv.t funtype vartype;
     globalenv := globalenv;
     symbolenv := Genv.to_senv globalenv;
     terminates := terminates;
     forever := forever;
     partial := partial |}.