(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** All imports and definitions used by .v Clight files generated by clightgen *)

Require Export String.
Require Export List.
Require Export ZArith.
Require Export Integers.
Require Export Floats.
Require Export AST.
Require Export Ctypes.
Require Export Cop.
Require Export Clight.
Require Import Maps.
Require Import Errors.

Definition tvoid := Tvoid.
Definition tschar := Tint I8 Signed noattr.
Definition tuchar := Tint I8 Unsigned noattr.
Definition tshort := Tint I16 Signed noattr.
Definition tushort := Tint I16 Unsigned noattr.
Definition tint := Tint I32 Signed noattr.
Definition tuint := Tint I32 Unsigned noattr.
Definition tbool := Tint IBool Unsigned noattr.
Definition tlong := Tlong Signed noattr.
Definition tulong := Tlong Unsigned noattr.
Definition tfloat := Tfloat F32 noattr.
Definition tdouble := Tfloat F64 noattr.
Definition tptr (t: type) := Tpointer t noattr.
Definition tarray (t: type) (sz: Z) := Tarray t sz noattr.

Definition volatile_attr := {| attr_volatile := true; attr_alignas := None |}.

Definition tattr (a: attr) (ty: type) :=
  match ty with
  | Tvoid => Tvoid
  | Tint sz si _ => Tint sz si a
  | Tlong si _ => Tlong si a
  | Tfloat sz _ => Tfloat sz a
  | Tpointer elt _ => Tpointer elt a
  | Tarray elt sz _ => Tarray elt sz a
  | Tfunction args res cc => Tfunction args res cc
  | Tstruct id _ => Tstruct id a
  | Tunion id  _ => Tunion id a
  end.

Definition tvolatile (ty: type) := tattr volatile_attr ty.

Definition talignas (n: N) (ty: type) :=
  tattr {| attr_volatile := false; attr_alignas := Some n |} ty.

Definition tvolatile_alignas (n: N) (ty: type) :=
  tattr {| attr_volatile := true; attr_alignas := Some n |} ty.

Definition make_composite_env (comps: list composite_definition): composite_env :=
  match build_composite_env comps with
  | OK e => e
  | Error _ => PTree.empty _
  end.
