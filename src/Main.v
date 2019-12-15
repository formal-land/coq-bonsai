Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

Definition main (argv : list LString.t) : C.t System.effect unit :=
  System.log (LString.s "Bonsai!").

(** Extract the Bonsai program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main_with_effects := Extraction.launch main.
Extraction "extraction/main" main_with_effects.
