Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

Local Open Scope string.
Local Open Scope list.

Notation "x ^^ y" := (String.append x y) (right associativity, at level 60).

Definition columns := 50.
Definition rows := 50.

Module Colors.
  Definition escape : string -> string := String (ascii_of_nat 27).
  Definition LightBrown := escape "[38;5;172m".
  Definition DarkBrown := escape "[38;5;130m".
  Definition BrownGreen := escape "[38;5;142m".
  Definition Green := escape "[38;5;106m".
  Definition Gray := escape "[38;5;243m".
  Definition R := escape "[0m".
End Colors.

Module Base.
  Definition width := 15.
  Definition art_lines : list string := [
    Colors.Gray ^^ ":" ^^ Colors.Green ^^ "___________" ^^ Colors.DarkBrown ^^
    "./~~\." ^^ Colors.Green ^^ "___________" ^^ Colors.Gray ^^ ":";
    " \                          /";
    "  \________________________/";
    "  (_)                    (_)"
  ].
  Definition art_lines_with_shift : list LString.t :=
    List.map (fun art_line =>
      LString.repeat (LString.s " ") (Nat.div2 columns - width) ++
      LString.s art_line
    ) art_lines.
End Base.

Definition main (argv : list LString.t) : C.t System.effect unit :=
  let new_line := "
" in
  System.log (
    LString.join (LString.s new_line) Base.art_lines_with_shift ++
    LString.s Colors.R
  ).

(** Extract the Bonsai program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main_with_effects := Extraction.launch main.
Extraction "extraction/main" main_with_effects.
