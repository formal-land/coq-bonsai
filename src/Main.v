Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

Local Open Scope bool.
Local Open Scope string.
Local Open Scope list.

Notation "x ^^ y" := (String.append x y) (right associativity, at level 60).

Definition columns := 50.
Definition rows := 50.
Definition lifeStart := 28.
Definition multiplier := 5.
Definition branchesMax := multiplier * 110.

Definition random max := Nat.modulo 12 max.

Definition new_line := "
".

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

Module List.
  Fixpoint apply_ith {A : Type} (l : list A) (index : nat) (f : A -> A)
    : list A :=
    match l with
    | nil => nil
    | cons x l =>
      match index with
      | O => cons (f x) l
      | S index => cons x (apply_ith l index f)
      end
    end.
End List.

Module Grid.
  Record t : Set := {
    pixels : list (list (string * string));
    trace : list (nat * nat)
  }.

  Definition init : t := {|
    pixels := List.repeat (List.repeat (Colors.R, " ") (columns + 1)) (rows + 1);
    trace := []
  |}.

  Definition set (grid : t) (x y : nat) (color : string) (chars : string) : t := {|
    pixels :=
      List.apply_ith grid.(pixels) y (fun line =>
        List.apply_ith line x (fun _ =>
          match chars with
          | EmptyString => (Colors.R, " ")
          | String c _ => (color, String c EmptyString)
          end
        )
      );
    trace := cons (x, y) grid.(trace)
  |}.

  Inductive Typ : Set :=
  | Dead
  | Dying
  | ShootLeft
  | ShootRight
  | Trunk.

  Definition isShoot (typ : Typ) : bool :=
    match typ with
    | ShootLeft | ShootRight => true
    | _ => false
    end.

  Definition isTrunk (typ : Typ) : bool :=
    match typ with
    | Trunk => true
    | _ => false
    end.

  (* Get dy based on type. *)
  Definition get_dy (y : nat) (typ : Typ) (life : nat) : Z :=
    let dy :=
      match typ with
      | Dying =>
        match random 10 with
        | 0 | 1 => (-1) % Z
        | 9 => 1 % Z
        | _ => 0 % Z
        end
      | ShootLeft | ShootRight =>
        match random 10 with
        | 0 | 1 => (-1) % Z
        | 8 | 9 => 1 % Z
        | _ => 0 % Z
        end
      | _ =>
        if Nat.eqb life lifeStart && (2 <? random 10) then
          (-1) % Z
        else
          0 % Z
      end in
    (* If we're about to hit the ground, cut it off. *)
    if
      (Z.gtb dy 0 && Nat.ltb y (rows - 1)) || (isTrunk typ && Nat.ltb life 4)
    then
      0 % Z
    else
      dy.

  (* Get dx based on type. *)
  Definition get_dx (typ : Typ) : Z :=
    match typ with
    | ShootLeft => (* tend left: dx=[-2,1] *)
      match random 10 with
      | 0 | 1 => (-2) % Z
      | 2 | 3 | 4 | 5 => (-1) % Z
      | 6 | 7 | 8 => 0 % Z
      | _ => 1 % Z
      end
    | ShootRight => (* tend right: dx=[-1,2] *)
      match random 10 with
      | 0 | 1 => 2 % Z
      | 2 | 3 | 4 | 5 => 1 % Z
      | 6 | 7 | 8 => 0 % Z
      | _ => (-1) % Z
      end
    | Dying => (* tend left/right: dx=[-3,3] *)
      (Z.of_nat (random 7) - 2) % Z
    | _ => (* tend equal: dx=[-1,1] *)
      (Z.of_nat (random 3) - 1) % Z
    end.

  Fixpoint branch (grid : t) (branches : nat) (x y : nat) (typ : Typ)
    (life : nat) : t :=
    match life with
    | O => grid
    | S life =>
      let dy := get_dy y typ life in
      let dx := get_dx typ in
      let branches := S branches in
      (* Re-branch upon conditions. *)
      let grid :=
        if Nat.ltb branches branchesMax then
          (* Branch is dead. *)
          if Nat.ltb life 3 then
            branch grid branches x y Dead life
          (* Branch is dying and needs to branch into leaves. *)
          else if (isShoot typ || isTrunk typ) && Nat.ltb life (multiplier + 2) then
            branch grid branches x y Dying life
          (* Re-branch if: not close to the base AND (pass a chance test OR be a trunk, not have too many shoots already, and not be about to die) *)
          else if
            isTrunk typ && Nat.ltb life (lifeStart - 8) &&
            (
              Nat.eqb (random (16 - multiplier)) 0 ||
              (Nat.eqb (Nat.modulo life 5) 0 && Nat.ltb 5 life)
            )
          then
            (* If a trunk is splitting and not about to die, chance to create another trunk *)
            if Nat.eqb (random 3) 0 && Nat.ltb 7 life then
              branch grid branches x y Trunk life
            else
              grid (*TODO*)
          else
            grid
        else
          grid in
      (* Implement dx, dy. *)
      let x := Z.to_nat (Z.of_nat x + dx) in
      let y := Z.to_nat (Z.of_nat y + dy) in
      (* Choose color. *)
      let color :=
        match typ with
        | ShootLeft | ShootRight | Trunk =>
          if Nat.eqb (random 4) 0 then
            Colors.LightBrown
          else
            Colors.DarkBrown
        | Dying => Colors.BrownGreen
        | Dead => Colors.Green
        end in
      (* Choose branch character. *)
      let chars : string :=
        match typ with
        | Trunk =>
          let chars :=
            if Z.ltb dx 0 then
              "\"
            else if Z.eqb dx 0 then
              "/|"
            else
              "/" in
          if Z.eqb dy 0 then
            "/~"
          else
            chars
        (* Shoots tend to look horizontal. *)
        | ShootLeft =>
          let chars :=
            if Z.ltb dx 0 then
              "\|"
            else if Z.eqb dx 0 then
              "/|"
            else
              "/" in
          (* growing down *)
          if Z.gtb dy 0 then
            "/"
          (* not growing *)
          else if Z.eqb dy 0 then
            "\_"
          else
            chars
        | ShootRight =>
          let chars :=
            if Z.ltb dx 0 then
              "\|"
            else if Z.eqb dx 0 then
              "/|"
            else
              "/" in
          (* growing down *)
          if Z.gtb dy 0 then
            "\"
          (* not growing *)
          else if Z.eqb dy 0 then
            "_/"
          else
            chars
        | _ => "<->"
        end in
      (* Choose leaf character. *)
      let chars :=
        if Nat.ltb life 4 then
          "&"
        else
          chars in
      (* Add character(s) to our grid. *)
      let grid := set grid x y color chars in
      branch grid branches x y typ life
    end.

  Definition grow : t :=
    branch init 0 (Nat.div2 columns) rows Trunk lifeStart.
(* Compute grow. *)

  Definition to_string (grid : t) : LString.t :=
    List.concat
      (List.map (fun line =>
          List.concat (List.map (fun '(color, chars) => LString.s (color ^^ chars)) line) ++ LString.s new_line
        )
        grid.(pixels)
      ).
End Grid.

Definition main (argv : list LString.t) : C.t System.effect unit :=
  System.log (
    Grid.to_string Grid.grow ++
    LString.join (LString.s new_line) Base.art_lines_with_shift ++
    LString.s Colors.R
  ).

(** Extract the Bonsai program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main_with_effects := Extraction.launch main.
Extraction "extraction/main" main_with_effects.
