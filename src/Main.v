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
Definition rows := 30.
Definition lifeStart := 28.
Definition multiplier := 5.
Definition branchesMax := multiplier * 110.
Definition shootsMax := multiplier.

Module Random.
  Definition t : Set := N * N.

  Definition seed : t := (2, 2) % N.

  Definition M : N := 1000.

  Definition next (seed : t) : t :=
    let '(n, n') := seed in
    let n'' := N.modulo (n + n') M in
    (n', n'').
End Random.

Module M.
  Definition t (A : Set) : Set :=
    Random.t -> A * Random.t.

  Definition ret {A : Set} (x : A) : t A :=
    fun seed => (x, seed).

  Definition bind {A B : Set} (x : t A) (f : A -> t B) : t B :=
    fun seed =>
      let '(x', seed') := x seed in
      f x' seed'.

  Definition random (n : nat) : t nat :=
    fun seed =>
      let seed' := Random.next seed in
      let result := N.to_nat (N.modulo (fst seed) (N.of_nat n)) in
      (result, seed').

  Definition run {A : Set} (x : t A) (seed : Random.t) : A :=
    fst (x seed).
End M.

Notation "'let?' x ':=' X 'in' Y" :=
  (M.bind X (fun x => Y))
  (at level 200, x pattern, X at level 100, Y at level 200).

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

  Record t : Set := {
    pixels : list (list (string * string));
    trace : list (nat * nat * Typ * string)
  }.

  Definition init : t := {|
    pixels := List.repeat (List.repeat (Colors.R, " ") (columns + 1)) (rows + 1);
    trace := []
  |}.

  Definition set (grid : t) (x y : nat) (typ : Typ) (color : string)
    (chars : string) : t :=
    {|
      pixels :=
        List.apply_ith grid.(pixels) y (fun line =>
          List.apply_ith line x (fun _ =>
            match chars with
            | EmptyString => (Colors.R, " ")
            | String c _ => (color, String c EmptyString)
            end
          )
        );
      trace := cons (x, y, typ, chars) grid.(trace)
    |}.

  (* Get dy based on type. *)
  Definition get_dy (y : nat) (typ : Typ) (life : nat) : M.t Z :=
    let? rand10 := M.random 10 in
    let dy :=
      match typ with
      | Dying =>
        match rand10 with
        | 0 | 1 => (-1) % Z
        | 9 => 1 % Z
        | _ => 0 % Z
        end
      | ShootLeft | ShootRight =>
        match rand10 with
        | 0 | 1 => (-1) % Z
        | 8 | 9 => 1 % Z
        | _ => 0 % Z
        end
      | _ =>
        if negb (Nat.eqb life lifeStart) && Nat.ltb 2 rand10 then
          (-1) % Z
        else
          0 % Z
      end in
    (* If we're about to hit the ground, cut it off. *)
    if
      (Z.gtb dy 0 && Nat.ltb y (rows - 1)) || (isTrunk typ && Nat.ltb life 4)
    then
      M.ret (0 % Z)
    else
      M.ret dy.

  (* Get dx based on type. *)
  Definition get_dx (typ : Typ) : M.t Z :=
    match typ with
    | ShootLeft => (* tend left: dx=[-2,1] *)
      let? rand10 := M.random 10 in
      M.ret match rand10 with
      | 0 | 1 => (-2) % Z
      | 2 | 3 | 4 | 5 => (-1) % Z
      | 6 | 7 | 8 => 0 % Z
      | _ => 1 % Z
      end
    | ShootRight => (* tend right: dx=[-1,2] *)
      let? rand10 := M.random 10 in
      M.ret match rand10 with
      | 0 | 1 => 2 % Z
      | 2 | 3 | 4 | 5 => 1 % Z
      | 6 | 7 | 8 => 0 % Z
      | _ => (-1) % Z
      end
    | Dying => (* tend left/right: dx=[-3,3] *)
      let? rand7 := M.random 7 in
      M.ret (Z.of_nat rand7 - 2) % Z
    | _ => (* tend equal: dx=[-1,1] *)
      let? rand3 := M.random 3 in
      M.ret (Z.of_nat rand3 - 1) % Z
    end.

  Fixpoint branch (grid : t) (branches : nat) (shoots : nat)
    (isShootRight : bool) (x y : nat) (typ : Typ) (life : nat) (fuel : nat)
    {struct fuel} : M.t t :=
    match life, fuel with
    | O, _ | _, O => M.ret grid
    | S life, S fuel =>
      let? dy := get_dy y typ life in
      let? dx := get_dx typ in
      let branches := branches + 1 in
      (* Re-branch upon conditions. *)
      let? (grid, shoots, isShootRight) :=
        let current := (grid, shoots, isShootRight) in
        if Nat.ltb branches branchesMax then
          let? rand16_multiplier := M.random (16 - multiplier) in
          (* Branch is dead. *)
          if Nat.ltb life 3 then
            let? grid := branch grid branches shoots isShootRight x y Dead life fuel in
            M.ret (grid, shoots, isShootRight)
          (* Branch is dying and needs to branch into leaves. *)
          else if (isShoot typ || isTrunk typ) && Nat.ltb life (multiplier + 2) then
            let? grid := branch grid branches shoots isShootRight x y Dying life fuel in
            M.ret (grid, shoots, isShootRight)
          (* Re-branch if: not close to the base AND (pass a chance test OR be a trunk, not have too many shoots already, and not be about to die) *)
          else if
            isTrunk typ && Nat.ltb life (lifeStart - 8) &&
            (
              Nat.eqb rand16_multiplier 0 ||
              (Nat.eqb (Nat.modulo life 5) 0 && Nat.ltb 5 life)
            )
          then
            (* If a trunk is splitting and not about to die, chance to create another trunk *)
            let? rand3 := M.random 3 in
            if Nat.eqb rand3 0 && Nat.ltb 7 life then
              let? grid := branch grid branches shoots isShootRight x y Trunk life fuel in
              M.ret (grid, shoots, isShootRight)
            else if Nat.ltb shoots shootsMax then
              (* Give the shoot some life. *)
              let life := life + multiplier - 2 in

              (* Shoots alternate from the first. *)
              let isShootRight := negb isShootRight in
              let typ := if isShootRight then ShootRight else ShootLeft in
              let? grid := branch grid branches shoots isShootRight x y typ life fuel in
              M.ret (grid, shoots + 1, isShootRight)
            else
              M.ret current
          else
            M.ret current
        else
          M.ret current in
      (* Implement dx, dy. *)
      let x := Z.to_nat (Z.of_nat x + dx) in
      let y := Z.to_nat (Z.of_nat y + dy) in
      (* Choose color. *)
      let? rand4 := M.random 4 in
      let color :=
        match typ with
        | ShootLeft | ShootRight | Trunk =>
          if Nat.eqb rand4 0 then
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
        | _ => ""
        end in
      (* Choose leaf character. *)
      let chars :=
        if Nat.ltb life 4 then
          "&"
        else
          chars in
      (* Add character(s) to our grid. *)
      let grid := set grid x y typ color chars in
      branch grid branches shoots isShootRight x y typ life fuel
    end.

  Definition grow : M.t t :=
    let? rand2 := M.random 2 in
    let isShootRight := Nat.eqb rand2 0 in
    let fuel := columns * rows in
    branch init 0 0 isShootRight (Nat.div2 columns) rows Trunk lifeStart fuel.

  Definition to_string (grid : t) : LString.t :=
    List.concat
      (List.map (fun line =>
          List.concat (List.map (fun '(color, chars) =>
            LString.s (color ^^ chars)) line
          ) ++ LString.s new_line
        )
        grid.(pixels)
      ).
End Grid.

Definition main (argv : list LString.t) : C.t System.effect unit :=
  let seed :=
    match argv with
    | [_; n; m] =>
      match LString.to_N 10 n, LString.to_N 10 m with
      | Some n, Some m => (n, m)
      | _, _ => Random.seed
      end
    | _ => Random.seed
    end in
  let grid := M.run Grid.grow seed in
  System.log (
    Grid.to_string grid ++
    LString.join (LString.s new_line) Base.art_lines_with_shift ++
    LString.s Colors.R
  ).

(** Extract the Bonsai program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main_with_effects := Extraction.launch main.
Extraction "extraction/main" main_with_effects.
