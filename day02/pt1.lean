import Mathlib

structure Draw where
  r : Nat
  g : Nat
  b : Nat
deriving Repr

def Game : Type := List Draw
def Bag : Type := Draw

def game_possible (bag: Bag) : Game → Bool
  | [] => true
  | draw :: game =>
    if (draw.r ≤ bag.r) ∧ (draw.g ≤ bag.g) ∧ (draw.b ≤ bag.b)
    then game_possible bag game
    else false

def test_line_to_digit : IO Unit := do
  let game1 : Game := [{r := 4, g := 0, b := 3},
                      {r := 1, g := 2, b := 6},
                      {r := 0, g := 2, b := 0}]
  let game2 : Game := [{r := 0, g := 2, b := 1},
                      {r := 1, g := 3, b := 4},
                      {r := 1, g := 1, b := 1}]
  let game3 : Game := [{r := 20, g := 8, b := 6},
                      {r := 4, g := 13, b := 5},
                      {r := 1, g := 5, b := 0}]
  let bag : Bag := {r := 12, g := 13, b := 14}
  IO.println (game_possible bag game1) -- true
  IO.println (game_possible bag game2) -- true
  IO.println (game_possible bag game3) -- false


def add_consistent_game_indices (games : List Game) (bag : Bag) (curr_idx : Nat := 1) (acc : Nat := 0) : Nat :=
  match games with
  | [] => acc
  | game :: games₂ =>
    let new_acc : Nat :=
      if game_possible bag game
      then acc + curr_idx
      else acc
    add_consistent_game_indices games₂ bag (curr_idx + 1) new_acc

def acc_matching_line_idxs (matching_lines : List Bool) : Nat :=
  (matching_lines.foldl (init := (0, 1))
    λ⟨acc, idx⟩ b ↦ ⟨if b then acc+idx else acc, idx+1⟩).fst


def parse_line_to_game (line : String) : Game :=
  let line_cleaned := (line.split (·=':'))[1]!  -- line_cleaned := " 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green"
  (line_cleaned.split (·=';')).map λ(draw_str : String) ↦ -- draw_str := " 3 blue, 4 red"
    let draw₀ : Draw := {r := 0, g := 0, b := 0}
    (draw_str.split (·=',')).foldl  (init := draw₀) -- Is there a way to call `.foldl` without parentheses?
      λ(draw: Draw) (color_str : String) ↦ -- color_str := " 3 blue"
        let color_count_str : String := color_str.foldl (init := "") λ acc c ↦
          acc ++ (if c.isDigit then c.toString else "")
        let color_count : Nat := color_count_str.toNat!
        let colors := ["red", "green", "blue"]
        let color_matcher := λs : String ↦ colors.map λc ↦ s.containsSubstr c
        let contains_rgb : List Bool := color_matcher color_str
        let draw := if contains_rgb[0]!
            then {draw with r := color_count}
            else draw
        let draw := if contains_rgb[1]!
            then {draw with g := color_count}
            else draw
        let draw := if contains_rgb[2]!
            then {draw with b := color_count}
            else draw
    draw


def txt_input_to_matching_lines (txt_input : String) (bag: Bag) : List Bool :=
   (((
   txt_input.splitOn "\n"
    ).filter (¬·.isEmpty)  -- removes empty lines
      ).map parse_line_to_game  -- converts each line to a Game
        ).map (game_possible bag ·)  -- converts each Game to Bool

def process_file_contents (file_contents : String): Nat :=
  let bag : Bag := {r := 12, g := 13, b := 14}
  let matching_lines: List Bool := txt_input_to_matching_lines file_contents bag
  acc_matching_line_idxs matching_lines

def test_process_file_contents : IO Unit := do
  let example_input := "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"
  IO.println (process_file_contents example_input) -- 8
#eval test_process_file_contents


def main : IO Unit := do
  let filename : System.FilePath := "input.txt"
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
  else
    let file_contents : String ← IO.FS.readFile filename
    let result := process_file_contents file_contents
    IO.println s!"Answer: {result}"
#eval main
