import Mathlib

structure Draw where
  r : Nat
  g : Nat
  b : Nat
deriving Repr

def Game : Type := List Draw
def Bag : Type := Draw

class Foldable (t : Type → Type) where
  foldl : (β → α → β) → β → t α → β
instance : Foldable List where
  foldl := List.foldl
instance : Foldable Array where
  foldl := Array.foldl
def agg_by_add {α : Type} [AddMonoid α] {β: Type → Type} [Foldable β]
    (arr: β α): α :=
  Foldable.foldl (·+·) 0 arr  -- here 0 is the additive identity
notation:70 "⨁ " xs => agg_by_add xs

def parse_line_to_game (line: String)  :=
  let line_cleaned := (line.splitOn ":")[1]!.trim
  (((line_cleaned.splitOn ";")
    ).filter (¬·.isEmpty)
      ).map λ(draw_str : String) ↦
        let draw_str_clean := draw_str.trim
        let color_strs := draw_str_clean.splitOn ", "
        let draw₀ : Draw := {r := 0, g := 0, b := 0}
        color_strs.foldl (init:= draw₀) λ draw color_count ↦
          let parts := color_count.trim.splitOn " "
          let count := parts[0]!.toNat!
          match parts[1]! with
          | "red"   => {draw with r := count}
          | "green" => {draw with g := count}
          | "blue"  => {draw with b := count}
          | _       => draw
#eval parse_line_to_game "Game 1: 4 red, 5 blue, 9 green; 7 green, 7 blue, 3 red; 10 red; "

def games_of_txtinput (txt_input: String) : List Game:=
  ((txt_input.splitOn "\n").filter
    (¬·.isEmpty)).map  -- removes empty lines
      parse_line_to_game  -- converts each line to a Game

def maxcubes_of_game (game : Game) : Bag :=
  game.foldl
    (init := ({r:=0, g:=0, b:=0}:Bag))
    λ acc draw ↦
      ({r := Nat.max acc.r draw.r,
        g := Nat.max acc.g draw.g,
        b := Nat.max acc.b draw.b}: Bag)

def power_of_maxcubes (bag : Bag) : Nat :=
  bag.r * bag.g * bag.b

def maxcubes_of_txtinput (txtinput : String) : ℕ :=
  ⨁ (games_of_txtinput txtinput).map (power_of_maxcubes ∘ maxcubes_of_game)

#eval maxcubes_of_txtinput "Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green"




def main : IO Unit := do
  let filename : System.FilePath := "input.txt"
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
  else
    let file_contents : String ← IO.FS.readFile filename
    let result := maxcubes_of_txtinput file_contents
    IO.println s!"Answer: {result}"
#eval main
