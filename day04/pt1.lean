import Mathlib

def count_matches (card: List ℕ × List ℕ) : ℕ :=
  let (winning, ticket) := card
  ticket.foldl (init := 0) λ (acc : ℕ) (n : ℕ) ↦
    if winning.contains n then acc + 1 else acc
#eval count_matches ([41,48,83,86,17], [83,86,6,31,17,9,48,53]) -- 4

def get_points (num_matches: ℕ) : ℕ :=
  match num_matches with
  | 0 => 0
  | n + 1 => 2 ^ n
#eval #[0,1,2,3] |>.map get_points -- #[0, 1, 2, 4]

def text_to_card (txt : String) : List ℕ × List ℕ :=
  let parts := (txt.splitOn ":")[1]!.splitOn " | "
  let winning := parts[0]!.splitOn " " |>.filter (·.length > 0) |>.map String.toNat!
  let ticket := parts[1]!.splitOn " " |>.filter (·.length > 0) |>.map String.toNat!
  (winning, ticket)

#eval text_to_card "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53"
#eval get_points (count_matches (text_to_card "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53"))

def answer_of_txtinput (input : String) : Option ℕ :=
  -- first, split each line by '\n'
  let lines : List String := input.splitOn "\n" |>.filter (· ≠ "")
  let points : List ℕ := lines.map (λ line ↦ get_points (count_matches (text_to_card line)))
  -- finally sum points
  let sum := points.foldl (init := 0) (·+·)
  some sum


def main : IO Unit := do
  let filename : System.FilePath := "day04/input.txt"
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
  else
    let file_contents : String ← IO.FS.readFile filename
    let opt_result := answer_of_txtinput file_contents
    match opt_result with
    | some result => IO.println s!"Answer: {result}"
    | none => IO.println s!"answer_of_txtinput returned none"

#eval main
