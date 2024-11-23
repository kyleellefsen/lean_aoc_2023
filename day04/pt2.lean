import Mathlib
import Batteries.Data.Vector
open Batteries (Vector)

def count_matches (card: List ℕ × List ℕ) : ℕ :=
  let (winning, ticket) := card
  ticket.foldl (init := 0) λ (acc : ℕ) (n : ℕ) ↦
    if winning.contains n then acc + 1 else acc
#eval count_matches ([41,48,83,86,17], [83,86,6,31,17,9,48,53]) -- 4

def text_to_card (txt : String) : List ℕ × List ℕ :=
  let parts := (txt.splitOn ":")[1]!.splitOn " | "
  let winning := parts[0]!.splitOn " " |>.filter (·.length > 0) |>.map String.toNat!
  let ticket := parts[1]!.splitOn " " |>.filter (·.length > 0) |>.map String.toNat!
  (winning, ticket)

#eval text_to_card "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53"

def input_test := "Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11"

def num_matches := input_test.splitOn "\n"
    |>.map (λ line ↦ count_matches (text_to_card line))
#eval num_matches


def get_final_card_count (num_matches : List ℕ) : Vector ℕ num_matches.length :=
    -- First, create a vector of ones called 'card_count' with the same length
    -- as num_matches.
    -- Then, iterate through each element in num_matches. For the ith element,
    -- which has value n, increment elements of card_count from [i+1] to [i+n] by
    -- the ith value of card_count. Then continue.

    -- The tricky part here is making sure the indices are correct. If
    -- num_matches[i] = 0, then don't do anything. If it is 1, increment card
    -- count[i+1]. If it is 2, increment card_count[i+1] and card_count[i+2].

    let VecN := Vector ℕ num_matches.length
    let rec process_cards (card_count : VecN) (i : ℕ) : VecN :=
      if h₁: i < num_matches.length then
        let n := card_count[i]
        let idxs_to_update := List.range num_matches[i] |>.map (· + i + 1)
        let card_count' := idxs_to_update.foldl
            (init := card_count)
            (λ acc idx ↦ acc.setD idx (acc[idx]! + n))
        process_cards card_count' (i + 1)
      else
        card_count
    let initial_card_count : VecN := Vector.mkVector num_matches.length 1
    (process_cards initial_card_count 0)

#check get_final_card_count

#eval get_final_card_count num_matches
#eval (get_final_card_count num_matches).toList.sum

def answer_of_txtinput (input : String) :=
  -- first, split each line by '\n'
  let lines : List String := input.splitOn "\n" |>.filter (· ≠ "")
  let num_matches : List ℕ := lines.map (λ line ↦ count_matches (text_to_card line))
--   some num_matches
  let final_card_count := get_final_card_count num_matches
  -- finally sum card counts
  let sum := final_card_count.toList.sum
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

/--
info: true
-/
#guard_msgs in #eval 3+3=6

#check_failure 1 + 1 = "hello"

⟨ ⟩
