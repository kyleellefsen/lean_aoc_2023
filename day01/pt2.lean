/-
  Advent of Code 2023 Day 1 pt 2.
  Author: Kyle L. Ellefsen
  Date Created: 2023-12-08
  Date Last Modified: 2023-12-09
  Lean 4.3.0
  Executed using `lean --run pt2.lean`
-/

def lists_begin_equal {α : Type} [BEq α] (l1 l2 : List α) : Bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => if x == y then lists_begin_equal xs ys else false
  | [], _ => false
  | _, [] => true

def test_lists_begin_equal : IO Unit := do
  IO.println (lists_begin_equal "eightwothree".toList "eight".toList) -- true
  IO.println (lists_begin_equal "eight".toList "eight23".toList) -- true
  IO.println (lists_begin_equal "eightwothree".toList "seven".toList) -- false
  IO.println (lists_begin_equal "eightwothree".toList "".toList) -- true
  IO.println (lists_begin_equal "z".toList "zero".toList) -- false

def replace_if_starts_with(text: List Char) (old: List Char) (new: Char) :=
  if lists_begin_equal text old then
    let old_length := old.length
    let suffix := text.drop old_length
    new :: suffix
  else
    text



def listCharsToString (lst : List Char) : String :=
  List.foldl (λ acc c => acc ++ c.toString) "" lst

def test_replace_if_starts_with : IO Unit := do
  IO.println (listCharsToString (replace_if_starts_with "eightwothree".toList "eight".toList '8'))  -- 8wothree

def findSingleSome {α : Type} : List (Option α) → Option α
| [] => none
| (some x :: xs) =>
  if xs.any (Option.isSome) then none
  else some x
| (none :: xs) => findSingleSome xs

def get_replacement_char (line: List Char): Option Char :=
  let digitWords : List (String × Char) :=
    [("zero", '0'),
    ("one", '1'),
    ("two", '2'),
    ("three", '3'),
    ("four", '4'),
    ("five", '5'),
    ("six", '6'),
    ("seven", '7'),
    ("eight", '8'),
    ("nine", '9')]
  let option_list : List (Option Char) := digitWords.map (λ pair : (String × Char) =>
    if lists_begin_equal line pair.fst.toList
    then some pair.snd
    else none
  )
  findSingleSome option_list

def build_up_new_charlist (old_charlist : List Char) (skipN : Nat) :=
  match old_charlist with
  | [] => []
  | x :: xs =>
    match skipN with
    | Nat.zero =>
      let new_ch_opt : Option Char := get_replacement_char old_charlist
      match new_ch_opt with
      | none => x :: build_up_new_charlist xs 0
      | some ch =>
        let skip_len := 1
        ch :: build_up_new_charlist xs (skip_len - 1)
    | Nat.succ n =>
      build_up_new_charlist xs n

def test_build_up_new_charlist : IO Unit := do
  IO.println (listCharsToString (build_up_new_charlist "zeroaaa".toList 0))
  IO.println (listCharsToString (build_up_new_charlist "azeroaaa".toList 0))
  IO.println (listCharsToString (build_up_new_charlist "onetwo".toList 0))
  IO.println (listCharsToString (build_up_new_charlist "zerone".toList 0))
  IO.println (listCharsToString (build_up_new_charlist "abcone2threexyz".toList 0))

def replace_text_digit_with_literal (text : String) : String :=
  listCharsToString (build_up_new_charlist text.toList 0)

def test_replace_text_digit_with_literal : IO Unit := do
  let test1 : String := "two1nine"
  let test2 : String := "eightwothree"
  let test3 : String := "abcone2threexyz"
  let test4 : String := "xtwone3four"
  let test5 : String := "4nineeightseven2"
  let test6 : String := "zoneight234"
  let test7 : String := "7pqrstsixteen"
  IO.println (replace_text_digit_with_literal test1) -- 219
  IO.println (replace_text_digit_with_literal test2) -- 8wo3
  IO.println (replace_text_digit_with_literal test3) -- abc123xyz
  IO.println (replace_text_digit_with_literal test4) -- x2ne34
  IO.println (replace_text_digit_with_literal test5) -- 49872
  IO.println (replace_text_digit_with_literal test6) -- z1ight234
  IO.println (replace_text_digit_with_literal test7) -- 7pqrst6teen

def line_to_digit (s: String) : Option Int :=
  let s' := replace_text_digit_with_literal s
  let digits : List Char := s'.toList.filter Char.isDigit
  let get_second: Char → Char → Char := λ _ b => b
  match digits with
  | [] => Option.none
  | first_digit :: xs =>
    let last_digit := xs.foldl get_second first_digit
    let digit_concat := String.mk [first_digit, last_digit]
    digit_concat.toInt?

def test_line_to_digit : IO Unit := do
  let test1 : String := "two1nine"
  let test2 : String := "eightwothree"
  let test3 : String := "abcone2threexyz"
  let test4 : String := "xtwone3four"
  let test5 : String := "4nineeightseven2"
  let test6 : String := "zoneight234"
  let test7 : String := "7pqrstsixteen"
  IO.println (line_to_digit test1) -- some 29
  IO.println (line_to_digit test2) -- some 83
  IO.println (line_to_digit test3) -- some 13
  IO.println (line_to_digit test4) -- some 24
  IO.println (line_to_digit test5) -- some 42
  IO.println (line_to_digit test6) -- some 14
  IO.println (line_to_digit test7) -- some 76

/--
  `sum_ints` takes a list of ints and returns their sum
-/
def sum_optional_ints (lines_digit: List (Option Int)): Option Int :=
  match lines_digit with
  | [] => none
  | l => some (
    l.foldl
      (λ (acc:Int) Opth => match Opth with
         | none => acc
         | some h => acc + h)
      (0: Int)
  )

def test_sum_ints : IO Unit := do
  let test1 : List (Option Int) := [some 2, some 8, some 6]
  let test2 : List (Option Int) := [none, some 8, some 6]
  let test3 : List (Option Int) := []
  IO.println (sum_optional_ints test1) -- some 16
  IO.println (sum_optional_ints test2) -- some 14
  IO.println (sum_optional_ints test3) -- none

/--
  `process_file_contents` takes the entire text file and returns the digit
-/
def process_file_contents (file_contents : String) :=
  let lines : List String := file_contents.splitOn "\n"
  let lines_digit := lines.map line_to_digit
  sum_optional_ints lines_digit

def test_process_file_contents : IO Unit := do
  let test_string : String := "11\n22\n22\n11"
  IO.println (process_file_contents test_string) -- some 66

def main : IO Unit := do
  let filename : System.FilePath := "input.txt"
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
  else
    let file_contents : String ← IO.FS.readFile filename
    let result := process_file_contents file_contents
    match result with
    | none => IO.println "process_file_contents returned none"
    | some n => IO.println s!"Answer: {n}"
