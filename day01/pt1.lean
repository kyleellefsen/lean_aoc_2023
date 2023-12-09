/-
  Advent of Code 2023 Day 1 pt 1.
  Author: Kyle L. Ellefsen
  Date Created: 2023-12-08
  Date Last Modified: 2023-12-08
-/

/--
  `line_to_digit` takes a line, extracts the first and last digit, concatenates
  them, converts them to an Int, and returns the result
-/
def line_to_digit (s: String) : Option Int :=
  let digits : List Char := s.toList.filter Char.isDigit
  let get_second: Char → Char → Char := λ _ b => b
  match digits with
  | [] => Option.none
  | first_digit :: xs =>
    let last_digit := xs.foldl get_second first_digit
    let digit_concat := String.mk [first_digit, last_digit]
    digit_concat.toInt?

def test_line_to_digit : IO Unit := do
  let test1 : String := "eighteight9dnvcqznjvfpreight"
  let test2 : String := "eighteight9dnvcqznjv8fpreight"
  let test3 : String := "eighteight9dnv7cqznjl3fpreight"
  let test4 : String := ""
  IO.println (line_to_digit test1) -- some 99
  IO.println (line_to_digit test2) -- some 98
  IO.println (line_to_digit test3) -- some 93
  IO.println (line_to_digit test4) -- none


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
