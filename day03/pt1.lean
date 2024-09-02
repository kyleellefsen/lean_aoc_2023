import Mathlib

/-
High Level Strategy
- First, find the [i,j] indices of contiguous numbers in a row. Each one of
  these is a candidate number. Store the number along with its set of indices
- Then, for each candidate number, for each index, scan the surrounding
  chars. If a char contains a symbol (anything that isn't a digit or a period),
  drop the entire number.

Data Structures
  It'll be handy to think of numbers as objects. Each number
  should have 1:1 correspondance with its (un)ordered indices. The indices need
  to be mapped to their surround, so that any symbol can be detected. I could
  create an index-block as an object, and create a function that generates an
  expanded index-block mask, and a function which checks for symbol presence in
  the mask.

  Alternatively, I could do the entire thing in a single pass, iterating through
  characters, looking up their neighbors, and either adding or discarding the
  accumulated number into a list. This option would probably be faster but
  would be less modular, and wouldn't let me play with lean data types.

  So I'll go multipass and create temporary data structures. I'll need:
    Data Types:
    - A character grid to store the raw input
    - An index block that contains both the mask of the number and the expanded
      mask.
    - A (number × index block) type that enables storage of the numbers and
      their corresponding positions in the character grid

    Functions:
    [x] A function that parses the raw text input and produces a char grid
    [x] A function that extracts the number×positions from the grid
    [x] A function that expands the index block of number position
    [x] A function that checks if an index block contains a symbol.



-/

abbrev CharGrid := Array (Array Char)
abbrev IndexBlock := List (ℕ × ℕ)
abbrev NumPos := ℕ × IndexBlock

def ex_txtinput := "467..114..
...*......
..35..633.
......#...
617*......
.....+.58.
..592.....
......755.
...$.*....
.664.598.."


def parseGrid (input: String) : CharGrid :=
  input.splitOn "\n"
  |>.filter (·.length > 0)  -- Remove any empty lines
  |>.map (·.toList.toArray)
  |>.toArray

#eval IO.println (parseGrid ex_txtinput)[0]!


def numpos_of_chargrid_aux (num_acc : String)
                           (row_idx col_idx : ℕ)
                           (numpos_list: List NumPos): List NumPos :=
  let n : Nat := num_acc.toNat!
  let i := row_idx
  let j₀ := col_idx - num_acc.length
  let block: IndexBlock :=
    (num_acc.foldl
      (init := (j₀, ([]: IndexBlock)))
      λ (j, idx_block) _ ↦ (j+1, idx_block ++ [(i, j)])
    ).snd
    let new_numpos : NumPos := (n, block)
  let new_numpos_list := numpos_list ++ [new_numpos]
  new_numpos_list

/- Finds all the numbers in the character grid, and stores them in a list
of (number, indexblock). -/
def numpos_of_chargrid (grid: CharGrid) : List NumPos :=
  let numpos_list₀ : List NumPos := []
  (grid.foldl (init := (0, numpos_list₀))  -- outer_acc := ⟨row_idx, list of number positions⟩
    λ (row_idx, numpos_list) row ↦
      let row_accum := (
        row.foldl (init := (0, numpos_list, ""))
          λ (col_idx, numpos_list, num_acc) c ↦
            if c.isDigit
            then (col_idx+1, numpos_list, num_acc ++ c.toString)
            else if num_acc.length > 0  -- if we are done building a number
            then
              let new_numpos_list := numpos_of_chargrid_aux num_acc row_idx col_idx numpos_list
              (col_idx+1, new_numpos_list, "")
            else (col_idx+1, numpos_list, num_acc)
        )
      let ⟨col_idx, numpos_list, num_acc⟩ := row_accum
      let new_numpos_list :=
        if num_acc.length > 0  -- if we are done building a number
        then numpos_of_chargrid_aux num_acc row_idx col_idx numpos_list
        else numpos_list
      (row_idx + 1, new_numpos_list)).snd
#eval numpos_of_chargrid (parseGrid ex_txtinput)



/--Takes a list of 2D indices and returns all the indices around them, including
adjacent indices. Does not include the original indices, or out of bounds
indices.
-/
def dilate_IndexBlock (block₀: IndexBlock) (nRows nCols :ℕ) : IndexBlock:=
  let init_blockset :  Std.HashSet (ℕ×ℕ) := Std.HashSet.ofList block₀
  let full_blockset :  Std.HashSet (ℕ×ℕ) := init_blockset.fold
    (init := Std.HashSet.ofList ([]: List (ℕ×ℕ)))
    λ adj idx ↦
      let ⟨x, y⟩ := idx  -- x is row index, y is col index
      let Δxs := if x = 0
                 then [0, 1]
                 else if x ≥ nRows - 1
                 then [-1, 0]
                 else [-1, 0, 1]
      let Δys := if y = 0
                 then [0, 1]
                 else if y ≥ nCols - 1
                 then [-1, 0]
                 else [-1, 0, 1]
      -- Cartesian Product
      let Δxys : List (ℤ×ℤ) := List.join (Δxs.map (λx ↦ Δys.map (λy ↦ (x, y))))
      let xys : List (ℕ×ℕ) := Δxys.map
        λ⟨Δx, Δy⟩ ↦ ⟨(x + Δx).toNat, (y + Δy).toNat⟩
      adj.insertMany xys
  -- HashSet difference is not in the standard library, so we'll do it manually
  let adj_blockset := init_blockset.fold
    (init:= full_blockset)
    λremainder idx ↦
      if remainder.contains idx
      then remainder.erase idx
      else remainder
  adj_blockset.toList

#eval dilate_IndexBlock [(0, 0), (0, 1), (0, 2)] 10 10

def block_has_symbol (grid: CharGrid) (block: IndexBlock) : Option Bool :=
  match block with
  | [] => some false
  | ⟨x, y⟩::idxs =>
    if hx: x ≥ grid.size then none else
    if hy: y ≥ grid[x].size then none else
    let c := (grid[x])[y]'(by omega)
    if c.isDigit ∨ c = '.'
    then block_has_symbol grid idxs
    else some true

#eval block_has_symbol (parseGrid ex_txtinput) [(0, 0), (0, 1), (0, 2)]

def answer_of_txtinput (txtinput: String) : Option ℕ:=
  let grid := parseGrid txtinput
  if hx: 0 ≥ grid.size then none else
  let nRows := grid.size
  let nCols := grid[0].size
  grid
  |> numpos_of_chargrid
  |>.map (λ⟨n, block⟩ ↦ (n, dilate_IndexBlock block nRows nCols))
  |>.map (λ⟨n, block⟩ ↦ (n, block_has_symbol grid block))
  |>.filter (λ⟨_, block⟩ ↦ match block with
    | some true => true
    | _ => false)
  |>.map (·.fst)
  |>.foldl (init:=0) (·+·)
  |> (some ·)

#eval answer_of_txtinput ex_txtinput


def main : IO Unit := do
  let filename : System.FilePath := "input.txt"
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
  else
    let file_contents : String ← IO.FS.readFile filename
    let opt_result := answer_of_txtinput file_contents
    match opt_result with
    | some result => IO.println s!"Answer: {result}"
    | none => IO.println s!"answer_of_txtinput returned none"


#eval main
