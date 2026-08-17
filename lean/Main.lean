import SharpKnapsack.DivideConquer

/-!
CLI for the verified #Knapsack FPTAS.

    lake exe sharpknapsack <ε> <capacity> <w₁> <w₂> …

`ε` is a rational like `1/10` (must satisfy 0 < ε ≤ 1). Prints the
approximate number of subsets of the weights with total weight ≤ capacity;
for small instances (n ≤ 15) also prints the exact count for comparison.
-/

def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [a] => a.toNat?.map fun n => (n : ℚ)
  | [a, b] =>
    match a.toNat?, b.toNat? with
    | some x, some y => if y = 0 then none else some ((x : ℚ) / (y : ℚ))
    | _, _ => none
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | epsStr :: capStr :: wStrs =>
    let some ε := parseRat epsStr
      | IO.eprintln s!"error: cannot parse ε from '{epsStr}' (expected e.g. 1/10)"
        return 1
    if ε ≤ 0 || 1 < ε then
      IO.eprintln s!"error: ε must satisfy 0 < ε ≤ 1, got {ε}"
      return 1
    let some C := capStr.toNat?
      | IO.eprintln s!"error: cannot parse capacity from '{capStr}'"
        return 1
    let mut S : List ℕ := []
    for w in wStrs do
      let some n := w.toNat?
        | IO.eprintln s!"error: cannot parse weight '{w}'"
          return 1
      S := S ++ [n]
    let answer := approxCount S C ε
    IO.println s!"items: {S.length}, capacity: {C}, ε = {ε}"
    IO.println s!"approximate #subsets with weight ≤ {C}: {answer}"
    if S.length ≤ 15 then
      IO.println s!"exact (brute force, for comparison):   {countLe S C}"
    return 0
  | _ =>
    IO.eprintln "usage: sharpknapsack <ε> <capacity> <w₁> <w₂> …"
    IO.eprintln "example: sharpknapsack 1/10 15 3 1 4 1 5 9 2 6"
    return 1
