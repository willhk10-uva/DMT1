/-!
Functional Core, Imperative Shell is a design pattern that separates pure, deterministic logic (the “core”) from side-effecting I/O and interactions (the “shell”).

The pure core:
- Contains business logic expressed as total functions.
- Is easy to test and reason about, free of side‑effects.

The imperative shell:
- Handles I/O, user interaction, and effectful operations.
- Calls into the core, passing in inputs and handling core outputs.

This Lean 4 file demonstrates this pattern with a simple calculator that reads two numbers from the console, computes their sum, and prints the result.
-/

namespace FunctionalCoreImperativeShell

/-- **Core:** A pure function that sums two integers. -/
def sumInts (x y : Int) : Int :=
  x + y

/-- **Core:** A pure parser that reads a string of digits into an integer. -/
def parseInt (s : String) : Option Int :=
  if s.all Char.isDigit then
    some (s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
  else
    none

/-- **Core:** Validates and sums two input strings, returning either an error or the sum. -/
def compute (sa sb : String) : Except String Int :=
  match parseInt sa, parseInt sb with
  | some a, some b => Except.ok (sumInts a b)
  | none, _        => Except.error s!"Invalid integer: '{sa}'"
  | _, none        => Except.error s!"Invalid integer: '{sb}'"

end FunctionalCoreImperativeShell

open FunctionalCoreImperativeShell

/-- **Shell:** Read a line from stdin, trimming whitespace. -/
def readLineTrim : IO String := do
  let h ← IO.getStdin
  let raw ← h.getLine
  pure (raw.trim)

/-- **Shell:** Main program: prompts, reads inputs, calls core, and prints results or errors. -/
def main : IO Unit := do
  IO.println "Enter first integer:"
  let sa ← readLineTrim
  IO.println "Enter second integer:"
  let sb ← readLineTrim
  match compute sa sb with
  | Except.ok sum    => IO.println s!"Sum is {sum}."
  | Except.error msg => IO.eprintln s!"Error: {msg}"

#eval main
