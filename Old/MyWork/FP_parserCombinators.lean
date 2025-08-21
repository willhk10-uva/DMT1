/-!
Parser combinators are higher-order functions that build complex parsers by combining simpler ones. They enable:

1. **Modularity**: Define small, reusable parsers and compose them.
2. **Readability**: Grammar-like structure in code.
3. **Backtracking and choice**: Easily express alternatives.
-/

namespace ParserCombinators

/-- A simple parser type: input `String → Option (result × remaining)` -/
def Parser (α : Type) := String → Option (α × String)

/-- Run a parser on input. -/
def run {α : Type} (p : Parser α) (s : String) : Option (α × String) :=
  p s

/-- Parser that always fails. -/
def failure {α : Type} : Parser α := fun _ => none

/-- Parser that consumes no input and returns `a`. -/
def pure {α : Type} (a : α) : Parser α := fun s => some (a, s)

/-- Parser that consumes a single character if it satisfies predicate `pred`. -/
def satisfy (pred : Char → Bool) : Parser Char := fun s =>
  match s.toList with
  | []      => none
  | c :: cs => if pred c then some (c, cs.asString) else none

/-- Parser for a specific character `c`. -/
def char (c : Char) : Parser Char := satisfy (· == c)

/-- Parser for any digit character. -/
def digit : Parser Char := satisfy Char.isDigit

/-- Sequencing combinator: p1 >>= f -/
def bind {α β} (p : Parser α) (f : α → Parser β) : Parser β := fun s =>
  match p s with
  | none         => none
  | some (a, s') => f a s'

instance : Monad Parser where
  pure := @pure
  bind := @bind
  map  := fun f p => fun s => match p s with | none => none | some (a, s') => some (f a, s')

/-- Choice combinator: try p1, if it fails, try p2. -/
def orElse {α} (p1 p2 : Parser α) : Parser α := fun s =>
  match p1 s with
  | some res => some res
  | none     => p2 s

infix:1 "<|>" => orElse

/-- Parser that consumes zero or more occurrences of `p`. -/
unsafe def many {α} (p : Parser α) : Parser (List α) := fun s =>
  let rec go (input : String) (acc : List α) : Option (List α × String) :=
    match p input with
    | some (a, rest) => go rest (acc ++ [a])
    | none           => some (acc, input)
  go s []

/-- Parser for a natural number (one or more digits). -/
unsafe def nat : Parser Nat :=
  many digit >>= fun cs =>
  if cs.isEmpty then failure else
  let n := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
  pure n

/-- Parser for whitespace. -/
unsafe def space : Parser Unit := many (satisfy Char.isWhitespace) >>= fun _ => pure ()

/-- Lexeme: parser p followed by optional whitespace. -/
unsafe def lexeme {α} (p : Parser α) : Parser α :=
  p >>= fun a => space >>= fun _ => pure a

/-- Parser for symbol string. -/
def symbol (str : String) : Parser String := fun s =>
  if s.startsWith str then some (str, s.drop str.length) else none

/-- Example: parse a list of comma-separated natural numbers. -/
unsafe def commaSepNat : Parser (List Nat) :=
  lexeme nat >>= fun n =>
  many (lexeme (char ',') >>= fun _ => lexeme nat) >>= fun ns =>
  pure (n :: ns)

/-! ### Examples -/

#eval run digit "123"                    -- some ('1', "23")
#eval run (char 'a') "abc"               -- some ('a', "bc")
#eval run nat "456xyz"                  -- some (456, "xyz")
#eval run (lexeme nat) "  78 "           -- some (78, "")
#eval run commaSepNat "1,2,  3,4"       -- some ([1,2,3,4], "")

end ParserCombinators
