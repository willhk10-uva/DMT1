/-!
Smart constructors are helper functions that enforce invariants when creating values of a data type,
ensuring that all constructed instances are valid by construction.

Key benefits:
1. **Encapsulation of invariants**: Prevent illegal states by hiding raw constructors.
2. **Improved readability**: Provide descriptive names for common construction patterns.
3. **Safe evolution**: Change underlying representation without breaking client code.

This Lean 4 file demonstrates smart constructors for a simple `NonEmptyList` type and a
`Percentage` type constrained to the range [0,100].
-/

/-! ### NonEmptyList: a list guaranteed to be non-empty -/
inductive NonEmptyList (α : Type) where
  | single : α → NonEmptyList α
  | cons   : α → NonEmptyList α → NonEmptyList α

/-- Provide a `Repr` instance for `NonEmptyList` when `α` itself is `Repr`. -/
instance {α : Type} [Repr α] : Repr (NonEmptyList α) where
  reprPrec
    | NonEmptyList.single a   => "[" ++ repr a ++ "]"
    | NonEmptyList.cons a tl  => repr a ++ " :: " ++ repr tl

namespace NonEmptyList

/-- `head` of a non-empty list. -/
def head {α : Type} : NonEmptyList α → α
  | single a   => a
  | cons a _   => a

/-- Smart constructor: build a list requiring at least one element. -/
def mk {α : Type} (hd : α) (tl : List α) : NonEmptyList α :=
  tl.foldr cons (single hd)

/-- Convert to a regular `List`. -/
def toList {α : Type} : NonEmptyList α → List α
  | single a   => [a]
  | cons a xs  => a :: toList xs

/-- Example usage: -/
def exampleNEL : NonEmptyList Nat :=
  mk 1 [2,3,4]

#eval repr (toList exampleNEL)  -- "[1, 2, 3, 4]"

end NonEmptyList

/-! ### Percentage: a wrapper for [0,100] -/
structure Percentage where
  value    : Nat
  /-- Invariant: 0 ≤ value ≤ 100 -/
  property : value ≤ 100

/-- Provide a default instance to satisfy general type class requirements. -/
instance : Inhabited Percentage where
  default := ⟨0, by simp⟩

namespace Percentage

/-- Smart constructor: safely create a `Percentage`, returning `Option`. -/
def mk? (n : Nat) : Option Percentage :=
  if h : n ≤ 100 then
    some ⟨n, h⟩
  else
    none

/-- Unsafe constructor: panics if out of bounds. -/
def mk! (n : Nat) : Percentage :=
  match mk? n with
  | some p => p
  | none   => panic! s!"Percentage out of range: {n}"

/-- Example valid and invalid constructions. -/
def valid : Option Percentage := mk? 75
#eval valid

def invalid : Option Percentage := mk? 150
#eval invalid

-- Using `mk!` will throw at runtime
#eval (mk! 25).value  -- 25
-- #eval (mk! 150).value  -- Panic!

end Percentage
