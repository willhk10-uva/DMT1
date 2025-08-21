/-!
Profunctors are abstractions that generalize functions by allowing transformations
on both input (contravariant) and output (covariant) positions. They underpin optics
and bidirectional computations.

Key operations:
- `dimap f g` applies `f` before and `g` after a profunctor.
- `lmap f` applies `f` to inputs only.
- `rmap g` applies `g` to outputs only.

Laws for all `p : Profunctor`:
1. `dimap id id = id`
2. `dimap (f ∘ h) (i ∘ g) = dimap h i ∘ dimap f g`
-/

namespace Profunctor

/-- Profunctor class: `p α β` supports bidirectional mapping. -/
class Profunctor (p : Type → Type → Type) where
  /-- `dimap f g` maps inputs contravariantly with `f` and outputs covariantly with `g`. -/
  dimap {α α' β β'} : (α' → α) → (β → β') → p α β → p α' β'

/-- Map only the input of a profunctor. -/
def lmap {p : Type → Type → Type} [Profunctor p] {α α' β}
  (f : α' → α) (pab : p α β) : p α' β :=
  Profunctor.dimap f id pab

/-- Map only the output of a profunctor. -/
def rmap {p : Type → Type → Type} [Profunctor p] {α β β'}
  (g : β → β') (pab : p α β) : p α β' :=
  Profunctor.dimap id g pab

/-- The function arrow is a Profunctor instance. -/
instance : Profunctor (· → ·) where
  dimap f g h := g ∘ h ∘ f

end Profunctor

open Profunctor

/-! ### Utilities for Examples -/

/-- Specialized `dimap` for functions to simplify examples. -/
def dimapFun {α α' β β'} (f : α' → α) (g : β → β') (h : α → β) : α' → β' :=
  g ∘ h ∘ f

/-! ### Examples -/

/-- Example 1: Shift input by +1, subtract 3, then multiply result by 2. -/
def example1 : Nat → Nat :=
  dimapFun (fun x => x + 1) (fun y => y * 2) (fun z => z - 3)

#eval example1 5  -- 6

/-- Example 2: Prepend "hello " to input; leave output unchanged. -/
def example2 : String → String :=
  dimapFun (fun s => "hello " ++ s) id id

#eval example2 "world"  -- "hello world"

/-- Example 3: Add 42 then convert to string. -/
def example3 : Nat → String :=
  dimapFun id (fun n => "Result: " ++ toString n) (fun x => x + 42)

#eval example3 8  -- "Result: 50"
