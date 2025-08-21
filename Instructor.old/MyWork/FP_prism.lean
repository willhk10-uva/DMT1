/-!
Prisms are optics that focus on one branch of a sum type, allowing safe matching and construction.

Key concepts:
1. **Preview**: Attempt to extract a part of a variant, returning `Option`.
2. **Review**: Construct a whole from a part.
3. **Composition**: Combine prisms to focus deeper into nested sums.

Prism laws (for a lawful prism `pr` with types `S` → `Option A` and `A` → `S`):
- **Preview-Review**: `preview pr (review pr a) = some a`
- **Review-Preview**: If `preview pr s = some a`, then `review pr a = s`
- **Set-Set**: Reapplying review doesn’t change result
-/

namespace Prism

/-- A monomorphic prism focusing on variant `A` within sum `S`. -/
structure Prism (S A : Type) where
  preview : S → Option A
  review  : A → S

/-- Attempt to extract the `A` part of `s`. -/
def preview {S A} (pr : Prism S A) (s : S) : Option A :=
  pr.preview s

/-- Build an `S` from the `A` part. -/
def review {S A} (pr : Prism S A) (a : A) : S :=
  pr.review a

/-- Match `s`, applying `f` when extraction succeeds, else `none`. -/
def match? {S A B} (pr : Prism S A) (f : A → B) (s : S) : Option B :=
  match pr.preview s with
  | some a => some (f a)
  | none   => none

/-- Compose two prisms: first from `S` to `A`, then `A` to `B`. -/
def compose {S A B} (outer : Prism S A) (inner : Prism A B) : Prism S B :=
  { preview := fun s => outer.preview s >>= inner.preview,
    review  := fun b => outer.review (inner.review b) }

end Prism

open Prism

/-! ### Examples -/

/-- Color sum type with `BEq` and `Repr`. -/
inductive Color where
  | red
  | green
  | blue
deriving Repr, BEq

/-- Prism focusing on the `red` case of `Color`. -/
def prismRed : Prism Color Unit :=
  { preview := fun c => if c == Color.red then some () else none,
    review  := fun _ => Color.red }

/-- Prism focusing on the `green` case of `Color`. -/
def prismGreen : Prism Color Unit :=
  { preview := fun c => if c == Color.green then some () else none,
    review  := fun _ => Color.green }

-- Preview examples
#eval preview prismRed Color.red    -- some ()
#eval preview prismRed Color.blue   -- none

-- Review examples
#eval review prismRed ()           -- Color.red
#eval review prismGreen ()         -- Color.green

/-- Shape sum type with `BEq` and `Repr`. -/
inductive Shape where
  | circle : Nat → Shape
  | rect   : Nat → Nat → Shape
deriving Repr, BEq

/-- Prism for `circle` constructor. -/
def prismCircle : Prism Shape Nat :=
  { preview := fun s =>
      match s with
      | Shape.circle r => some r
      | _              => none,
    review  := Shape.circle }

/-- Prism for `rect` constructor yielding a pair. -/
def prismRect : Prism Shape (Nat × Nat) :=
  { preview := fun s =>
      match s with
      | Shape.rect w h => some (w, h)
      | _              => none,
    review  := fun (w, h) => Shape.rect w h }

/-- Prism focusing on rectangle width, ignoring height. -/
def prismRectWidth : Prism Shape Nat :=
  compose prismRect
          { preview := fun (w, _) => some w,
            review  := fun w => (w, 0) }

-- Preview composed prism
#eval preview prismRectWidth (Shape.rect 5 10)  -- some 5
#eval preview prismRectWidth (Shape.circle 7)   -- none

-- Construct shapes via review
#eval review prismCircle 3   -- Shape.circle 3
#eval review prismRect (4,6) -- Shape.rect 4 6
