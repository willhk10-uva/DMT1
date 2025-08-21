/-!
Lenses are composable getters and setters that focus on a part of a data structure,
enabling functional updates without mutation.

Key concepts:
1. **Getter**: Extract a subpart from a structure.
2. **Setter**: Produce an updated structure given a new subpart.
3. **Composition**: Combine lenses to focus deeply nested fields.

Laws for a lawful lens (`get` and `set`):
- **Get-Set**: `set s (get s) = s`
- **Set-Get**: `get (set s a) = a`
- **Set-Set**: `set (set s a₁) a₂ = set s a₂`
-/

namespace Lens

/-- A monomorphic lens focusing on a part of type `A` within `S`. -/
structure Lens (S A : Type) where
  get : S → A
  set : S → A → S

/-- View through a lens. -/
def view {S A : Type} (ln : Lens S A) (s : S) : A :=
  ln.get s

/-- Update through a lens. -/
def set {S A : Type} (ln : Lens S A) (s : S) (a : A) : S :=
  ln.set s a

/-- Modify a target by applying `f` through the lens. -/
def over {S A : Type} (ln : Lens S A) (f : A → A) (s : S) : S :=
  let a := ln.get s
  ln.set s (f a)

/-- Compose two lenses: first focus `A` in `S`, then `B` in `A`. -/
def compose {S A B : Type} (outer : Lens S A) (inner : Lens A B) : Lens S B :=
  { get := fun s => inner.get (outer.get s),
    set := fun s b => outer.set s (inner.set (outer.get s) b) }

end Lens

open Lens

/-! ### Examples -/

-- A simple record type
structure Person where
  name : String
  age  : Nat
deriving Repr

/-- Lens focusing on the `name` field of `Person`. -/
def nameLens : Lens Person String :=
  { get := fun p => p.name,
    set := fun p n => { p with name := n } }

/-- Lens focusing on the `age` field of `Person`. -/
def ageLens : Lens Person Nat :=
  { get := fun p => p.age,
    set := fun p a => { p with age := a } }

-- Example person
def alice : Person := { name := "Alice", age := 30 }

-- Viewing fields
#eval view nameLens alice   -- "Alice"
#eval view ageLens alice    -- 30

-- Setting fields
def alice2 := set nameLens alice "Alicia"
#eval view nameLens alice2  -- "Alicia"

def alice3 := over ageLens (· + 1) alice
#eval view ageLens alice3   -- 31

-- Nested record example
structure Company where
  ceo : Person
  name : String
deriving Repr

def company : Company := { ceo := alice, name := "Acme" }

/-- Lens for the `ceo` field of `Company`. -/
def ceoLens : Lens Company Person :=
  { get := fun c => c.ceo,
    set := fun c p => { c with ceo := p } }

-- Compose lenses to focus on CEO's age
def ceoAgeLens : Lens Company Nat :=
  compose ceoLens ageLens

#eval view ceoAgeLens company           -- 30

def updated := over ceoAgeLens (· + 5) company
#eval view ceoAgeLens updated           -- 35
#eval updated                           -- Company.mk { ceo := Person.mk { name := "Alice", age := 35 }, name := "Acme" }
