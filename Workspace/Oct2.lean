theorem por {P : Prop} : (P ∨ False) ↔ P :=
(
  Iff.intro /- takes two arguments-/
  (
    fun porf =>
    (
      match porf with
      | Or.inl p => p
      | Or.inr f => False.elim f
    )
  )
  (
    fun (p : P) => Or.inl p /- need to construct a proof of p or false-/
  )
)

axiom X : Prop
axiom Y : Prop

namespace foo

inductive Dool where
| troo
| felse

def neg : Dool → Dool
| troo => felse
| felse => troo
