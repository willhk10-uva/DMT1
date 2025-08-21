import Init.Data.Repr
import Mathlib.Data.Rat.Defs

import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.Algebra.Module.Pi

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.List.ToFinsupp


/- @@@
<!-- toc -->

## Function Spaces

In the last chapter we represented α n-tuplies as functions of type
*Fin n → α*. We then defined addition, multiplication, and other such
on them, mainly by lifting the corresponding operations on the elements
by pointwise application to corresponding elements. We then established
additional structures on this space of functions, showing, e.g., that it
forms an additive commutative group.

Lean provides a second function space, from index to indexed values, that
is also useful for representing polymorphic tuples. The big difference is
that the index set is no longer *Fin n* by any type, making this space more
general. Furthermore, the index type need no longer even be finite. However,
there's one significant constraint: the function can be defined on no more
than a finite number of inputs.  Such a function is said to have *finite
support*. (We won't think hard about this part here.) The name of the type
is thus explained: *Finsupp*.

## Finsupp (ι →₀ α)

Quoting mathlib: Finsupp α M, denoted α →₀ M, is the type of
functions f : α → M such that f x = 0 for all but finitely many x.

```lean
structure Finsupp
  (α : Type*)                     -- index type (could be Fin n)
  (M : Type*) [Zero M] where      -- result (tuple element) type
  support : Finset α              -- the support
  toFun : α → M                   -- the function
                                  -- and proof of finite support
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0
```
@@@ -/

open Finsupp
#check Finsupp (Fin 3 → Nat)      -- Fin 3 is fine as an index set
#check Finsupp (Nat → Nat)        -- Nat → Nat with finite support

/- @@@
There are benefits for us in using *Finsupp* instead of just *Fin n → α*.
There are also downsides. Proofs can be more ponderous with *Finsupp*, for
example. An important benefit is that mathlib already provides not only the
usual algebraic operations but also group and other structures on values of
this type. So we don't have to! A second benefit is that one can get bases
for vector spaces for free.
@@@ -/

def f : Nat →₀ ℚ := List.toFinsupp [(1/2 : ℚ), 1/4, 1/6]
def g : Nat →₀ ℚ := List.toFinsupp [(1/3 : ℚ), 1/5, 1/7]
#check f + g
#check 3 • (f + g)



/- @@@
TUPLE
@@@ -/

#reduce (inferInstance : AddCommGroup (Nat →₀ ℚ))
-- #reduce (inferInstance : Module ℚ (Nat →₀ ℚ))

structure Tuple (α : Type u) (n : Nat) [Zero α] where
  toFun : Fin n →₀ α

instance [Zero α] : CoeFun (Tuple α n) (fun _ => Fin n → α) where
  coe v := v.toFun

instance [Add α] [Zero α] [DecidableEq (Fin n)] : Add (Tuple α n) where
  add x y := ⟨Add.add x.toFun y.toFun⟩


instance [Add α] [Zero α] : Add (Tuple α n) where
  add x y := ⟨ (x.toFun + y.toFun) ⟩  -- ⟨x.toFun + y.toFun⟩




  open Finsupp

instance [Add α] [Zero α] : Add (Tuple α n) where
  add x y := ⟨x.toFun + y.toFun⟩

instance [Zero α] : Zero (Tuple α n) where
  zero := ⟨0⟩

instance [Neg α] [Zero α] : Neg (Tuple α n) where
  neg x := ⟨-x.toFun⟩

instance [AddCommGroup α] : AddCommGroup (Tuple α n) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul n x := ⟨n • x.toFun⟩
  zsmul n x := ⟨n • x.toFun⟩
  add_assoc := by intros; apply Subtype.ext; simp [add_assoc]
  zero_add := by intros; apply Subtype.ext; simp
  add_zero := by intros; apply Subtype.ext; simp
  add_comm := by intros; apply Subtype.ext; simp
  add_left_neg := by intros; apply Subtype.ext; simp


example (t : Tuple ℚ 3) : t + t



-- #reduce (inferInstance : Module ℚ (Nat →₀ ℚ))




structure Vc (α : Type u) (n : Nat) where
  val : Tuple α n

instance : CoeFun (Vc α n) (fun _ => Tuple α n) where
  coe v := v.val

#reduce (inferInstance : AddCommGroup (Nat →₀ ℚ))



instance [Zero α]: CoeFun (Vc α n) (fun _ => α →₀ ℚ) where
  coe v := v.val

#check f
def F :

#reduce (inferInstance : Module ℚ (Nat →₀ ℚ))

instance (α : Type u) [Ring α] : Module α (Nat →₀ α) :=
{
  smul := _
  one_smul := _
  smul_zero := _
  smul_add := _
  add_smul := _
  zero_smul := _
  mul_smul := _
}
