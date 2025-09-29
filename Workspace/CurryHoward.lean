#check And
#check Prod


namespace MyAnd
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

axiom P : Prop
axiom Q : Prop

def aProof : And P Q := _
#check And.left aProof
#check And.right aProof
end MyAnd


namespace MyProd
structure Prod (α : Type u) (β  : Type v) where
  mk ::
  fst : α
  snd : β

#check (Prod)
#check Prod Bool String
def aProd : Prod Bool String := Prod.mk true "I love lean!"
#eval aProd
#check Prod.mk

#eval Prod.fst aProd
#eval Prod.snd aProd
end MyProd

namespace MyFuncs
def S : Type := String
def T : Type := Bool

#check S → T

def aFunc: String → Bool :=
  fun (s: String) => False

def aFunc2: (String → Bool) :=
  fun (s: String) => True

#check ∀ (s: S), T
def aFunc3: ∀ (s: String), T :=

end MyFuncs

namespace MyDr
inductive Or(a b : Prop) : Prop where
| inl (h : a) : Or a b
| inr (h : b) : Or a b

def zeroEqZero : 0 = 0 := by rfl
end MyDr


theorem aThm : 0 = 0 ∨ 1 = 0 :=
  let pfZeZ : 0 = 0 := rfl
  Or.inl pfZeZ
