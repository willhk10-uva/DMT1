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

open Dool

def neg : Dool → Dool
| troo => felse
| felse => troo


inductive myNat : Type where
| zero : myNat
| succ (n : myNat) : myNat

open myNat
def three : myNat := succ ( succ (succ zero))

end foo

def myNeg : Bool → Bool
| true => false
| false => true

#check Unit

def unitToUnit : Unit → Unit  := fun u => u

inductive Lonely where

#check Empty

def et2 (α : Type) : Empty → α :=
  fun e : Empty => nomatch e

#check False

def ftp (P : Prop) : False → p :=
  fun e : False => nomatch e

def exfalso ( P : Prop) : False → P :=
  fun e : False => nomatch e

#check Not

def etb : Empty → Empty := fun u => nomatch u
