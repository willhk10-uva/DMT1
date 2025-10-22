/- def(a fn called apply0 assumed alpha: Type (implicit) f: alpha → alpha
return value of f applied 0 times to its argument-/

def zero {α : Type}: (α → α) → α → α
| f, a => a

#check zero

def two {α : Type} : (α → α) → (a : α) → α
| f, a => f (f a)

def three {α : Type} : (α → α) → (a : α) → α
| f, a => f (f (f a))

def four {α : Type} : (α → α) → (a : α) → α
| f, a => f ( f (f (f a)))

def inc (n : Nat) := n + 1

def whatIsThis := ((@three Nat) ∘ (@four Nat))

#reduce whatIsThis
#eval two inc 8
#eval two inc 10

#check three
#check @three Nat

#eval three inc (two inc 0)

#reduce ((@two Nat inc) ∘ (@three Nat inc))

#eval three inc (four inc 2)

theorem refl {P : Prop}: P → P := (fun p=> p)
