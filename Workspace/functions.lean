def myAdd : Nat → Nat → Nat :=
  fun n1 n2 : Nat => n1 + n2

#eval myAdd 3 5

def myAdd' (n1 n2 : Nat) : Nat :=
  n1 + n2

def myAdd''' : (n1 : Nat) → (n2 : Nat) → Nat :=
  fun n1 n2 => n1 + n2

def notMyAdd : Nat → Nat → Nat :=
  fun n1 n2 => n1 + n2

def add1 : Nat → Nat := myAdd 1
#check add1
#eval add1 5
#eval add1 5

def add10 : Nat → Nat := myAdd 10
#eval add10 5
#eval add10 15

def ifThenElse : Bool → Bool → Bool → Bool
| b1, b2, b3 => if b1 then b2 else b3

#eval ifThenElse true false true
#eval ifThenElse false false true

#check ifThenElse

def newAdd : Nat → Nat → Nat := fun n1 n2 => n1 + n2
def newAdd' := fun (n1 : Nat) n2 => n1 + n2
def weird (alpha : Type) (a : alpha) : Bool := true
def strange {alpha : Type} (a : alpha) : Bool := true

#check newAdd
#check newAdd'

#eval weird String "i am a string"
#eval weird Nat 42
#eval weird Bool false


#eval strange 3
#eval strange "Hi there"
#eval strange false

def myNeg (b : Bool) : Bool :=
match b with
| true => false
| false => false

#check myNeg
#check Or
