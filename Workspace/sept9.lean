axiom P : Prop
axiom Q : Prop
#check P → Q

def aProp (x:Nat) (h : x = 1): (x+1) = 2 :=
by
  rw [h]

def aProp' (x:Nat) : (x = 1) → (x+1 = 2) :=
  fun (h : x = 1) => by
    rw [h]

#check (aProp)
#check (aProp')

axiom x : Nat
axiom h : x = 1

#check aProp x h
#check aProp' x h

#check True
#check True

def timpt : True → True :=
  fun (t : True) => t

#check False
#check (_ : False)

def timpf : True → False :=
  fun (t : True) => _

def fimpt : False → True :=
  fun(h : False)  => True.intro

def fimpt' : False → True :=
  fun(h : False)  => False.elim h
