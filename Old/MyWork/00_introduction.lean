/- @@@
### Constants
-/

/- @@@
In first order theory we establish the meanings of
constant symbols outside of the syntax of the logic
per se. Typically one will say something like this,
assuming that the domain of discourse in these cases
is natural number arithmetic. Let *c* be the constant
with value one. Here it is in Lean 4.
@@@ -/

def c : Nat := 1


/- @@@
### Variables

In first order theory we might say, let N be a variable
ranging over the natural numbers. In Lean we'll use the
same trick as previously, but here we add the type of the
value to which a variable will be interpreted. Here then
in Lean is the same idea.
@@@ -/

-- The Var type need be defined only once
structure Var (α : Type) where
index : Nat

-- A variable expression
def n : Var Nat := Var.mk 0

/- @@@
Given an interpretation function from Var to Nat one
can now look up the value of such a variable under a
given interpretation.
@@@ -/

-- an interpretation, all variables bound to zero
def anInterp := λ varIndex: Var Nat => 0

#eval anInterp n    -- expect 0
