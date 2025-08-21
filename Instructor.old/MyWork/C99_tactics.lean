/- @@@
The Lean libraries already overload dozes of typeclasses
to establish abstract algebraic properties of the rational
numbers. For example, the libraries already caontain a
statement and proof that addition of rationals, defined
as usual, is associative. You can use Lean search engines
to ease the process of finding general-purpose proofs of
this sort: basic mathematical results.
@@@ -/

#check Rat.add_assoc

/- @@@

### Properties of 1-D Rational Vectors

With all that in mind, now we'll build monoid, grup, and
eventually vector space structures around our Vc type.

#### Addition Operation
@@@ -/


def addVc (v1 v2 : Vc) : Vc := Vc.mk (v1.val + v2.val)
instance : Add Vc := { add := addVc}

/- @@@
@@@ -/
def zeroVc := Vc.mk 0
instance : OfNat Vc 0 where ofNat := Vc.mk 0  -- notation-providing typeclass
instance : Zero Vc := { zero := 0 }

/- @@@
@@@ -/
theorem zeroAddVc : ∀ (a : Vc), (0 : Vc) + a = a :=
by
  intro a
  apply congrArg Vc.mk
  simp
  rfl

/- @@@
@@@ -/
theorem addZeroVc : ∀ (a : Vc), a + 0 = a :=
by
  intro a
  apply congrArg Vc.mk
  simp
  rfl

/- @@@
@@@ -/
instance : AddZeroClass Vc :=
{
  zero_add := zeroAddVc
  add_zero := addZeroVc
}


/- @@@
#### Inverse Operation
@@@ -/
def invVc (v : Vc) := Vc.mk (-v.val)

/- @@@
#### Scalar Multiplication by Nat
@@@ -/
def nsmulVc (s : Nat) (v : Vc ) := Vc.mk (s * v.val)


/- @@@
Remember, here you prove the generalized addition-is-associative
theorem as a specalization of the generalized definition to your
particular type.
@@@ -/
theorem addAssocVc : ∀ (v1 v2 v3: Vc),
  (v1 + v2) + v3 = v1 + (Add.add v2 v3) :=
by
  /- @@@
  Suppose v1, v2, and v3 are vectors (values of type Vc).
  What we'll have to show is *(v1 + v2) + v3 = v1 + (v2 + v3)*.
  @@@ -/
  intro v1 v2 v3

  /- @@@
  Now observe that each *v* must be of the form, *Vc.mk q*,
  where *q* is the rational value from which the vector was
  constructed. By the *substitutability of equals* (axiom) of
  equality, we can rewrite each *v* as *Vc.mk q* (with its
  own value of *q*). Under this rewriting the goal becomes
  to (v1 + v2).val = v1.val + (v2 + v3).val. The rewriting
  applies to the top-level terms.

  What this subsitution does is expose the rational number
  representations of the *Vc* arguments.. We're rewriting
  the values in their destructured forms to expose their
  representations *to Lean*.
  @@@ -/
  apply congrArg Vc.mk

  /- @@@
  At this point, Lean can satisfy the goal with Rat.add_assoc
  @@@ -/
  apply Rat.add_assoc
