import Mathlib.Algebra.Field.Defs
import Batteries.Data.Rat.Basic
import Batteries.Data.Rat.Lemmas

abbrev K := ℚ



instance : MulOneClass K :=
{
  -- ∀ (a : ℚ), 1 * a = a
  one_mul := by
    intro a
    exact Rat.one_mul a

  mul_one := by sorry
}

/-
type mismatch
  Rat.one_mul a
has type
  @OfNat.ofNat ℚ 1 Rat.instOfNat * a = a : Prop
but is expected to have type
  @OfNat.ofNat ℚ 1 One.toOfNat1 * a = a : Prop
-/

-- -------CUTS--------

/-
A *ring* is a group under addition that also has a
multiplication operations. A ring might not be a group
under multiplication, for the lack of multiplicative
inverses. When a ring also has mutiplicative inverses,
it's a field.

The rationals (without 0) are grou under multiplication
as well as being a group under addition and so form a
field. A nice example of a ring that is not a field is
the set of univariate polynomials with real coefficients.
You can add them. You can negate (additively invert) them.
But the inverse of such a polynomial is in general not
a polynomial, but rather a *rational function*. You can,
in principle, define an affine space over a module with
polynomials as scalars that scale the vector-like module
elements!
-/

-- CUTS

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


-- ----------------

/- @@@
#### Lifting Equality Proofs Through Function Applications

In Lean, congrArg is a proof of the property of equality
that allows equalities between terms to be *lifted* through
arbitrary function applications. In other words, if *α* and
*β* are types, *f* is any function of type α → β, and *h*
proves *a = b* then *congrArgs h* proves *f a = f b*.

  ```lean
congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂
  ```

Congruence in the function argument: if a₁ = a₂ then f a₁ = f a₂ for any (nondependent) function f. This is more powerful than it might look at first, because you can also use a lambda expression for f to prove that <something containing a₁> = <something containing a₂>. This function is used internally by tactics like congr and simp to apply equalities inside subterms.


To prove *f a = f b* a proof of *a = b* will suffice.
The rule works for *any* function. For example,  with
*(a b : ℚ)*, suppose that I also have a proof, *h,* of
*a = b*. By the rule and using *h* we can deduce that
*Vc.mk a = Vc.mk b.*

In reverse, if we need a proof of *f a = f b* it will
suffice to apply *congrArg* to *h*. So to show that two
vectors, *v1* and *v2* are equal, where *v1 := Vc.mk q1*
and *v2 := Vc.mk q2*, it will suffice to show *q1 = q2*.
Applying any function *f* to two things that are equal
will produce results that are equal.

#### AddSemigroup Vc

Recall that a semigroup has carrier set and a binary
operation with the property of being associative.
@@@ -/

instance : AddSemigroup Vc :=
{
  add_assoc := addAssocVc
}

/- @@@
AddZeroClass M
@@@ -/

instance : AddZeroClass Vc :=
{
  zero_add := by
    intro a
    simp [addVc]

  add_zero := by
    intro a
    simp [addVc]
}

/- @@@
#### AddMonoid Vc
@@@ -/
instance : AddMonoid Vc :=
{
  nsmul := nsmulRec
}

/- @@@
#### AddCommSemigroup
@@@ -/
instance : AddCommSemigroup Vc :=
{
  add_comm := by
    intro v1 v2
    apply congrArg Vc.mk
    exact Rat.add_comm v1.val v2.val
}


/- @@@
#### AddCommMonoid
@@@ -/
instance : AddCommMonoid Vc := {}



/- @@@
#### Semiring Sc
@@@ -/

def addSc (s1 s2 : Sc) := Sc.mk (s1.val + s2.val)
instance : Add Sc := { add := addSc }

theorem add_assocSc : ∀ (s1 s2 s3 : Sc), (s1 + s2) + s3 = s1 + (s2 + s3) := by
  intro s1 s2 s3
  apply congrArg Sc.mk
  apply Rat.add_assoc


instance : Zero Sc := { zero := Sc.mk 0 }

instance : Semiring Sc :=
{
  add := addSc
  add_assoc := add_assocSc
  zero := Sc.mk (0 : ℚ)
  zero_add := by
    intro a
    apply congrArg Sc.mk
    simp [addSc]
    rfl

  add_zero := by
    intro a
    apply congrArg Sc.mk
    simp [addSc]
    rfl

  nsmul := nsmulRec

  add_comm := by
    intro a b
    apply congrArg Sc.mk
    apply Rat.add_comm

  mul := _
  left_distrib := _
  right_distrib := _
  zero_mul := _
  mul_zero := _
  mul_assoc := _
  one := _
  one_mul := _
  mul_one := _
}

instance : NonAssocSemiring Vc := sorry

instance : NonUnitalNonAssocSemiring Vc := sorry

instance :  AddCommMonoidWithOne Vc := sorry
instance : MulZeroOneClass Vc :=
{
   zero_mul := _
   mul_zero := _
}

instance :  NonUnitalNonAssocSemiring Vc := sorry

instance : SemigroupWithZero Vc := _

instance : NonUnitalSemiring Vc := sorry


instance : Module Sc Vc := _

------------------



/- @@@
A field is both a
groups under addition and (exluding the zero element) a group
under multiplication, where multiplication and addition follow
the usual distributive laws. The rational and the real numbers
are both groups.



Such a vector *v* acts on a point *p* by *translating* it.
You can visualize this action as putting the tail of some
vector, *v*, on a point, *p*, and then moving the point to
the head of the vector. The resulting point is *v +ᵥ p*.
The basic set-up is just as we've developed it so far,
but now actions are vectors in a vector space rather than
just rotations in a group of rotational symmetries.

The question this chapter answers is, so what's vector
space, and what are the consequences of changing the set
of actions from just a group to a vector space.

One consequence is that the torsor has to change to
accommodate all the possible actions. In our example, we
replaced *Rot* (a set of rotations) with the (infinite) 2-D
plane. That's necessary as a single point can be translated
to any other point in the plane by just choosing the right
vector (action) from the vector space to *send it there*.

A second big change is that the set of scalars used to
scale actions is no longer just the naturals or integers
but a *field*. A field comprises a carrier set of values
(think of real numbers) where these values are an abelian
(commutative) group under addition; and, with the additive
zero removed, an abelian group under multiplication; and
where the usual distributive laws relate these operations.

The fact that a field is group under multiplication means
that a field contains *multiplicative inverses* of all of
the elements. When the scalars that scale actions are from
a field, they can be fractions or reals: not only *2* or
*-2* but *1/2* or *π,* for example.

For example, in a *real* vector space we can multiply
(scale) a vector, which is to say a translation action,
by any real number, including *0.5*. When scalars vary
over the field of the real numbers, or rational numbers,
they can send a single point to *anywhere* on the real
(or rational) 2-D plane.

A torsor acted upon but such actions has to have enough
points in it to represent the destinations of all those
of the tensor and group laws. The set of points of the 2-D
vector actions under all the prevailing constraints. The
real or rational plane of points is thus structured, as
a torsor, by the structure of the group of differences,
which, for this torsor, with its definition of *-ᵥ* (the
vector-valued difference of two points), is a vector space.

In this chapter, we will establish formally that the set
of 2-D points with rational coefficients forms a torsor
with an associated vector space of everydat 2-D vectors.
We'll parameterize our library by (i.e., generalize over)
the scalar field. We'll use ℚ (the rationals) in examples,
as they are computable so we will be able to run and use
our code.


As we've already seen, the Lean libraries decompose the
definitions of structures, such as fields, into multiple
parts, specified by separate typeclasses, each defining
some required additional element of structure (additional
fields) around one or more types. Some of the typeclasses
in such a hierarchy correspond to abstractions commonly
taught in upper division, or early graduate, mathematics.
Others are less fundamental and can be read as artifacts
that could have been different but that serve to support
the structuring of mathlib under the constraints of type
theory and Lean 4.

The rest of this chapter starts with a concrete example
to be developed. Following that, we traverse the hierarchy
of typeclasses for which we need instances to establish a
pair of types, *G* and *P*, as a vector space, with *G* with an aim to specify
real or rational n-tuples comes its development down through
the graph of typeclasses that need to be instianted in
general to fully specify a mathematical structure on a
given type or tuple of types.

## Running Example:

We are going to construct a rational affine 2-space. This
is a set of points, each represented as a pair of rational
numbers, with a corresponding set of vectors, represented
in the same way, with scalars being single rational numbers.
We could use real numbers here, but the resulting library
would not compute.
@@@ -/

-- Examples
def sc' : Rat := 1/2
def sc : ℚ := 1/2

/- @@@
Suppose we have points, p = (1/2, 1/2), and q = (3/2,/3/2).
We'll define q -ᵥ p = (3/2 - 1/2, 3/2 - 1/2) = (1/1, 1/1), with
with point-point subtraction yielding the vector, v = (1, 1).
Next the vector-point addition v +ᵥ p will be (1/2+1, 1/2+1).
We also have scaling, with *a • (x, y) defined as (a • x, a • y).
However, whereas before we had no fractional scalars, now we
do, so we also have fractions of actions, e.g., *w = 1/2 • v*.
@@@ -/

abbrev Scalar := ℚ



/- @@@
### Scalar Tuples

As we see in the preceding informal example, we're
going to need to represent scalar *tuples*, here ordered
pairs, as we're using such tuples to represent values of
both point and vector type objects.

One way to think about a tuple, such as an ordered pair,
is as a mapping from positional indices (such as 0 or 1
for an ordered pair) to the values at those positions in
any given pair. Such a function maps from an index set, in
this case the set {0, 1}, to values, defining an order
on them.

```lean
structure Fin (n : Nat) where
  val : Nat
  isLt : val < n
```
@@@ -/

abbrev Tuple (α : Type) (n : Nat) := Fin n → α



/- @@@
We can now represent rational ℚ-tuples formally.
And what we'll want the following examples of tuples
to represent in turn are two *points* in a flat plane.
@@@ -/

-- The point (1/2, 1/2)
def p : Fin 2 → ℚ
| 0 => 1/2
| 1 => 1/2

-- the point (3/2, 3/2)
def q : Tuple Scalar 2
| 0 => 3/2
| 1 => 3/2

/- @@@
We can add points like this element-wise, but while we're
at it, we might as well generalize to arbitrary dimensions
and to arbitrary element types, provided addition is defined.
@@@ -/

def tupleAdd
    {α : Type}          -- any element type
    [Add α]             -- for which addition is defined
    {n : Nat}           -- and any dimension
    (a b : Fin n → α) : -- given any two tuples
    Fin n → α :=        -- return the the tuple
  fun i => a i + b i    -- of element wise sums

/- @@@
Inverse of tuple is similar
@@@ -/

def tupleInv
    {α : Type}          -- any element type
    [Neg α]             -- for which addition is defined
    {n : Nat}           -- and any dimension
    (a : Fin n → α) :   -- given any tuple
    Fin n → α :=        -- return the the tuple of
  fun i => -(a i)       -- element wise inverses


/- @@@
Here's an overload of toString for our tuple type
@@@ -/
instance {α : Type} [ToString α] {n : Nat} : ToString (Tuple α n) where
  toString f :=
    let elems := List.ofFn f |>.map toString
    "(" ++ String.intercalate ", " elems ++ ")"

#eval toString p
#eval toString q


/- @@@
Note: You can initialize a value of type Fin n with
any natural number, m, in which case the result will
be Fin m % n. Here, for example, we see in the example
that follows that *4* typed as an element of Fin 3 is
read as being (1 : Fin 3).
 -/
example : (4 : Fin 3) = (1 : Fin 3) := rfl


/- @@@
## Ring

A ring *(R, +, ⋅)* consists of a carrier set, *R*, with
both addition (+) and multiplication (*) operators. The
easiest ring to think about is the integers, where R = ℤ.
To be a ring, *R* must be a commutative (i.e., *abelian*)
group under *+*. That means associativity of *+*, a zero,
additive inverses, andcommutativity of *+*. *R* must be
only a semigroup under multiplication, which need only to
be associative. Finally, the usual distributive laws hold
(for a*(b+c) and (a+b)*c).

As an example, the set of natural numbers, ℕ, with the usual
addition and multiplication operators do *not* form a ring,
because the natural numbers is not a group under addition,
as there are no additive inverses in the natural numbers.

On the other hand, the integers, ℤ, does form a ring under
the usual addition and multiplication operators. First,
the integers forms a group under addition. Second, it is
a commutative group, as integer addition is commutative.
The integers also form a multiplicative semigroup, as the
integer multiplication operation is commutative. Finally,
the usual distributive laws for *+* and \* apply.

Two more examples of rings are the set of all polynomials,
*ℤ[x]*, in one variable, *x*, and with integer coefficients,
and the set of all n-by-n matrices with integer entries. You
should be able to confirm that these sets and operations do
satisfy the ring axioms.
@@@ -/

/- @@@
## Module
@@@ -/

/- @@@
## Field
@@@ -/

/- @@@
## Vector Space
@@@ -/




open Affine             -- AffineSpace = AddTorsor

#check AffineSpace

-- A commutative group has a commutative operator
#check AddCommGroup     -- AddGroup + AddCommMonoid
#check AddCommMonoid    -- AddMonoid + AddCommSemigroup
#check AddCommSemigroup -- AddSemigroup + AddCommMagma
#check AddCommMagma     -- Add + add commutativity law
/- @@@
```lean
class AddCommMagma (G : Type u) extends Add G where
  protected add_comm : ∀ a b : G, a + b = b + a
```
@@@ -/

/- @@@
@@@ -/


#check Field
#check Module                       -- Semiring R, AddCommMonoid M, DistribMulAction R M

#check Semiring                     -- NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
#check NonUnitalSemiring            -- NonUnitalNonAssocSemiring α, SemigroupWithZero α
#check NonAssocSemiring             -- NonUnitalNonAssocSemiring α, MulZeroOneClass α, AddCommMonoidWithOne α
#check SemigroupWithZero            -- Semigroup S₀, MulZeroClass S₀
#check NonUnitalNonAssocSemiring    -- AddCommMonoid α, Distrib α, MulZeroClass α
#check AddCommMonoidWithOne         -- AddMonoidWithOne + AddCommMonoid
#check Distrib                      -- Mul, Add, distributive laws
#check MulZeroClass                 -- Mul, Zero, mul by zero laws
#check AddCommMonoid                -- AddMonoid + AddCommSemigroup
#check AddMonoidWithOne             -- NatCast, AddMonoid, One
#check NatCast                      -- Mapping from Nat to given Type
#check Zero
#check One
#check MonoidWithZero               -- Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
#check MulZeroOneClass              -- MulOneClass M₀, MulZeroClass M₀

#check DistribMulAction             -- [Monoid M] [AddMonoid A] extends MulAction
#check MulAction                    -- Monoid, SMul, laws

#check AffineSpace

variable (𝕜 : Type*) [Field 𝕜]
variable (V : Type*) [AddCommGroup V] [Module 𝕜 V]
