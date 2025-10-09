/- @@@
# Negation (¬)

## Big Idea from Last Time

- one pigeon is no holes is impossible (pigeonhole principle)
- (P → Empty), (P → False) uninhabited unless P is uninhabited
- So if (P → Empty), (P → False), then P must be uninhabited
- In Type uninhabited means empty. In Prop is means false.
- Empty : Type and False : Prop are given uninhabited types

## New Idea: Not (¬)

- Suppose α and P are uninhabited types / propositions
  - { α : Type } (pEmpty : α → Empty)
  - { P : Prop } (pFalse : P → Prop)
@@@ -/

axiom α : Type
axiom P : Prop

/- @@@
### Optional Side-Note

- Type is Type 0 is Sort 1
- Prop is Sort 0

You can generalize with `Sort u`
@@@ -/



/- @@@
### Negation Introduction

#### Logical case
  - Knowing that P is uninhabited
  - Means knowing there is no proof of it
  - Means knowing for sure that it's false
  - Now we'd like to say *Not p* is true
  - A perfect proof: *pFalse : P → False*
  - We *define* *(Not P)* to be *P → False*
@@@ -/

#check (Not)      -- Not (a : Prop) : Prop
-- def Not (a : Prop) : Prop := a → False

/- @@@

Just as *∧ : Prop → Prop → Prop* is notation
for *And _ _*, mathematics and logic use the
unary prefix notation, ¬P, to mean (Not P),
which, in turn, means *P → False*. These are
all the same proposition.
@@@ -/

#reduce (types := true) ¬P
#reduce (types := true) Not P
-- P → False


/- @@@
We cannot overemphasize the importance of very
quickly learning to translate between *¬P* and
*P → False* as meaning exactly the same thing.
In particular, a proof of *¬P* is a *function*
(of type P → False).

What does this mean? Suppose you have your own
uninhabited logical type (proposition), *Wrong,*
with no proofs. What interesting new proposition
should we be able to prove about *Wrong*?
@@@ -/

-- Exercise!

/- @@@
@@@ -/

def foo {P : Prop} {α : Type} : (P → false) → P → α := /- If I assume P is any proposition and alpha is any type of object, and you have a proof that p is false and you have a proof of p, then you have a contradiction-/
(
  fun pf=>
  (
    fun (p : P) => nomatch (pf p)

  )
)

def bar {P : Prop} {α : Type} : ¬P → P → α
| np, p => nomatch (np p)


def noContra {P : Prop} : ¬(P ∧ ¬P)
| h =>
(
  let p := h.left
  let np := h.right
  nomatch (np p)
)

def noContra' {P : Prop} : ¬(P ∧ ¬P)
| h => nomatch h

/-theorem proqValid{P : Prop} : P ∨ ¬P :=
_ -/
/- unprovable without stronger assumptions-/

theorem notDistribOverAnd {P Q: Prop} : ¬(P ∧ Q) → (¬P∨¬Q)
| h => (Or.inl (fun (p : P) => _))

theorem notDistribOverAnd' {P Q: Prop} : (¬P∨Q) → ¬(P ∧ Q)
| (Or.inl np) => _
| (or.inr np) => _
