/-!
Tagless Final (or finally tagless) is a style of embedding domain-specific languages (DSLs)
without defining an explicit AST. Instead, you define an interface of operations (the DSL's syntax)
parametrized by a representation type `repr : Type → Type`.

Key benefits:
1. **Type safety**: Only well-typed terms can be expressed, as you never expose raw AST.
2. **Multiple interpretations**: Provide different instances of the interface to evaluate,
   pretty-print, optimize, or compile the same DSL program.
3. **Extensibility**: Add new operations by extending the interface, without changing existing code.

This example shows a simple arithmetic DSL with integer literals and addition.
-/

-- The DSL interface
class Symantics (repr : Type → Type) where
  lit : Int → repr Int
  add : repr Int → repr Int → repr Int

open Symantics

/-- Example DSL program: 1 + (2 + 3) -/
def example1 {R : Type → Type} [Symantics R] : R Int :=
  add (lit 1) (add (lit 2) (lit 3))

/-- Another example: (4 + 5) + 6 -/
def example2 {R : Type → Type} [Symantics R] : R Int :=
  add (add (lit 4) (lit 5)) (lit 6)

-- Interpretation 1: Evaluation to `Int` (as `Nat` under the hood)
instance evalSym : Symantics (fun α => α) where
  lit n   := n
  add x y := x + y

-- Interpretation 2: Pretty-printing to `String`
instance printSym : Symantics (fun α => String) where
  lit n   := toString n
  add x y := "(" ++ x ++ " + " ++ y ++ ")"

/-! ### Running the examples -/

#eval @example1 (fun α => α) evalSym      -- uses `evalSym`: yields 6
#eval @example1 (fun α => String) printSym -- uses `printSym`: yields "(1 + (2 + 3))"

#eval @example2 (fun α => α) evalSym      -- uses `evalSym`: yields 15
#eval @example2 (fun α => String) printSym -- uses `printSym`: yields "((4 + 5) + 6)"

/-!
To extend the DSL with multiplication, define:

class MulSym (repr : Type → Type) extends Symantics repr where
  mul : repr Int → repr Int → repr Int

and provide instances for `evalSym` and `printSym`, without touching `example1` and `example2`.
-/
