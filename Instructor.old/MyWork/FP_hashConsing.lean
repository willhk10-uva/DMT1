/- ***
Hash-consing is a technique for ensuring that structurally equivalent data structures
share the same memory representation, typically using a hash table to store canonical
representatives of each unique structure.

The key benefits of hash-consing are:
1. **Memory efficiency**: Identical subexpressions are stored only once
2. **Fast equality checking**: Structural equality reduces to ID comparison
3. **Sharing preservation**: Complex expressions with common subterms automatically share memory

This implementation demonstrates hash-consing on a simple expression language, where
each unique expression gets assigned a canonical representative with a unique ID.
*** -/

-- Hash-consing implementation in Lean 4
-- This ensures that structurally equivalent terms share the same representation

import Std.Data.HashMap
import Std.Data.HashMap.Basic

-- A simple expression type for demonstration
inductive Expr where
  | var : String → Expr
  | const : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
deriving BEq, Hashable, Repr

-- Hash-consed expression with unique ID
structure HCExpr where
  id : Nat
  expr : Expr
deriving BEq, Repr

-- Hash-consing table state
structure HCState where
  table : Std.HashMap Expr HCExpr
  counter : Nat

-- Default empty state
def HCState.empty : HCState :=
  HCState.mk (Std.HashMap.emptyWithCapacity 16) 0

-- Hash-consing monad
abbrev HC := StateM HCState

-- Hash-cons an expression
def hashCons (e : Expr) : HC HCExpr := do
  let state ← get
  match state.table[e]? with
  | some hce => return hce
  | none =>
    let newId := state.counter
    let hce := HCExpr.mk newId e
    let newTable := state.table.insert e hce
    set (HCState.mk newTable (newId + 1))
    return hce

-- Helper function to create hash-consed expressions
def mkVar (name : String) : HC HCExpr := hashCons (Expr.var name)
def mkConst (n : Nat) : HC HCExpr := hashCons (Expr.const n)
def mkAdd (e1 e2 : HCExpr) : HC HCExpr := hashCons (Expr.add e1.expr e2.expr)
def mkMul (e1 e2 : HCExpr) : HC HCExpr := hashCons (Expr.mul e1.expr e2.expr)

-- Example 1: Basic hash-consing showing shared structure
def example1 : HC (HCExpr × HCExpr × HCExpr) := do
  let x ← mkVar "x"
  let y ← mkVar "y"
  let x_plus_y ← mkAdd x y
  let x_plus_y_again ← mkAdd x y  -- This should reuse the same HCExpr
  let different ← mkAdd y x       -- Different structure, new HCExpr
  return (x_plus_y, x_plus_y_again, different)

-- Run example1 and show results
def runExample1 : IO Unit := do
  let (result, finalState) := example1.run HCState.empty
  IO.println s!"Example 1 Results:"
  IO.println s!"First x+y ID: {result.1.id}"
  IO.println s!"Second x+y ID: {result.2.1.id}"
  IO.println s!"Different y+x ID: {result.2.2.id}"
  IO.println s!"Are first two the same? {result.1.id == result.2.1.id}"

#eval runExample1

-- Example 2: Complex expression with multiple shared subexpressions
def example2 : HC (HCExpr × HCExpr) := do
  let x ← mkVar "x"
  let two ← mkConst 2
  let three ← mkConst 3

  -- Build: 2 * x + 3 * x
  let two_x ← mkMul two x
  let three_x ← mkMul three x
  let expr1 ← mkAdd two_x three_x

  -- Build the same expression again: 2 * x + 3 * x
  let two_x_again ← mkMul two x    -- Should reuse existing 2 * x
  let three_x_again ← mkMul three x -- Should reuse existing 3 * x
  let expr2 ← mkAdd two_x_again three_x_again -- Should reuse existing result

  return (expr1, expr2)

-- Run example2 and show results
def runExample2 : IO Unit := do
  let (result, finalState) := example2.run HCState.empty
  IO.println s!"Example 2 Results:"
  IO.println s!"First expr ID: {result.1.id}"
  IO.println s!"Second expr ID: {result.2.id}"
  IO.println s!"Are they the same? {result.1.id == result.2.id}"

#eval runExample2

-- Utility to show the hash table contents
def showTable (state : HCState) : IO Unit := do
  IO.println "Hash table contents:"
  for (expr, hcexpr) in state.table.toList do
    IO.println s!"ID {hcexpr.id}: {repr expr}"

-- Demonstrate hash-consing with table inspection
def demonstrateHashConsing : IO Unit := do
  let (result, finalState) := example2.run HCState.empty
  IO.println s!"Result: First expr ID {result.1.id}, Second expr ID {result.2.id}"
  IO.println s!"Are they the same object? {result.1.id == result.2.id}"
  showTable finalState

#eval demonstrateHashConsing
