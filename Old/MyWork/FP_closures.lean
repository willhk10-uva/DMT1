/- ***
Closures are functions that capture and "close over" variables from their surrounding
lexical scope, maintaining access to these variables even after the outer scope has
finished executing.

The key benefits of closures are:
1. **Lexical scoping**: Functions can access variables from their definition context
2. **State encapsulation**: Private state can be maintained across function calls
3. **Higher-order programming**: Enable powerful functional programming patterns like currying and partial application

This implementation demonstrates closures in a simple functional language, where
functions can capture free variables from their environment and maintain access
to them throughout their lifetime.
*** -/

-- Closure implementation in Lean 4
-- This demonstrates how functions can capture and maintain access to their lexical environment

import Std.Data.HashMap
import Std.Data.HashMap.Basic

-- Variable names
abbrev VarName := String

-- Forward declarations for mutual recursion
mutual
  -- Values in our language
  inductive Value where
    | int : Int → Value
    | bool : Bool → Value
    | closure : Closure → Value
  deriving Repr

  -- Expressions in our simple functional language
  inductive Expr where
    | var : VarName → Expr
    | lit : Value → Expr
    | lambda : VarName → Expr → Expr  -- λx. body
    | app : Expr → Expr → Expr        -- function application
    | let_ : VarName → Expr → Expr → Expr  -- let x = e1 in e2
    | add : Expr → Expr → Expr        -- arithmetic
    | if_ : Expr → Expr → Expr → Expr -- conditionals
  deriving Repr

  -- A closure captures a lambda expression and its defining environment
  structure Closure where
    param : VarName      -- parameter name
    body : Expr          -- function body
    env : List (VarName × Value)  -- captured environment as list for Repr
  deriving Repr
end

-- Environment mapping variable names to values
abbrev Env := Std.HashMap VarName Value

-- Helper to convert between Env and List representation
def envToList (env : Env) : List (VarName × Value) := env.toList
def listToEnv (list : List (VarName × Value)) : Env :=
  list.foldl (fun acc (name, value) => acc.insert name value) Std.HashMap.empty

-- Helper to create closure with HashMap env
def Closure.mk' (param : VarName) (body : Expr) (env : Env) : Closure :=
  Closure.mk param body (envToList env)

-- Evaluation monad with error handling
inductive EvalError where
  | unboundVar : VarName → EvalError
  | notAFunction : Value → EvalError
  | notAnInt : Value → EvalError
  | notABool : Value → EvalError
deriving Repr

abbrev EvalM := ExceptT EvalError Id

-- Helper to create empty environment
def Env.empty : Env := Std.HashMap.empty

-- Helper to extend environment
def Env.extend (env : Env) (name : VarName) (value : Value) : Env :=
  env.insert name value

-- Evaluate expressions to values with fuel to ensure termination
def eval (fuel : Nat) (env : Env) (expr : Expr) : EvalM Value :=
  match fuel with
  | 0 => throw (EvalError.unboundVar "recursion limit exceeded")
  | fuel + 1 =>
    match expr with
    | Expr.var name =>
      match env[name]? with
      | some value => pure value
      | none => throw (EvalError.unboundVar name)

    | Expr.lit value => pure value

    | Expr.lambda param body =>
      -- Create closure capturing current environment
      pure (Value.closure (Closure.mk' param body env))

    | Expr.app func arg => do
      let funcVal ← eval fuel env func
      let argVal ← eval fuel env arg
      match funcVal with
      | Value.closure closure =>
        -- Extend captured environment with argument binding
        let closureEnv := listToEnv closure.env
        let newEnv := closureEnv.extend closure.param argVal
        eval fuel newEnv closure.body
      | _ => throw (EvalError.notAFunction funcVal)

    | Expr.let_ name bindExpr bodyExpr => do
      let bindVal ← eval fuel env bindExpr
      let newEnv := env.extend name bindVal
      eval fuel newEnv bodyExpr

    | Expr.add e1 e2 => do
      let v1 ← eval fuel env e1
      let v2 ← eval fuel env e2
      match v1, v2 with
      | Value.int i1, Value.int i2 => pure (Value.int (i1 + i2))
      | Value.int _, _ => throw (EvalError.notAnInt v2)
      | _, _ => throw (EvalError.notAnInt v1)

    | Expr.if_ cond thenExpr elseExpr => do
      let condVal ← eval fuel env cond
      match condVal with
      | Value.bool true => eval fuel env thenExpr
      | Value.bool false => eval fuel env elseExpr
      | _ => throw (EvalError.notABool condVal)

-- Helper function with default fuel amount
def evalWithDefaultFuel (env : Env) (expr : Expr) : EvalM Value :=
  eval 1000 env expr

-- Helper constructors
def mkInt (n : Int) : Expr := Expr.lit (Value.int n)
def mkBool (b : Bool) : Expr := Expr.lit (Value.bool b)
def mkVar (name : VarName) : Expr := Expr.var name
def mkLambda (param : VarName) (body : Expr) : Expr := Expr.lambda param body
def mkApp (func : Expr) (arg : Expr) : Expr := Expr.app func arg
def mkLet (name : VarName) (bindExpr : Expr) (bodyExpr : Expr) : Expr := Expr.let_ name bindExpr bodyExpr

-- Example 1: Basic closure capturing a free variable
def example1 : Expr :=
  -- let x = 10 in λy. x + y
  mkLet "x" (mkInt 10)
    (mkLambda "y" (Expr.add (mkVar "x") (mkVar "y")))

-- Run example1
def runExample1 : IO Unit := do
  let result := evalWithDefaultFuel Env.empty example1
  match result with
  | Except.ok value => IO.println s!"Example 1 Result: {repr value}"
  | Except.error err => IO.println s!"Example 1 Error: {repr err}"

#eval runExample1

-- Example 2: Closure maintaining state across calls (counter)
def example2 : Expr :=
  -- let counter = 0 in
  -- let increment = λ_. counter + 1 in
  -- let newCounter = increment () in
  -- increment is a closure that captures 'counter'
  mkLet "counter" (mkInt 0)
    (mkLet "increment" (mkLambda "_" (Expr.add (mkVar "counter") (mkInt 1)))
      (mkApp (mkVar "increment") (mkInt 42))) -- argument ignored

def runExample2 : IO Unit := do
  let result := evalWithDefaultFuel Env.empty example2
  match result with
  | Except.ok value => IO.println s!"Example 2 Result: {repr value}"
  | Except.error err => IO.println s!"Example 2 Error: {repr err}"

#eval runExample2

-- Example 3: Higher-order function creating closures (partial application)
def example3 : Expr :=
  -- let add = λx. λy. x + y in
  -- let add5 = add 5 in
  -- add5 10
  mkLet "add" (mkLambda "x" (mkLambda "y" (Expr.add (mkVar "x") (mkVar "y"))))
    (mkLet "add5" (mkApp (mkVar "add") (mkInt 5))
      (mkApp (mkVar "add5") (mkInt 10)))

def runExample3 : IO Unit := do
  let result := evalWithDefaultFuel Env.empty example3
  match result with
  | Except.ok value => IO.println s!"Example 3 Result: {repr value}"
  | Except.error err => IO.println s!"Example 3 Error: {repr err}"

#eval runExample3

-- Example 4: Nested closures with multiple captured variables
def example4 : Expr :=
  -- let x = 100 in
  -- let y = 200 in
  -- let f = λz. x + y + z in
  -- f 300
  mkLet "x" (mkInt 100)
    (mkLet "y" (mkInt 200)
      (mkLet "f" (mkLambda "z" (Expr.add (Expr.add (mkVar "x") (mkVar "y")) (mkVar "z")))
        (mkApp (mkVar "f") (mkInt 300))))

def runExample4 : IO Unit := do
  let result := evalWithDefaultFuel Env.empty example4
  match result with
  | Except.ok value => IO.println s!"Example 4 Result: {repr value}"
  | Except.error err => IO.println s!"Example 4 Error: {repr err}"

#eval runExample4

-- Utility to demonstrate closure inspection
def showClosure (closure : Closure) : IO Unit := do
  IO.println s!"Closure parameter: {closure.param}"
  IO.println s!"Closure body: {repr closure.body}"
  IO.println "Captured environment:"
  for (name, value) in closure.env do
    IO.println s!"  {name} = {repr value}"

-- Demonstrate closure creation and inspection
def demonstrateClosures : IO Unit := do
  IO.println "=== Closure Demonstration ==="

  -- Create a closure that captures variables
  let expr := mkLet "a" (mkInt 42)
               (mkLet "b" (mkInt 58)
                 (mkLambda "x" (Expr.add (Expr.add (mkVar "a") (mkVar "b")) (mkVar "x"))))

  let result := evalWithDefaultFuel Env.empty expr
  match result with
  | Except.ok (Value.closure closure) => do
    IO.println "Created closure successfully!"
    showClosure closure

    -- Now apply the closure
    let application := mkApp expr (mkInt 100)
    let appResult := evalWithDefaultFuel Env.empty application
    match appResult with
    | Except.ok value => IO.println s!"Application result: {repr value}"
    | Except.error err => IO.println s!"Application error: {repr err}"

  | Except.ok other => IO.println s!"Expected closure, got: {repr other}"
  | Except.error err => IO.println s!"Error creating closure: {repr err}"

#eval demonstrateClosures
