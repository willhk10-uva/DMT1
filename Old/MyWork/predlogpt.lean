namespace predLogic

inductive Szort
  | Int
  | Bool
  | String
  | Custom (name : String)

def interpret : Szort → Type
  | Szort.Int => Int
  | Szort.Bool => Bool
  | Szort.String => String
  | Szort.Custom _ => String -- Default to String for simplicity


inductive Term : Szort → Type
  | var : ∀ {s : Szort}, String → Term s
  | const : ∀ {s : Szort}, interpret s → Term s
  | func : (argSorts : List Szort) → (retSort : Szort) →
      String → (args : List (Σ s, Term s)) → Term retSort

instance : Inhabited (interpret Szort.Int) := { default := (0:Int) }          -- Default for Int
instance : Inhabited (interpret Szort.Bool) := ⟨false⟩     -- Default for Bool
instance : Inhabited (interpret Szort.String) := ⟨""⟩      -- Default for String


set_option diagnostics true

-- Evaluation for Terms
def Term.eval {s : Szort} [Inhabited (interpret retSzort)] (env : String → ∀ s, Term s) : Term s → interpret s
  | Term.var x =>
    match env x with
    | t => Term.eval env (t s)
  | Term.const val => val
  | Term.func argSzorts retSzort fname args =>
    -- Ensure arguments align with expected Szorts
    if argSzorts.length != args.length then
      panic! "Arity mismatch: expected {argSzorts.length}, but got {args.length}"
    else
      let evaluatedArgs := args.zip argSzorts |>.map (fun ⟨⟨Szort, term⟩, expectedSzort⟩ =>
        if Szort != expectedSzort then
          panic! s!"Szort mismatch: expected {expectedSzort}, but got {Szort}"
        else
          Term.eval env term)
      -- Implement function evaluation logic here
      match fname with
      | "add" =>
        match evaluatedArgs with
        | [x, y] =>
          match x, y with
          | Int, Int => x + y   -- TODO: check
          | _, _ => panic! "Argument type mismatch for add"
        | _ => panic! "Incorrect number of arguments for add"
      | _ => panic! s!"Function {fname} evaluation not implemented yet"

inductive Predicate : List Szort → Type
  | pred : String → Predicate args

inductive Formula : Type
  | atom : ∀ {argSzorts : List Szort},
      Predicate argSzorts → (args : List (Σ s, Term s)) → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | forall_ : Szort → String → Formula → Formula
  | exists_ : Szort → String → Formula → Formula

-- Evaluation for Formulas
def Formula.eval (env : String → ∀ s, Term s) : Formula → Bool
  | Formula.atom pred args =>
    -- Placeholder for predicate evaluation
    panic! "Predicate evaluation not implemented"
  | Formula.not φ => not (Formula.eval env φ)
  | Formula.and φ₁ φ₂ => (Formula.eval env φ₁) && (Formula.eval env φ₂)
  | Formula.or φ₁ φ₂ => (Formula.eval env φ₁) || (Formula.eval env φ₂)
  | Formula.forall_ s var φ =>
    -- Implement universal quantifier evaluation
    panic! "Universal quantifier evaluation not implemented"
  | Formula.exists_ s var φ =>
    -- Implement existential quantifier evaluation
    panic! "Existential quantifier evaluation not implemented"

-- Example: Defining terms and functions
def termX := Term.const Szort.Int 42
def termY := Term.const Szort.Int 24

def exampleFunc := Term.func [Szort.Int, Szort.Int] Szort.Int
  "add" -- Function name
  [⟨Szort.Int, termX⟩, ⟨Szort.Int, termY⟩]

-- Example: Evaluating a function
def dummyEnv : String → ∀ s, Term s := fun x => Term.const Szort.Int 0

#eval Term.eval dummyEnv exampleFunc -- Outputs: 66

-- Example: Defining a predicate
def examplePredicate : Predicate [Szort.Int] := Predicate.pred "isPositive"

-- Example: Defining a formula
def exampleFormula := Formula.and
  (Formula.atom examplePredicate [⟨Szort.Int, termX⟩]) -- isPositive(42)
  (Formula.atom examplePredicate [⟨Szort.Int, termY⟩]) -- isPositive(24)

end predLogic
