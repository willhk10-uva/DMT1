inductive FuncSymbol
  | const : String → FuncSymbol -- Constants are 0-ary functions
  | func : String → Nat → FuncSymbol -- Functions with arity

inductive PredSymbol
  | pred : String → Nat → PredSymbol -- Predicates with arity

-- Define terms
inductive Term
  | var : String → Term -- Variables
  | app : FuncSymbol → List Term → Term -- Function application

open FuncSymbol Term

-- Define formulas
inductive Formula
  | true_ : Formula -- True constant
  | false_ : Formula -- False constant
  | atom : PredSymbol → List Term → Formula -- Atomic formula
  | not_ : Formula → Formula -- Negation
  | and_ : Formula → Formula → Formula -- Conjunction
  | or_ : Formula → Formula → Formula -- Disjunction
  | implies_ : Formula → Formula → Formula -- Implication
  | forall_ : String → Formula → Formula -- Universal quantifier
  | exists_ : String → Formula → Formula -- Existential quantifier

structure Structure where
  (domain : Type) -- The domain of individuals
  (funcInterp : FuncSymbol → List domain → domain) -- Interpretation of function symbols
  (predInterp : PredSymbol → List domain → Prop) -- Interpretation of predicate symbols


def VarAssignment (S : Structure) := String → S.domain

def evalTerm {S : Structure} (assign : VarAssignment S) : Term → S.domain
  | Term.var x => assign x
  | Term.app f args =>
      let evaluatedArgs := args.attach.map (fun ⟨t, _⟩ => evalTerm assign t)
      S.funcInterp f evaluatedArgs

/-
def evalFormulaBool {S : Structure} (assign : VarAssignment S) : Formula → Bool
  | Formula.true_ => true
  | Formula.false_ => false
  | Formula.atom p args =>
      let evaluatedArgs := args.attach.map (fun ⟨t, _⟩ => evalTerm assign t)
      S.predInterp p evaluatedArgs  -- `predInterp` now returns `Bool`
  | Formula.not_ φ => !(evalFormulaBool assign φ)
  | Formula.and_ φ ψ => (evalFormulaBool assign φ) && (evalFormulaBool assign ψ)
  | Formula.or_ φ ψ => (evalFormulaBool assign φ) || (evalFormulaBool assign ψ)
  | Formula.implies_ φ ψ => !(evalFormulaBool assign φ) || (evalFormulaBool assign ψ)  -- `A → B` is `¬A ∨ B`
  | Formula.forall_ x φ =>
      (List.range 10).all (fun d => evalFormulaBool (fun y => if y = x then d else assign y) φ)
  | Formula.exists_ x φ =>
      (List.range 10).any (fun d => evalFormulaBool (fun y => if y = x then d else assign y) φ)
-/

def evalFormula {S : Structure} (assign : VarAssignment S) : Formula → Prop
  | Formula.true_ => True
  | Formula.false_ => False
  | Formula.atom p args =>
      let evaluatedArgs := args.attach.map (fun ⟨t, _⟩ => evalTerm assign t)
      S.predInterp p evaluatedArgs
  | Formula.not_ φ => ¬(evalFormula assign φ)
  | Formula.and_ φ ψ => (evalFormula assign φ) ∧ (evalFormula assign ψ)
  | Formula.or_ φ ψ => (evalFormula assign φ) ∨ (evalFormula assign ψ)
  | Formula.implies_ φ ψ => (evalFormula assign φ) → (evalFormula assign ψ)
  | Formula.forall_ x φ =>
      ∀ (d : S.domain), evalFormula (fun y => if y = x then d else assign y) φ
  | Formula.exists_ x φ =>
      ∃ (d : S.domain), evalFormula (fun y => if y = x then d else assign y) φ

/-! ### Examples of Terms and Their Evaluation -/
def natStructure : Structure where
  domain := Nat  -- Set the domain to Nat
  funcInterp :=
    fun f args =>
      match f, args with
      | FuncSymbol.const "zero", [] => 0
      | FuncSymbol.const "one", [] => 1
      | FuncSymbol.func "add" 2, [x, y] => x + y
      | FuncSymbol.func "mul" 2, [x, y] => x * y
      | _, _ => panic! "Undefined function symbol"
  predInterp :=
    fun p args =>
      match p, args with
      | PredSymbol.pred "leq" 2, [x, y] => x ≤ y
      | _, _ => panic! "Undefined predicate"

-- Explicitly tell Lean that `natStructure.domain` supports numeric literals
instance : OfNat natStructure.domain n where
  ofNat := n

-- Define a variable assignment
def natAssign : VarAssignment natStructure :=
  fun x => match x with
    | "x" => 3  -- Works because `OfNat` is now defined
    | "y" => 5
    | _ => 0  -- Default value


-- Example terms
def term1 : Term := Term.var "x"  -- Variable x
def term2 : Term := Term.var "y"  -- Variable y
def term3 : Term := Term.app (FuncSymbol.const "one") []  -- Constant 1
def term4 : Term := Term.app (FuncSymbol.func "add" 2) [term1, term2]  -- x + y

-- Evaluating terms in natStructure
#eval evalTerm natAssign term1  -- Output: 3
#eval evalTerm natAssign term2  -- Output: 5
#eval evalTerm natAssign term3  -- Output: 1
#eval evalTerm natAssign term4  -- Output: 3 + 5 = 8


/-! ### Examples of Predicate Evaluation -/

-- Example formulas with predicates
def formula1 : Formula := Formula.atom (PredSymbol.pred "leq" 2) [term1, term2]  -- leq(x, y)  → 3 ≤ 5
def formula2 : Formula := Formula.not_ formula1  -- ¬ leq(x, y)  → ¬(3 ≤ 5)
def formula3 : Formula := Formula.and_ formula1 (Formula.atom (PredSymbol.pred "leq" 2) [term2, term1])
-- (leq(x, y) ∧ leq(y, x)) → (3 ≤ 5 ∧ 5 ≤ 3)

-- Evaluating formulas in natStructure
set_option diagnostics true


example : evalFormula natAssign formula1  := by
  simp [formula1, evalFormula, term1, term2, evalTerm, natAssign]



--example : evalFormula natAssign formula2 = True := _
--example : evalFormula natAssign formula3 = True  := _
