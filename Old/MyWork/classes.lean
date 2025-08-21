import DMT1.Lectures.L02_propLogic.semantics
import DMT1.Lectures.L02_propLogic.syntax
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

namespace classes





class Eval (Etype Stype : Type) where
(eval : Etype → Stype → Bool)

-- Instance for propositional logic
instance propEval :
Eval (DMT1.lecture.propLogic.syntax.Expr) (DMT1.lecture.propLogic.semantics.Interp) :=
{ eval := λ e i => DMT1.lecture.propLogic.semantics.eval e i }


-- Example:
def e : DMT1.lecture.propLogic.syntax.Expr := ⊤
def i : DMT1.lecture.propLogic.semantics.Interp := fun _ => true

-- We can call propLogic eval directly or as stored in the propEval instance
#reduce DMT1.lecture.propLogic.semantics.eval e i
#reduce propEval.eval e i
#check propEval.eval


/- @@@
Example: Predicate Logic
-/

section predLogic

/-
Summary of Multi-Type Domain Representation in Type Theory
Feature	Type Theory Mechanism	Example
Separate types for each "sort"	Define distinct types	N,StrN,Str.
Disjoint union of types	Sum types (A+BA+B)	N+BoolN+Bool.
Combining attributes	Product types (A×BA×B)	Str×NStr×N.
Indexed domains	Dependent types (A(x)A(x))	Vec(R,n)Vec(R,n).
All possible types	Universes (Type0Type0​)	Quantifying over types.
Relationships between types	Category-like structures	Graphs or
other relational structures.
-/


/- @@@
Types - Car, Bool, Nat
Sets
Funcs
Rels
-/



structure AVDomain : Type 1 where
(Car : Type)
(cars : Set car)
(massKgFun : Car → Nat)
(nearRel : Car → Car → Bool)

inductive PredExpr : Type where
| foo


inductive AVPredExpr : Type where
| carVarExpr : AVPredExpr
| carFuncExpr : AVPredExpr
| relExpr : AVPredExpr

class predInterp (e : predExpr)




structure predInterp : Type where
()


end predLogic

/-
D: The domain of discourse, a non-empty set over which variables range.
II: The interpretation function, which assigns:

    Elements of DD to constant symbols.
    Subsets of DnDn (relations) to nn-ary predicate symbols.
    Functions Dn→DDn→D to nn-ary function symbols.
-/


def superEval (Etype Stype : Type) [i : Eval Etype Stype] (e : Etype) (s : Stype) : Bool :=
  i.eval e s

open Eval

#reduce eval e i



end classes
