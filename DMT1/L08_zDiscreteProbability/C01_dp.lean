import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Discrete Probability (finite sample spaces)
This module introduces a minimal collection of definitions that are
sufficient for a first‑course treatment of discrete probability in Lean 4.
All sample spaces are assumed **finite** so that sums are finite and
measures are defined by explicit enumeration.
-/

open Finset
open scoped BigOperators

namespace DiscreteProbability

noncomputable section
open Classical

/‑ A **sample space** is a finite set of outcomes.  ‑/
abbrev SampleSpace (Ω : Type) := Finset Ω
abbrev Event       (Ω : Type) := Finset Ω

/-- A probability measure on a finite sample space.  Elements that are
    not in `space` have probability `0` by `prob_support`. -/
structure ProbabilityMeasure (Ω : Type) where
  space        : SampleSpace Ω
  prob         : Ω → ℝ
  prob_nonneg  : ∀ ω, 0 ≤ prob ω
  prob_support : ∀ ω, ω ∉ space → prob ω = 0
  prob_sum_one := by
      classical
      -- `Ω.card` is positive and thus non‑zero because `Ω` is non‑empty.
      have hcard_pos : 0 < Ω.card := (Finset.card_pos).2 hΩ
      have hcard_ne : (Ω.card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcard_pos)
      -- Sum is `|Ω| * (1 / |Ω|)`.
      simp [Finset.sum_const, nsmul_eq_mul, hcard_ne] using
        mul_inv_cancel_iff_mul_eq.2 ⟨by
          simp [hcard_ne],
          by
            field_simp [hcard_ne]⟩ (μ : ProbabilityMeasure Ω)

/-- Probability of an event.  Only the part of the event lying inside
    the sample space contributes to the sum. -/
@[simp]
def P (A : Event Ω) : ℝ :=
  (A ∩ μ.space).sum μ.prob

@[simp] lemma P_empty : μ.P (∅ : Event Ω) = 0 := by
  simp [P]

@[simp] lemma P_univ : μ.P μ.space = 1 := by
  simpa [P] using μ.prob_sum_one

end ProbabilityMeasure

/-- Uniform probability measure on a **non‑empty** finite set. -/
/-- Uniform probability measure on a non‑empty finite set. -/
noncomputable
def uniformMeasure {α : Type} (Ω : Finset α) (hΩ : Ω.Nonempty) :
    ProbabilityMeasure α :=
  { space := Ω
  , prob  := fun ω => if _h : ω ∈ Ω then (1 : ℝ) / Ω.card else 0
  , prob_nonneg := by
      intro ω
      by_cases hω : ω ∈ Ω
      · have hcard_pos : (0 : ℝ) < (Ω.card : ℝ) := by
          have : 0 < Ω.card := (Finset.card_pos).2 hΩ
          exact_mod_cast this
        have : (0 : ℝ) ≤ (1 : ℝ) / Ω.card :=
          div_nonneg (by norm_num) (le_of_lt hcard_pos)
        simpa [hω] using this
      · simp [hω]
  , prob_support := by
      intro ω hω
      simp [hω]
  , prob_sum_one := by
      have hcard_pos : 0 < Ω.card := (Finset.card_pos).2 hΩ
      have hcard_ne : (Ω.card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcard_pos)
      have hsum : (Ω.sum fun ω => if _ : ω ∈ Ω then (1 : ℝ) / Ω.card else 0) =
          (Ω.sum fun _ => (1 : ℝ) / Ω.card) := by
        apply Finset.sum_congr rfl
        intro ω hω
        simp [hω]
      have hsum_const : (Ω.sum fun _ => (1 : ℝ) / Ω.card) =
          (Ω.card : ℝ) * ((1 : ℝ) / Ω.card) := by
        simp [Finset.sum_const, Nat.cast_mul]
      have hmul : (Ω.card : ℝ) * ((1 : ℝ) / Ω.card) = 1 := by
        field_simp [hcard_ne]
      simpa [hsum, hsum_const] using hmul }

namespace ProbabilityMeasure

variable {Ω : Type} (μ : ProbabilityMeasure Ω)

/-- Conditional probability `P(A | B)` assuming `P B ≠ 0`. -/
noncomputable
def condProb (A B : Event Ω) (hB : μ.P B ≠ 0) : ℝ :=
  μ.P (A ∩ B) / μ.P B

/-- Independence of events. -/
@[simp]
def Independent (A B : Event Ω) : Prop :=
  μ.P (A ∩ B) = μ.P A * μ.P B

/-- Bayes' rule (simple division‑by‑definition for finite spaces). -/
lemma bayes {A B : Event Ω} (hB : μ.P B ≠ 0) :
    condProb μ A B hB = μ.P (A ∩ B) / μ.P B := by
  rfl

/-- A discrete (finite) random variable with values in `α`. -/
abbrev DRandom (α : Type) := Ω → α

/-- Probability mass function `P(X = a)`. -/
noncomputable
def pmf {α} (X : DRandom μ α) (a : α) : ℝ :=
  ((μ.space.filter (fun ω => X ω = a)).sum μ.prob)

/-- Expectation of a real‑valued random variable. -/
noncomputable
def expectation (X : DRandom μ ℝ) : ℝ :=
  μ.space.sum (fun ω => μ.prob ω * X ω)

/-- Variance. -/
noncomputable
def variance (X : DRandom μ ℝ) : ℝ :=
  let μX := expectation μ X
  expectation μ (fun ω => (X ω - μX)^2)

/-- Indicator function of an event. -/
@[simp]
def indicator (A : Event Ω) : Ω → ℝ :=
  fun ω => if ω ∈ A then 1 else 0

/-- `E[1_A] = P(A)`. -/
lemma expectation_indicator_eq_prob (A : Event Ω) :
    expectation μ (indicator μ A) = μ.P A := by
  classical
  -- Unfold definitions
  unfold expectation indicator ProbabilityMeasure.P
  -- Push multiplication inside the `ite`
  simp_rw [mul_ite, mul_one, mul_zero]
  -- Rewrite the sum with `ite` as a sum over a filtered set
  have h_sum : μ.space.sum (fun ω => if ω ∈ A then μ.prob ω else 0) =
      (μ.space.filter (fun ω => ω ∈ A)).sum μ.prob := by
    -- Use `Finset.sum_filter` in the desired direction only
    simpa using
      (Finset.sum_filter (s := μ.space) (f := μ.prob) (p := fun ω => ω ∈ A)).symm
  -- Show that `filter` equals the finset intersection
  have h_set : μ.space.filter (fun ω => ω ∈ A) = A ∩ μ.space := by
    ext ω
    simp [Finset.mem_filter, and_comm, and_left_comm]
  -- Finish the calculation
  simpa [h_sum, h_set] 

end ProbabilityMeasure

end DiscreteProbability
