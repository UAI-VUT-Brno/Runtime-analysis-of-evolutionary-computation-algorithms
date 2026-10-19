import ECRuntime.LeadingOnesOccupationTotalClosure
import ECRuntime.OneMax
import Mathlib

open scoped BigOperators ENNReal
open Finset

namespace ECRuntime

/-!
# Stage 27 fix 25: standard mutation-rate LeadingOnes corollaries

Stage 27 fix 24 fix 3 is compiler verified warning/error-free.  In particular, the
main exact finite-`n` uniformly initialized LeadingOnes expectation theorem is now
proved for every nondegenerate mutation rate `0 < p < 1`.

This file adds the standard evolutionary-computation specialization `p = 1/n`.
For `n >= 2` this rate lies strictly between zero and one, so the promoted exact
runtime theorem applies directly.  Keeping the rate and its range lemmas named avoids
repeating proof terms throughout the public API and makes the standard-rate corollaries
easier to use downstream.

The finite-sum statement remains deliberately unsimplified in this slice.  A subsequent
purely algebraic corollary may rewrite that finite geometric sum to the usual closed
form; no probabilistic or trajectory-semantic argument remains.
-/

/-- The conventional mutation rate for an `n`-bit `(1+1)` EA. -/
noncomputable def leadingOnesStandardMutationRate (n : ℕ) : ℝ :=
  (1 : ℝ) / (n : ℝ)

@[simp] theorem leadingOnesStandardMutationRate_eq_one_div_natCast (n : ℕ) :
    leadingOnesStandardMutationRate n = (1 : ℝ) / (n : ℝ) := by
  rfl

/-- The standard mutation rate is positive whenever the bit-string length is positive. -/
theorem leadingOnesStandardMutationRate_pos
    {n : ℕ} (hn : 0 < n) :
    0 < leadingOnesStandardMutationRate n := by
  unfold leadingOnesStandardMutationRate
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact one_div_pos.mpr hnR

/-- For `n >= 2`, the standard mutation rate is strictly smaller than one. -/
theorem leadingOnesStandardMutationRate_lt_one
    {n : ℕ} (hn : 2 ≤ n) :
    leadingOnesStandardMutationRate n < 1 := by
  unfold leadingOnesStandardMutationRate
  have hnR0 : (0 : ℝ) < (n : ℝ) := by
    have hn0 : 0 < n := by omega
    exact_mod_cast hn0
  have hnR1 : (1 : ℝ) < (n : ℝ) := by
    have hn1 : 1 < n := by omega
    exact_mod_cast hn1
  calc
    (1 : ℝ) / (n : ℝ) < (n : ℝ) / (n : ℝ) :=
      (div_lt_div_iff_of_pos_right hnR0).2 hnR1
    _ = 1 := div_self (ne_of_gt hnR0)

/-- Positive standard mutation rate in the nondegenerate `n >= 2` regime. -/
theorem leadingOnesStandardMutationRate_pos_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    0 < leadingOnesStandardMutationRate n := by
  exact leadingOnesStandardMutationRate_pos (by omega)

/-- Exact uniformly initialized LeadingOnes expectation at the standard rate `p = 1/n`,
in the canonical real-formula wrapper. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_standardMutationRate_eq_formula
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (leadingOnesStandardMutationRate n)
        (leadingOnesStandardMutationRate_pos_of_two_le hn).le
        (leadingOnesStandardMutationRate_lt_one hn).le =
      ENNReal.ofReal
        (leadingOnesUniformExpectedRuntimeFormula
          n (leadingOnesStandardMutationRate n)) := by
  exact
    leadingOnesUniformFirstHittingTimeExpectation_eq_formula
      (leadingOnesStandardMutationRate_pos_of_two_le hn)
      (leadingOnesStandardMutationRate_lt_one hn)

/-- Expanded exact finite-level runtime formula at the standard mutation rate `p = 1/n`. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_standardMutationRate_eq_finiteSum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (leadingOnesStandardMutationRate n)
        (leadingOnesStandardMutationRate_pos_of_two_le hn).le
        (leadingOnesStandardMutationRate_lt_one hn).le =
      ENNReal.ofReal
        ((1 / 2 : ℝ) *
          ∑ i : Fin n,
            (leadingOnesStandardMutationRate n *
              (1 - leadingOnesStandardMutationRate n) ^ i.val)⁻¹) := by
  exact
    leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum
      (leadingOnesStandardMutationRate_pos_of_two_le hn)
      (leadingOnesStandardMutationRate_lt_one hn)

/-- The exact uniformly initialized runtime at `p = 1/n` is finite for `n >= 2`. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_standardMutationRate_ne_top
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (leadingOnesStandardMutationRate n)
        (leadingOnesStandardMutationRate_pos_of_two_le hn).le
        (leadingOnesStandardMutationRate_lt_one hn).le ≠ ⊤ := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_standardMutationRate_eq_formula hn]
  exact ENNReal.ofReal_ne_top

/-- In every positive dimension, the LeadingOnes-specific spelling of the standard
mutation rate agrees with the repository-wide canonical `standardMutationRate`. -/
theorem leadingOnesStandardMutationRate_eq_standardMutationRate
    {n : ℕ} (hn : 0 < n) :
    leadingOnesStandardMutationRate n = standardMutationRate n := by
  simp [leadingOnesStandardMutationRate, standardMutationRate, Nat.ne_of_gt hn,
    div_eq_mul_inv]

/-- Exact uniformly initialized LeadingOnes expectation stated directly with the
repository-wide canonical standard mutation rate. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_formula
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (standardMutationRate n)
        (standardMutationRate_pos (by omega)).le
        (standardMutationRate_lt_one hn).le =
      ENNReal.ofReal
        (leadingOnesUniformExpectedRuntimeFormula n (standardMutationRate n)) := by
  exact
    leadingOnesUniformFirstHittingTimeExpectation_eq_formula
      (standardMutationRate_pos (by omega))
      (standardMutationRate_lt_one hn)

/-- Expanded exact finite-level runtime formula using the repository-wide canonical
standard mutation rate. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_finiteSum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (standardMutationRate n)
        (standardMutationRate_pos (by omega)).le
        (standardMutationRate_lt_one hn).le =
      ENNReal.ofReal
        ((1 / 2 : ℝ) *
          ∑ i : Fin n,
            (standardMutationRate n *
              (1 - standardMutationRate n) ^ i.val)⁻¹) := by
  exact
    leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum
      (standardMutationRate_pos (by omega))
      (standardMutationRate_lt_one hn)

/-- The exact uniformly initialized LeadingOnes runtime at the repository-wide
canonical standard rate is finite for `n >= 2`. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_ne_top
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (hn : 2 ≤ n) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (standardMutationRate n)
        (standardMutationRate_pos (by omega)).le
        (standardMutationRate_lt_one hn).le ≠ ⊤ := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_formula hn]
  exact ENNReal.ofReal_ne_top

end ECRuntime
