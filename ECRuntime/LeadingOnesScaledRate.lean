import ECRuntime.LeadingOnesOccupationTotalClosure
import ECRuntime.MutationRateRegime
import Mathlib

open scoped BigOperators ENNReal
open Finset

namespace ECRuntime

/-!
# Stage 28: exact LeadingOnes runtime in the `p = c/n` regime

Stage 27 proves the exact uniformly initialized finite-`n` LeadingOnes expectation for
every `0 < p < 1`.  This file merely specializes that promoted theorem through the
reusable `scaledMutationRate c n` API.  It is the finite-dimensional entry point for
the `p=c/n` regime used by the later asymptotic and tight-linear-function stages.
-/

/-- Exact uniformly initialized LeadingOnes expectation at mutation rate `p = c/n`. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {c : ℝ} (hc : 0 < c) (hn : 0 < n) (hcn : c < (n : ℝ)) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (scaledMutationRate c n)
        (scaledMutationRate_pos hc hn).le
        (scaledMutationRate_lt_one hn hcn).le =
      ENNReal.ofReal
        (leadingOnesUniformExpectedRuntimeFormula n (scaledMutationRate c n)) := by
  exact leadingOnesUniformFirstHittingTimeExpectation_eq_formula
    (scaledMutationRate_pos hc hn) (scaledMutationRate_lt_one hn hcn)

/-- Expanded exact finite-level LeadingOnes runtime formula at mutation rate `p = c/n`. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_finiteSum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {c : ℝ} (hc : 0 < c) (hn : 0 < n) (hcn : c < (n : ℝ)) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (scaledMutationRate c n)
        (scaledMutationRate_pos hc hn).le
        (scaledMutationRate_lt_one hn hcn).le =
      ENNReal.ofReal
        ((1 / 2 : ℝ) *
          ∑ i : Fin n,
            (scaledMutationRate c n *
              (1 - scaledMutationRate c n) ^ i.val)⁻¹) := by
  exact leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum
    (scaledMutationRate_pos hc hn) (scaledMutationRate_lt_one hn hcn)

/-- The exact uniformly initialized LeadingOnes runtime is finite throughout the
nondegenerate `p=c/n` regime. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_ne_top
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {c : ℝ} (hc : 0 < c) (hn : 0 < n) (hcn : c < (n : ℝ)) :
    leadingOnesUniformFirstHittingTimeExpectation
        n (scaledMutationRate c n)
        (scaledMutationRate_pos hc hn).le
        (scaledMutationRate_lt_one hn hcn).le ≠ ⊤ := by
  rw [leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula
    hc hn hcn]
  exact ENNReal.ofReal_ne_top

end ECRuntime
