import ECRuntime.RLSUniformInitialExact
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 144 — USER-APPROVED statement (Round 26); promoted; Round 28 official full gate passed.
Source direction: Doerr--Doerr (2013), coupons with random initial stake.
The RLS uniform-start runtime is bounded by the worst-case coupon-collector
expectation n H_n, without requiring the unproved Stage 138 finite correction.
This is a finite theorem, not a claim of the paper's full limit law.
Round 25 found a multiplication-order mismatch in the final upper-bound step.
This round corrects it, retaining the exact approved theorem header.
-/

/-- The elementary binomial mass formula, independently proved in the
compiler-checked Stage 137 candidate, is reused without candidate imports. -/
private theorem stage144_binomialMass (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Real)) =
      (2 : Real) ^ n := by
  have h : ((1 : Real) + 1) ^ n =
      (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Real)) := by
    simp [add_pow]
  simpa only [one_add_one_eq_two] using h.symm

/-- Uniform initialization can only improve the worst-initial-state
expected runtime n H_n, for every positive linear fitness function.
Nonnegativity is included explicitly. -/
theorem proposed_rlsLinear_uniformInitial_runtimeEnvelope
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    0 ≤ (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n ∧
    (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n ≤
      (n : Real) * harmonicReal n := by
  have hstage134 := proposed_rlsLinear_uniformInitial_runtimeAverage hn w hw
  have hpow : (0 : Real) < (2 : Real) ^ n := by positivity
  have hsum_nonneg :
      0 ≤ (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k) := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (Nat.cast_nonneg _) (harmonicReal_nonneg k)
  have hsum_upper :
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k) ≤
        (2 : Real) ^ n * harmonicReal n := by
    calc
      (Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k) ≤
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal n) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            exact mul_le_mul_of_nonneg_left
              (harmonicReal_mono hkn) (Nat.cast_nonneg _)
      _ = (2 : Real) ^ n * harmonicReal n := by
        rw [← Finset.sum_mul, stage144_binomialMass]
  rw [hstage134]
  constructor
  · exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (le_of_lt hpow)) hsum_nonneg
  · have hnormalized :
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) /
            (2 : Real) ^ n ≤ harmonicReal n := by
      exact (div_le_iff₀ hpow).2 (by
        simpa only [mul_comm ((2 : Real) ^ n) (harmonicReal n)]
          using hsum_upper)
    calc
      (n : Real) / (2 : Real) ^ n *
          ((Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) * harmonicReal k)) =
        (n : Real) *
          (((Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) := by
              ring
      _ ≤ (n : Real) * harmonicReal n :=
        mul_le_mul_of_nonneg_left hnormalized (Nat.cast_nonneg _)

end ECRuntime
