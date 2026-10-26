import ECRuntime.AdaptiveLeadingOnesScalarRenewalSolution
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 279 (P01, research candidate). This is an explicit finite convolution
solution of the approved scalar renewal equation. The finite recurrence
is not yet the infinite occupation/first-hitting-time identity of Stage 245.
The power-index rearrangement uses Mathlib `Finset.sum_range_succ`,
`Finset.mul_sum`, `pow_succ`, and `omega` and awaits compiler verification.
-/

/-- Exact scalar renewal unrolling; the entry at time `s` contributes
`q^(t-1-s)` to occupation at time `t`. -/
theorem proposed_finiteOccupationRenewalSolution_convolution
    (q initial : Real) (entry : Nat → Real) (t : Nat) :
    finiteOccupationRenewalSolution q initial entry t =
      q ^ t * initial +
      ∑ s ∈ Finset.range t, q ^ (t - 1 - s) * entry s := by
  induction t with
  | zero =>
      simp [finiteOccupationRenewalSolution]
  | succ t ih =>
      rw [finiteOccupationRenewalSolution, ih, Finset.sum_range_succ]
      have hterm : ∀ s ∈ Finset.range t,
          q * (q ^ (t - 1 - s) * entry s) =
            q ^ (t + 1 - 1 - s) * entry s := by
        intro s hs
        have hst : s < t := Finset.mem_range.mp hs
        have hexp : t + 1 - 1 - s = (t - 1 - s) + 1 := by omega
        rw [hexp, pow_succ]
        ring
      have hsum :
          q * (∑ s ∈ Finset.range t, q ^ (t - 1 - s) * entry s) =
            ∑ s ∈ Finset.range t, q ^ (t + 1 - 1 - s) * entry s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
      rw [mul_add, hsum, pow_succ]
      have hlast : t + 1 - 1 - t = 0 := by omega
      rw [hlast, pow_zero, one_mul]
      ring

end ECRuntime
