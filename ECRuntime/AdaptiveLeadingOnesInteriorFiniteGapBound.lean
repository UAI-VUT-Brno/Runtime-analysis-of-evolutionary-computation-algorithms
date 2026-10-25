import ECRuntime.AdaptiveLeadingOnesInteriorFiniteResidenceGap
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! Stage 258 (P01, approved statement; pending promotion). This makes the cost of approaching
p₀=1 quantitatively small, rather than merely giving its exact rational
expression. It remains a residence-surrogate statement; Stage 245 still
requires a genuine pathwise occupation theorem. -/

/-- For 0 < ε ≤ 1/2, the total finite residence-sum overhead of the
strictly interior approximation is at most 2 ε. -/
theorem proposed_leadingOnesAdaptive_interiorFiniteResidenceGap_le_twoEps
    (n : Nat) (hn : 0 < n) (eps : Real)
    (heps0 : 0 < eps) (hepsHalf : eps ≤ 1 / 2) :
    (∑ i : Fin n,
      ((leadingOnesInteriorApproxSchedule eps i.val *
          (1 - leadingOnesInteriorApproxSchedule eps i.val) ^ i.val)⁻¹ -
        (leadingOnesLocallyOptimalSchedule i.val *
          (1 - leadingOnesLocallyOptimalSchedule i.val) ^ i.val)⁻¹)) ≤
      2 * eps := by
  have heps1 : eps < 1 := by linarith
  rw [proposed_leadingOnesAdaptive_interiorFiniteResidenceGap
    n hn eps heps0 heps1]
  have hden : (0 : Real) < 1 - eps := by linarith
  apply (div_le_iff₀ hden).2
  have hfac : 0 ≤ eps * (1 - 2 * eps) :=
    mul_nonneg heps0.le (by linarith)
  nlinarith

end ECRuntime
