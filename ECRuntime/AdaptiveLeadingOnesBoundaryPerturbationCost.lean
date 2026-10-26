import ECRuntime.AdaptiveLeadingOnesInteriorApproxSchedule
import Mathlib

namespace ECRuntime

/-! Stage 246 (P01, approved statement; proof-34 diagnostic repair).
At the level-zero boundary, replacing the optimal p₀=1 by p₀=1-ε
adds exactly ε/(1-ε) to the reciprocal exit rate. This is algebraic
and is NOT an expected-total-runtime assertion before Stage 245 closes. -/

/-- Exact level-zero price of making the locally optimal adaptive
LeadingOnes schedule strictly interior. -/
theorem proposed_leadingOnesAdaptive_interiorZeroResidenceGap
    (eps : Real) (heps0 : 0 < eps) (heps1 : eps < 1) :
    (leadingOnesInteriorApproxSchedule eps 0 *
      (1 - leadingOnesInteriorApproxSchedule eps 0) ^ 0)⁻¹ -
      (leadingOnesLocallyOptimalSchedule 0 *
        (1 - leadingOnesLocallyOptimalSchedule 0) ^ 0)⁻¹ =
      eps / (1 - eps) := by
  -- The hypothesis `0 < eps` is not needed by the bare rational identity,
  -- but it is part of the frozen admissible-perturbation statement. Check
  -- explicitly that the forbidden eps=0 boundary cannot occur.
  by_cases hz : eps = 0
  · exact False.elim ((ne_of_gt heps0) hz)
  · have hne : 1 - eps ≠ (0 : Real) := ne_of_gt (sub_pos.mpr heps1)
    have hrate : leadingOnesInteriorApproxSchedule eps 0 = 1 - eps := rfl
    have hopt : leadingOnesLocallyOptimalSchedule 0 = 1 := by
      norm_num [leadingOnesLocallyOptimalSchedule]
    simp only [hrate, hopt, pow_zero, mul_one, inv_one]
    field_simp [hne]
    ring

end ECRuntime
