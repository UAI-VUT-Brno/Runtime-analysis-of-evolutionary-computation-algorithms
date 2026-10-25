import ECRuntime.AdaptiveLeadingOnesWeightedResidenceOptimality
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! Stage 249 (P01, pending approval).
This is the sharp half-weighted aggregate cost bound required **after** the
occupation bridge is established. It does not equate an aggregate cost with
actual expected runtime. -/

/-- The locally optimal adaptive rate schedule minimizes the finite
half-weighted residence surrogate among strictly interior rate schedules. -/
theorem proposed_leadingOnesAdaptive_halfResidenceCost_optimal
    (n : Nat) (rate : Nat → Real)
    (hrate : ∀ j : Nat, j < n → 0 < rate j ∧ rate j < 1) :
    (1 / 2 : Real) *
      (∑ i : Fin n,
        (leadingOnesLocallyOptimalSchedule i.val *
          (1 - leadingOnesLocallyOptimalSchedule i.val) ^ i.val)⁻¹) ≤
    (1 / 2 : Real) *
      (∑ i : Fin n,
        (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  have h := proposed_leadingOnesAdaptive_optimalWeightedResidenceCost_le
    n rate (fun _ => (1 / 2 : Real)) (by intro i; norm_num) hrate
  simpa only [Finset.mul_sum] using h

end ECRuntime
