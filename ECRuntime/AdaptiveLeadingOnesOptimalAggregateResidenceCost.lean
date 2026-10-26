import ECRuntime.AdaptiveLeadingOnesOptimalResidenceBound
import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! Stage 239, proposed, NOT APPROVED.
The locally optimal rate minimizes the **sum of conditional residence
costs** over all LeadingOnes levels. This is a comparison of finite
algebraic functionals. Identifying it with actual total runtime requires a
separate pathwise occupation/expectation decomposition. -/

/-- The sum of inverse one-step exit masses is pointwise minimized by the
per-level optimal mutation schedule. This is not yet a total-runtime claim. -/
theorem proposed_leadingOnesAdaptive_optimalAggregateResidenceCost_le
    (n : Nat) (rate : Nat → Real)
    (hrate : ∀ j : Nat, j < n → 0 < rate j ∧ rate j < 1) :
    (∑ i : Fin n,
      (leadingOnesLocallyOptimalSchedule i.val *
        (1 - leadingOnesLocallyOptimalSchedule i.val) ^ i.val)⁻¹) ≤
    (∑ i : Fin n,
      (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  apply Finset.sum_le_sum
  intro i _
  exact proposed_leadingOnesAdaptive_optimalLocalResidenceBound
    i.val (rate i.val) (hrate i.val i.isLt).1 (hrate i.val i.isLt).2

end ECRuntime
