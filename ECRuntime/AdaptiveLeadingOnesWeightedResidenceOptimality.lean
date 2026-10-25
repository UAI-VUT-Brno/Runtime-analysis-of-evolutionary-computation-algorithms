import ECRuntime.AdaptiveLeadingOnesOptimalResidenceBound
import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! Stage 244 (new, pending approval).
The pointwise optimal residence-cost bound extends to every finite
nonnegative weighting of levels. Only an independently certified
occupation/expectation formula can identify the weights with an
actual total-runtime objective. -/

/-- All nonnegative weighted sums of reciprocal exit probabilities
are minimized by the locally optimal levelwise mutation rates. -/
theorem proposed_leadingOnesAdaptive_optimalWeightedResidenceCost_le
    (n : Nat) (rate : Nat → Real) (w : Fin n → Real)
    (hw : ∀ i : Fin n, 0 ≤ w i)
    (hrate : ∀ j : Nat, j < n → 0 < rate j ∧ rate j < 1) :
    (∑ i : Fin n, w i *
      (leadingOnesLocallyOptimalSchedule i.val *
        (1 - leadingOnesLocallyOptimalSchedule i.val) ^ i.val)⁻¹) ≤
    (∑ i : Fin n, w i *
      (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (proposed_leadingOnesAdaptive_optimalLocalResidenceBound
       i.val (rate i.val) (hrate i.val i.isLt).1 (hrate i.val i.isLt).2)
    (hw i)

end ECRuntime
