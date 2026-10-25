import ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
import Mathlib

open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: transfer a full infinite time series, not just every finite
truncation. ENNReal permits nonnegative countable sums without a separate
summability assumption. We deliberately make no such claim for signed weights. -/

/-- For every nonnegative time weight, the (possibly infinite) total
survival functional agrees between coupon sampling and strict-monotone RLS. -/
theorem proposed_couponProcess_infiniteWeightedSurvival_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n))
    (weight : Nat → ENNReal) (x : BitString n) :
    (∑' t : Nat, weight t * ENNReal.ofReal
      (finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x)) =
    (∑' t : Nat, weight t * ENNReal.ofReal
      (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x)) := by
  apply tsum_congr
  intro t
  rw [proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
    hn fitness hf target t x]

end ECRuntime
