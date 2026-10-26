import ECRuntime.RandomStakeCouponArbitraryTargetHittingProbability
import Mathlib

open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: extended-nonnegative weighted infinite time functionals of the
pointwise cumulative hitting distribution. Unlike the difference of
arbitrary nonabsorbing survival masses, this is a CDF-like complement
functional, not automatically a first-hitting point mass. -/

/-- Infinite nonnegative weighted hitting-by-time CDF functionals transfer. -/
theorem proposed_couponProcess_infiniteWeightedHitByTime_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n))
    (weight : Nat → ENNReal) (x : BitString n) :
    (∑' t : Nat, weight t * ENNReal.ofReal
      ((1 : Real) - finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x)) =
    (∑' t : Nat, weight t * ENNReal.ofReal
      ((1 : Real) - finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x)) := by
  apply tsum_congr
  intro t
  rw [proposed_couponProcess_arbitraryTarget_hitByTime_eq_strictMonotoneRLS
    hn fitness hf target t x]

end ECRuntime
