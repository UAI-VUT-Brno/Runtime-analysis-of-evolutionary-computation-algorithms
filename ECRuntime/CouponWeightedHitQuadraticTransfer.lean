import ECRuntime.RandomStakeCouponWeightedHittingTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: quadratic time weights in finite hitting-CDF functionals.
The result does not assume an absorbing target. -/

/-- Quadratically weighted hitting-by-time CDFs agree for coupon and RLS. -/
theorem proposed_couponProcess_quadraticWeightedHitByTime_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n -> Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat) (x : BitString n) :
    (∑ t ∈ Finset.range horizon,
      ((t : Real) ^ 2) * ((1 : Real) - finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x)) =
    (∑ t ∈ Finset.range horizon,
      ((t : Real) ^ 2) * ((1 : Real) - finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x)) := by
  exact proposed_couponProcess_arbitraryTarget_weightedHitByTime_eq_RLS
    hn fitness hf target horizon (fun t => (t : Real) ^ 2) x

end ECRuntime
