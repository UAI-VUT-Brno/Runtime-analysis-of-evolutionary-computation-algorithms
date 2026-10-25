import ECRuntime.CouponWeightedSurvivalIncrementTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: a finite probability-generating-polynomial transfer for survival
increments.  For arbitrary nonabsorbing targets these are signed changes of
survival mass, not necessarily the first-hitting distribution. -/

/-- Discounted finite survival-decrement polynomials of the coupon process
and strictly monotone RLS agree for every target and starting state. -/
theorem proposed_couponProcess_discountedSurvivalDecrement_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (discount : Real) (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      discount ^ t *
        (finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x -
         finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ (t + 1) x))) =
    (Finset.sum (Finset.range horizon) (fun t =>
      discount ^ t *
        (finiteLevelSurvival
           ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
           targetᶜ t x -
         finiteLevelSurvival
           ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
           targetᶜ (t + 1) x))) := by
  exact proposed_couponProcess_weightedSurvivalDecrement_eq_RLS
    hn fitness hf target horizon (fun t => discount ^ t) x

end ECRuntime
