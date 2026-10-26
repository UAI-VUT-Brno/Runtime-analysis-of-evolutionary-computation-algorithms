import ECRuntime.RandomStakeCouponWeightedHittingTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: a finite discounted hitting CDF generating polynomial, valid
for every real discount. This complements the certified discounted
survival result without assuming the target is absorbing. -/

/-- Discounted finite hitting-by-time generating sums agree statewise. -/
theorem proposed_couponProcess_discountedHitByTime_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (discount : Real) (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      discount ^ t *
        ((1 : Real) - finiteLevelSurvival
          (randomStakeCouponTransition hn) targetᶜ t x))) =
    (Finset.sum (Finset.range horizon) (fun t =>
      discount ^ t *
        ((1 : Real) - finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x))) := by
  exact proposed_couponProcess_arbitraryTarget_weightedHitByTime_eq_RLS
    hn fitness hf target horizon (fun t => discount ^ t) x

end ECRuntime
