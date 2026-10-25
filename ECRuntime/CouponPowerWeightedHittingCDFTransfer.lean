import ECRuntime.RandomStakeCouponWeightedHittingTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: arbitrary nonnegative integer power-weighted hitting CDFs
transfer, even when the target is not absorbing. These are finite
functionals and do not identify first-hitting masses by subtraction. -/

/-- Every finite power-weighted hitting-by-time functional is preserved. -/
theorem proposed_couponProcess_powerWeightedHitByTime_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon exponent : Nat)
    (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      (t : Real) ^ exponent *
        ((1 : Real) - finiteLevelSurvival
          (randomStakeCouponTransition hn) targetᶜ t x))) =
    (Finset.sum (Finset.range horizon) (fun t =>
      (t : Real) ^ exponent *
        ((1 : Real) - finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x))) := by
  exact proposed_couponProcess_arbitraryTarget_weightedHitByTime_eq_RLS
    hn fitness hf target horizon (fun t => (t : Real) ^ exponent) x

end ECRuntime
