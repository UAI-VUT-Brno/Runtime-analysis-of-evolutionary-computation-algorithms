import ECRuntime.CouponWeightedSurvivalIncrementTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: power-weighted *survival decrements* are invariant. These
quantities are not identified with hitting-time masses unless the target
is absorbing, so the theorem states exactly the transferred functional. -/

/-- Polynomial weighting of successive survival decrements is preserved. -/
theorem proposed_couponProcess_powerWeightedSurvivalDecrement_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon exponent : Nat)
    (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      ((t : Real) ^ exponent) *
      (finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x -
        finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ (t+1) x))) =
    (Finset.sum (Finset.range horizon) (fun t =>
      ((t : Real) ^ exponent) *
      (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x -
       finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ (t+1) x))) := by
  exact proposed_couponProcess_weightedSurvivalDecrement_eq_RLS
    hn fitness hf target horizon (fun t => (t : Real) ^ exponent) x

end ECRuntime
