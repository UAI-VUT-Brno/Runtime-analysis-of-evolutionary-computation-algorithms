import ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: the entire finite-time sequence of differences of survival
masses transfers through the exact coupon/RLS kernel correspondence.
For non-absorbing targets this is a survival-mass difference, not the
probability of a first hit. -/

/-- Adjacent-time survival-mass decrements agree for arbitrary targets. -/
theorem proposed_couponProcess_arbitraryTarget_survivalDecrement_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (t : Nat) (x : BitString n) :
    finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x -
      finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ (t + 1) x =
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      targetᶜ t x -
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ (t + 1) x := by
  rw [proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
      hn fitness hf target t x,
    proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
      hn fitness hf target (t + 1) x]

end ECRuntime
