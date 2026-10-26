import ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: complement the exact arbitrary-target finite-horizon survival
law to obtain the cumulative target-hitting distribution. No assumption
about target monotonicity, symmetry, or starting distribution is needed. -/

/-- Coupon and strict-monotone RLS target-hitting probabilities coincide at
all finite horizons, expressed as one minus nonhitting survival probability. -/
theorem proposed_couponProcess_arbitraryTarget_hitByTime_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (t : Nat) (x : BitString n) :
    (1 : Real) - finiteLevelSurvival
      (randomStakeCouponTransition hn) targetᶜ t x =
    (1 : Real) - finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      targetᶜ t x := by
  rw [proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
    hn fitness hf target t x]

end ECRuntime
