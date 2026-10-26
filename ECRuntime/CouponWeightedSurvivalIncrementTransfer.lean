import ECRuntime.RandomStakeCouponSurvivalIncrementTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: signed time weights applied to increments of the survival
profile transfer exactly between the coupon and monotone-RLS kernels.
This is not yet a first-hitting-time mass identity for nonabsorbing targets. -/

/-- Weighted successive survival decrements agree at every finite horizon. -/
theorem proposed_couponProcess_weightedSurvivalDecrement_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n -> Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (weight : Nat -> Real) (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      weight t * (finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x -
          finiteLevelSurvival (randomStakeCouponTransition hn)
            targetᶜ (t + 1) x))) =
    (Finset.sum (Finset.range horizon) (fun t =>
      weight t * (finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x -
          finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
              targetᶜ (t + 1) x))) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
        hn fitness hf target t x,
      proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
        hn fitness hf target (t + 1) x]

end ECRuntime
