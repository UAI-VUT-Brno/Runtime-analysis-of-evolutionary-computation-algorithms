import ECRuntime.RandomStakeCouponArbitraryTargetHittingProbability
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: equality of the entire finite-horizon hitting CDF yields
arbitrary signed weighted hit-by-time functionals, useful for distributional
comparison and discrete generating functions. -/

/-- Arbitrary finite weighted hitting-probability functionals transfer
from the coupon process to strictly monotone RLS. -/
theorem proposed_couponProcess_arbitraryTarget_weightedHitByTime_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (weight : Nat → Real) (x : BitString n) :
    (∑ t ∈ Finset.range horizon,
      weight t * ((1 : Real) - finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x)) =
    (∑ t ∈ Finset.range horizon,
      weight t * ((1 : Real) - finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x)) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [proposed_couponProcess_arbitraryTarget_hitByTime_eq_strictMonotoneRLS
    hn fitness hf target t x]

end ECRuntime
