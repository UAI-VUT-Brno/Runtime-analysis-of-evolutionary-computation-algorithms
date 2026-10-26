import ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: equal finite-time laws transfer *arbitrary finite linear
functionals* of survival, not just the first truncated moment. This
provides a reusable bridge toward variance and distributional claims. -/

/-- Arbitrarily weighted finite sums of target survival probabilities
coincide for the direct coupon process and strict-monotone RLS. -/
theorem proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (weight : Nat → Real) (x : BitString n) :
    (∑ t ∈ Finset.range horizon,
      weight t * finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x) =
    (∑ t ∈ Finset.range horizon,
      weight t * finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
    hn fitness hf target t x]

end ECRuntime
