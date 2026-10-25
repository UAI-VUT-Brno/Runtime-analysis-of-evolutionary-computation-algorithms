import ECRuntime.RLSMonotoneWeightedSurvivalInvariance
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! P02: exact invariance extends from each finite survival mass to
arbitrary signed time-dependent cost profiles and initial state weights. -/

/-- Strictly coordinate-monotone objectives induce the same finite-horizon
weighted survival-cost functional for arbitrary real time costs. -/
theorem proposed_strictMonotoneRLS_weightedSurvivalCostProfile_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (weights : BitString n → Real) (cost : Nat → Real) (r T : Nat) :
    (∑ t ∈ Finset.range T, cost t *
      (∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ t x)) =
    (∑ t ∈ Finset.range T, cost t *
      (∑ x : BitString n, weights x *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ t x)) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [proposed_strictMonotoneRLS_weightedFixedTargetSurvival_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ weights r t]

end ECRuntime
