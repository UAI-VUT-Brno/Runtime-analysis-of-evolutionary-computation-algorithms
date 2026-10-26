import ECRuntime.RLSWeightedInfiniteSurvivalFunctional
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02: a joint finite collection of target thresholds can have different
starting weights and different nonnegative time costs, yet its entire
infinite-horizon survival functional is objective invariant. -/

/-- Simultaneous (possibly nonuniform) infinite survival costs for finitely
many thresholds are invariant across strictly monotone objectives. -/
theorem proposed_strictMonotoneRLS_multiThresholdInfiniteSurvival_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (thresholds : Finset Nat)
    (initial : Nat → BitString n → ENNReal)
    (cost : Nat → Nat → ENNReal) :
    (∑ r ∈ thresholds,
      ∑ x : BitString n,
        initial r x * (∑' t : Nat, cost r t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
            (rlsZeroAtMost (n := n) r)ᶜ t x))) =
    (∑ r ∈ thresholds,
      ∑ x : BitString n,
        initial r x * (∑' t : Nat, cost r t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
            (rlsZeroAtMost (n := n) r)ᶜ t x))) := by
  classical
  apply Finset.sum_congr rfl
  intro r _
  exact proposed_strictMonotoneRLS_weightedInfiniteSurvivalCost_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ r (initial r) (cost r)

end ECRuntime
