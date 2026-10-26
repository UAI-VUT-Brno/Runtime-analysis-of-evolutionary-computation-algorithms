import ECRuntime.RLSWeightedInfiniteSurvivalFunctional
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02: the certified per-target all-time survival invariance can be
summed over *countably* many independent thresholds and cost profiles.
This permits the extended value infinity without convergence hypotheses. -/

/-- Countable sums of nonnegative, threshold-dependent infinite survival
costs are invariant under changing the strictly monotone objective. -/
theorem proposed_strictMonotoneRLS_countableThresholdSurvivalCost_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (initial : Nat → BitString n → ENNReal)
    (cost : Nat → Nat → ENNReal) :
    (∑' r : Nat,
      ∑ x : BitString n,
        initial r x * (∑' t : Nat, cost r t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
            (rlsZeroAtMost (n := n) r)ᶜ t x))) =
    (∑' r : Nat,
      ∑ x : BitString n,
        initial r x * (∑' t : Nat, cost r t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
            (rlsZeroAtMost (n := n) r)ᶜ t x))) := by
  classical
  apply tsum_congr
  intro r
  exact proposed_strictMonotoneRLS_weightedInfiniteSurvivalCost_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ r (initial r) (cost r)

end ECRuntime
