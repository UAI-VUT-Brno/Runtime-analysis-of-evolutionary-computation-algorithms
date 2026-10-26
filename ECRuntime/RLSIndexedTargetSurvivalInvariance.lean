import ECRuntime.RLSWeightedInfiniteSurvivalFunctional
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02. An arbitrary countable index can select a possibly repeated target
threshold; no injectivity or convergence assumption is needed for ENNReal. -/

/-- Countable indexed families of nonnegative survival costs are invariant
under the strictly monotone objective, even for repeated thresholds. -/
theorem proposed_strictMonotoneRLS_indexedThresholdSurvivalCost_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (threshold : Nat → Nat)
    (initial : Nat → BitString n → ENNReal)
    (cost : Nat → Nat → ENNReal) :
    (∑' a : Nat,
      ∑ x : BitString n,
        initial a x * (∑' t : Nat, cost a t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
            (rlsZeroAtMost (n := n) (threshold a))ᶜ t x))) =
    (∑' a : Nat,
      ∑ x : BitString n,
        initial a x * (∑' t : Nat, cost a t * ENNReal.ofReal
          (finiteLevelSurvival
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
            (rlsZeroAtMost (n := n) (threshold a))ᶜ t x))) := by
  classical
  apply tsum_congr
  intro a
  exact proposed_strictMonotoneRLS_weightedInfiniteSurvivalCost_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ (threshold a) (initial a) (cost a)

end ECRuntime
