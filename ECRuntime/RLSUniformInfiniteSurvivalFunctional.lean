import ECRuntime.RLSInfiniteSurvivalFunctionalInvariance
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02. A nonnegative infinite-horizon cost profile averaged under an
arbitrary finite initial distribution. Stage 306 supplies the statewise
identity; no summability or finiteness assumptions are needed in ENNReal. -/

/-- For coordinate-strictly-monotone objectives, the uniform-start
nonnegative infinite-horizon fixed-target survival functional is objective
independent, even when its extended value is infinite. -/
theorem proposed_strictMonotoneRLS_uniformInfiniteSurvivalCost_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r : Nat) (cost : Nat → ENNReal) :
    (∑ x : BitString n,
      ∑' t : Nat, cost t * ENNReal.ofReal
        (finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ t x)) =
    (∑ x : BitString n,
      ∑' t : Nat, cost t * ENNReal.ofReal
        (finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ t x)) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  exact proposed_strictMonotoneRLS_infiniteSurvivalFunctional_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ r x cost

end ECRuntime
