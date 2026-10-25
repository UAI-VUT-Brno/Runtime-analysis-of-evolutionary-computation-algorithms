import ECRuntime.RLSInfiniteSurvivalFunctionalInvariance
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02: remove the uniform-initialization restriction from the infinite
survival-cost statement. All initial weights and time costs are nonnegative
extended reals, so neither finiteness nor convergence is assumed. -/

/-- Infinite survival costs are objective invariant for every nonnegative
initial mass profile, not only a uniform start. -/
theorem proposed_strictMonotoneRLS_weightedInfiniteSurvivalCost_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r : Nat) (initial : BitString n → ENNReal) (cost : Nat → ENNReal) :
    (∑ x : BitString n,
      initial x * (∑' t : Nat, cost t * ENNReal.ofReal
        (finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
          (rlsZeroAtMost (n := n) r)ᶜ t x))) =
    (∑ x : BitString n,
      initial x * (∑' t : Nat, cost t * ENNReal.ofReal
        (finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
          (rlsZeroAtMost (n := n) r)ᶜ t x))) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  rw [proposed_strictMonotoneRLS_infiniteSurvivalFunctional_invariant
    hn fitness₁ fitness₂ hf₁ hf₂ r x cost]

end ECRuntime
