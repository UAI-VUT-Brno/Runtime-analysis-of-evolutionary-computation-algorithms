import ECRuntime.RLSMonotoneFixedTargetSurvivalInvariant
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 276 (P02, dependent research proposal). A fixed-target
finite-horizon distributional invariance, for arbitrary signed initial
weights and not merely an expectation under uniform initialization.
Stage 271 must first be compiler-promoted.
-/

/-- Every finite-horizon fixed-target survival average has the same
value under two strictly coordinate-monotone objective functions, for
any prescribed initial weighting. -/
theorem proposed_strictMonotoneRLS_weightedFixedTargetSurvival_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (weights : BitString n → Real) (r t : Nat) :
    (∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        (rlsZeroAtMost (n := n) r)ᶜ t x) =
    (∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        (rlsZeroAtMost (n := n) r)ᶜ t x) := by
  apply Finset.sum_congr rfl
  intro x _hx
  rw [proposed_strictMonotoneRLS_fixedTarget_survival_objectiveInvariant
    hn fitness₁ fitness₂ hf₁ hf₂ r t x]

end ECRuntime
