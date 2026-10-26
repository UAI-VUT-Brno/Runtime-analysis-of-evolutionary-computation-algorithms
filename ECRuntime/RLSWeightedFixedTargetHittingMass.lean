import ECRuntime.RLSMonotoneWeightedSurvivalInvariance
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 285 (P02, proposed). From the verified full finite-horizon survival
law, derive the corresponding arbitrary-weight first-hitting-time mass
invariance. This algebra works for signed weights; it claims neither a
probability distribution nor nonnegativity without additional hypotheses.
-/

/-- First-hit mass as a consecutive difference of finite survival weights
is invariant under changes between strictly monotone objectives. -/
theorem proposed_strictMonotoneRLS_weightedFixedTarget_hittingMass_invariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (weights : BitString n → Real) (r t : Nat) :
    ((∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        (rlsZeroAtMost (n := n) r)ᶜ t x) -
     (∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) =
    ((∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        (rlsZeroAtMost (n := n) r)ᶜ t x) -
     (∑ x : BitString n, weights x *
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x)) := by
  rw [proposed_strictMonotoneRLS_weightedFixedTargetSurvival_invariant
      hn fitness₁ fitness₂ hf₁ hf₂ weights r t]
  rw [proposed_strictMonotoneRLS_weightedFixedTargetSurvival_invariant
      hn fitness₁ fitness₂ hf₁ hf₂ weights r (t + 1)]

end ECRuntime
