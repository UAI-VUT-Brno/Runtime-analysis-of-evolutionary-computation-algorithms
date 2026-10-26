import ECRuntime.RLSMonotoneFixedTargetSurvivalInvariant
import Mathlib

namespace ECRuntime

/-!
Stage 280 (P02, proposed). The entire time-to-target probability law,
including each individual exact hitting-time mass, is invariant under
changes of a strictly coordinate-monotone fitness function. This is the
finite-difference consequence of the certified finite-horizon survival law.
-/

/-- Equality of exact fixed-target first-hitting-time masses, expressed
as consecutive survival differences, for two strictly monotone objectives. -/
theorem proposed_strictMonotoneRLS_fixedTarget_hittingMass_objectiveInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r t : Nat) (x : BitString n) :
    (finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
      (rlsZeroAtMost (n := n) r)ᶜ t x -
     finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
      (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x) =
    (finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
      (rlsZeroAtMost (n := n) r)ᶜ t x -
     finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
      (rlsZeroAtMost (n := n) r)ᶜ (t + 1) x) := by
  rw [proposed_strictMonotoneRLS_fixedTarget_survival_objectiveInvariant
        hn fitness₁ fitness₂ hf₁ hf₂ r t x]
  rw [proposed_strictMonotoneRLS_fixedTarget_survival_objectiveInvariant
        hn fitness₁ fitness₂ hf₁ hf₂ r (t + 1) x]

end ECRuntime
