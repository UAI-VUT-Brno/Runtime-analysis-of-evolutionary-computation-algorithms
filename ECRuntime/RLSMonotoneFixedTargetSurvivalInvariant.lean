import ECRuntime.StrictMonotoneRLS
import ECRuntime.RLSFixedTarget
import Mathlib

namespace ECRuntime

/-!
Stage 271 (P02, new proposal). Upgrade the certified pointwise and
uniform mean invariance from expectation alone to the complete finite-
horizon survival sequence, for any zero-count fixed-target threshold.
This is a distributional statement, not just an expectation identity.
-/

/-- The complete finite-horizon fixed-target survival law of one-bit
RLS is independent of the choice of strictly coordinate-monotone
objective, at each initial bitstring and every horizon. -/
theorem proposed_strictMonotoneRLS_fixedTarget_survival_objectiveInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (r t : Nat) (x : BitString n) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
      (rlsZeroAtMost (n := n) r)ᶜ t x =
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
      (rlsZeroAtMost (n := n) r)ᶜ t x := by
  rw [candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness₁ hf₁,
      candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness₂ hf₂]

end ECRuntime
