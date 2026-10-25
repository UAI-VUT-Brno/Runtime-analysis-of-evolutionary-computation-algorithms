import ECRuntime.DoerrDoerrMonotoneUniformMean
import Mathlib

namespace ECRuntime

/-!
Stage 265 (P02). The exact uniform-start RLS mean is objective-invariant
within the coordinatewise strictly monotone class, not just asymptotically
universal. This is a clean finite-dimensional strengthening of the paper
scope provided by the existing explicit coupon-collector identity.
-/

/-- Every two strictly coordinate-monotone fitness functions on the same
Boolean space have exactly the same uniform-start one-bit RLS mean. -/
theorem proposed_strictMonotoneRLS_uniformMean_objectiveInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂) :
    strictMonotoneRLSUniformInitialMean hn fitness₁ =
      strictMonotoneRLSUniformInitialMean hn fitness₂ := by
  exact
    (proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection hn fitness₁ hf₁).trans
      (proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection hn fitness₂ hf₂).symm

end ECRuntime
