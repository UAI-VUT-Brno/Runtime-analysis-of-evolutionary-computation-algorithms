import ECRuntime.StrictMonotoneRLS
import Mathlib

namespace ECRuntime

/-!
Stage 268 (P02, proposed). Objective invariance is true at each initial
bitstring, not only after uniform averaging. The theorem uses the already
certified common coupon-collector runtime representation.
-/

/-- The exact expected runtime of one-bit RLS, starting at a fixed bitstring,
is identical for any two strictly coordinate-monotone objectives. -/
theorem proposed_strictMonotoneRLS_pointwiseRuntime_objectiveInvariant
    {n : Nat} (hn : 0 < n)
    (fitness₁ fitness₂ : BitString n → Real)
    (hf₁ : CandidateCoordinateStrictMonotonicity fitness₁)
    (hf₂ : CandidateCoordinateStrictMonotonicity fitness₂)
    (x : BitString n) :
    runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₁)
        ({allOnes n} : Set (BitString n)) x =
      runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness₂)
        ({allOnes n} : Set (BitString n)) x := by
  rw [candidateStrictMonotoneRLS_runtimeSup_eq_harmonic hn fitness₁ hf₁ x,
      candidateStrictMonotoneRLS_runtimeSup_eq_harmonic hn fitness₂ hf₂ x]

end ECRuntime
