import ECRuntime.HarmonicLogLower
import ECRuntime.RLSUniformInitialRefinedRuntimeEnvelope
import Mathlib

namespace ECRuntime

/-!
Stage 150 — USER-APPROVED theorem statement; provisional Round 31 public integration.
Doerr--Doerr (2013) random-initial-stake coupon collection: finite,
dimension-dependent LOWER logarithmic bound matching the approved Stage 149
upper logarithmic bound at first order. Relies only on promoted Stage 147 and promoted Stage 148.
Independently compiled clean in Round 30; full public gate remains pending.
-/

/-- Explicit finite lower runtime envelope for uniformly initialized
one-bit RLS on all strictly positive linear objectives. -/
theorem proposed_rlsLinear_uniformInitial_logRuntimeLower
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (n : Real) * (Real.log ((n : Real) + 1) - 1 +
      (1 : Real) / (2 : Real) ^ n) ≤
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n := by
  have hlog := proposed_harmonicReal_log_succ_le n
  have hrefined :=
    (proposed_rlsLinear_uniformInitial_refinedRuntimeEnvelope hn w hw).1
  calc
    (n : Real) * (Real.log ((n : Real) + 1) - 1 +
        (1 : Real) / (2 : Real) ^ n) ≤
      (n : Real) * (harmonicReal n - 1 +
        (1 : Real) / (2 : Real) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
          linarith
    _ ≤ _ := hrefined

end ECRuntime
