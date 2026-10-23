import ECRuntime.RLSUniformInitialLogRuntimeLower
import ECRuntime.RLSUniformInitialLogRuntimeEnvelope
import Mathlib

namespace ECRuntime

/-!
Stage 153 — USER-APPROVED statement; source compiled cleanly in Round 32. Full public gate pending.
Doerr--Doerr (2013), coupon collection with a random initial stake.
This extracts an explicit additive O(n) error around n log n from the
already-promoted logarithmic runtime bounds, uniformly over positive weights.
It is finite-dimensional and does not depend on the open Stage 137 limit.
-/

/-- Uniform-start RLS has an additive at-most-n discrepancy from n log n
for every positive dimension and every strictly positive linear objective. -/
theorem proposed_rlsLinear_uniformInitial_nLogN_additiveEnvelope
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (n : Real) * Real.log (n : Real) - (n : Real) ≤
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n ∧
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
        (2 : Real) ^ n ≤
      (n : Real) * Real.log (n : Real) + (n : Real) := by
  have hlower := proposed_rlsLinear_uniformInitial_logRuntimeLower hn w hw
  have hupper := proposed_rlsLinear_uniformInitial_logRuntimeUpper hn w hw
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hlogle : Real.log (n : Real) ≤ Real.log ((n : Real) + 1) :=
    Real.log_le_log hnpos (by linarith)
  have hpow : (0 : Real) ≤ (1 : Real) / (2 : Real) ^ n := by positivity
  have hterm : Real.log (n : Real) - 1 ≤
      Real.log ((n : Real) + 1) - 1 + (1 : Real) / (2 : Real) ^ n := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hterm (le_of_lt hnpos)
  constructor
  · calc
      (n : Real) * Real.log (n : Real) - (n : Real) =
          (n : Real) * (Real.log (n : Real) - 1) := by ring
      _ ≤ (n : Real) * (Real.log ((n : Real) + 1) - 1 +
          (1 : Real) / (2 : Real) ^ n) := hscaled
      _ ≤ _ := hlower
  · calc
      _ ≤ (n : Real) * (1 + Real.log (n : Real)) := hupper
      _ = (n : Real) * Real.log (n : Real) + (n : Real) := by ring

end ECRuntime
