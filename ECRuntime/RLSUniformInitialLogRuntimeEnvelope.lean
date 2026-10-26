import ECRuntime.RLSUniformInitialExpectedRuntimeEnvelope
import Mathlib

namespace ECRuntime

/-!
Stage 149 — PROMOTED after the user-supplied Round 30 official eight-gate verification.
Source direction: Doerr--Doerr (2013), random initial stake. The exact
RLS uniform-start runtime formula yields this finite n(1+log n) upper bound,
not the full first-order limit. The compiler-observed signature and axioms
are frozen in `ECRuntimeTest.Round30PromotionPins`.
-/

/-- A finite n(1+log n) average runtime upper bound for one-bit RLS
on positive linear functions, uniformly over the positive weights. -/
theorem proposed_rlsLinear_uniformInitial_logRuntimeUpper
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (Finset.univ.sum (fun x : BitString n =>
      (runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w))
        ({allOnes n} : Set (BitString n)) x).toReal)) /
      (2 : Real) ^ n ≤
    (n : Real) * (1 + Real.log (n : Real)) := by
  have hmain := (proposed_rlsLinear_uniformInitial_runtimeEnvelope hn w hw).2
  have hharm : harmonicReal n ≤ 1 + Real.log (n : Real) :=
    harmonic_le_one_add_log n
  exact hmain.trans (mul_le_mul_of_nonneg_left hharm (Nat.cast_nonneg n))

end ECRuntime
