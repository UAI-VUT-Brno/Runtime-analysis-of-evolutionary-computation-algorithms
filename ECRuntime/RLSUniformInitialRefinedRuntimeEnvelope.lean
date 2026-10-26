import ECRuntime.RLSUniformInitialExact
import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.RLSUniformInitialCorrectionEnvelope
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 147 — USER-APPROVED statement; promoted after the complete Round 29 gate; compiler-observed declaration pinned in Round29PromotionPins.
Literature direction: Doerr--Doerr (2013), coupon collection with random
initial stake. It refines Stage 144 using the exact Stage 138 identity;
its lower bound records the dimension-dependent geometric correction.
Lean compilation of this proposal is independent of any open analytic limit.
-/

/-- Exact random-start RLS average lies in a sharper explicit interval.
The term `2^(-n)` in the lower bound is a finite-dimension correction;
this statement makes no assertion about the full limiting distribution. -/
theorem proposed_rlsLinear_uniformInitial_refinedRuntimeEnvelope
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (n : Real) * (harmonicReal n - 1 + (1 : Real) / (2 : Real) ^ n) ≤
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n ∧
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n ≤
      (n : Real) * harmonicReal n := by
  have hstage134 := proposed_rlsLinear_uniformInitial_runtimeAverage hn w hw
  have hclosed := proposed_binomialHarmonicAverage_closedForm n
  have henv := proposed_rlsUniformInitial_harmonicCorrection_geometricEnvelope n
  have hrew :
      (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n =
      (n : Real) * (harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) := by
    rw [hstage134]
    calc
      (n : Real) / (2 : Real) ^ n *
          ((Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) * harmonicReal k)) =
        (n : Real) *
          (((Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n) := by ring
      _ = (n : Real) * (harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j))) := by rw [hclosed]
  rw [hrew]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    linarith [henv.2]
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    linarith [henv.1]

end ECRuntime
