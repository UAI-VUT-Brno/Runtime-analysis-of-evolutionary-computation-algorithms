import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.RLSUniformInitialExact
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 142 — USER-APPROVED STATEMENT; promoted after the complete Round 29 gate; compiler-observed declaration pinned in Round29PromotionPins.
Literature direction: Doerr--Doerr (2013), Collecting Coupons with Random
Initial Stake. This is the exact finite-dimension runtime counterpart of
Stage 138, not an assertion of the full distributional results of the paper.

Dependency: Stage 134 is promoted and supplies the exact binomial-harmonic
runtime average. The Stage 138 finite identity passed all eight official Round 28 gates.
The Round 29 public integration and non-vacuity witness passed the complete
eight-gate verifier; the proof statement and implementation are frozen.
-/

/-- Exact expected mutation iterations under uniform initialization,
for any positive linear objective, with the finite binomial correction. -/
theorem proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (Finset.univ.sum (fun x : BitString n =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n)) x).toReal)) /
      (2 : Real) ^ n =
    (n : Real) *
      (harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) := by
  -- Stage 138 passed the official Round 28 promotion gate.
  have hclosed := proposed_binomialHarmonicAverage_closedForm n
  have hstage134 := proposed_rlsLinear_uniformInitial_runtimeAverage hn w hw
  rw [hstage134]
  rw [← hclosed]
  ring

end ECRuntime
