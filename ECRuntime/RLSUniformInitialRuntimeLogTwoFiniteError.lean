import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import ECRuntime.LogTwoHarmonicCorrectionFiniteSandwich
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 164 -- USER-APPROVED statement; independently compiler-clean in Round 43.
Statement header frozen. The public integration is provisional and needs the
Round 44 complete eight-gate check. No promotion is claimed yet.
Literature direction: Doerr--Doerr (2013), coupon collection with a random
initial stake. This quantifies the finite error for the *actual expected
one-bit RLS runtime*, not merely the binomial-harmonic average.

Dependencies: certified Stages 142 (exact finite RLS correction) and
154 (finite logarithmic half-series enclosure). Neither adaptive mutation
nor the full distribution of coupon-collector runtime is addressed.
-/

/-- Under uniform initialization, the exact expected number of one-bit RLS
iterations on any positive linear objective differs from the second-order
approximation `n * (H_n - log 2)` by at most `n / 2^n`. -/
theorem proposed_rlsLinear_uniformInitial_logTwoFiniteRuntimeEnvelope
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) :
    (n : Real) * (harmonicReal n - Real.log 2) ≤
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
        (n : Real) *
          (harmonicReal n - Real.log 2 + (1 : Real) / (2 : Real) ^ n) := by
  let C : Real :=
    (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j))
  have hfinite : C ≤ Real.log 2 ∧
      Real.log 2 ≤ C + (1 : Real) / (2 : Real) ^ n := by
    simpa only [C] using proposed_logTwo_harmonicHalfSeries_finiteSandwich n
  have hnnonneg : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg _
  have hlow : harmonicReal n - Real.log 2 ≤ harmonicReal n - C := by
    linarith [hfinite.1]
  have hupp : harmonicReal n - C ≤
      harmonicReal n - Real.log 2 + (1 : Real) / (2 : Real) ^ n := by
    linarith [hfinite.2]
  constructor
  · rw [proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection hn w hw]
    exact mul_le_mul_of_nonneg_left hlow hnnonneg
  · rw [proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection hn w hw]
    exact mul_le_mul_of_nonneg_left hupp hnnonneg

end ECRuntime
