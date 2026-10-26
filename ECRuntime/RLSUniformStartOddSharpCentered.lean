import ECRuntime.RLSUniformStartOddCenteredIdentity
import ECRuntime.RandomInitialStakeScaledBinomialCorrectionLimit
import ECRuntime.RandomInitialStakeOddSharpCorrection
import Mathlib

open Filter
open scoped BigOperators

namespace ECRuntime

/-!
Stage 210 (NEW proposal; awaiting human statement approval).

Odd-dimensional sharp expected runtime of uniform-start one-bit RLS on
canonical positive linear weights. Unlike the even case, the centered
additive correction is +1/2. This proposition requires both the exact
Stage 207 finite identity and the Stage 208 scaled series-tail limit.
-/

/-- The expected runtime centered at `(2m+1) * H_m` has limiting additive
constant `+1/2` for odd dimensions. -/
theorem proposed_rlsLinear_uniformInitial_oddSharpCentered :
    Tendsto
      (fun m : Nat =>
        ((Finset.univ.sum (fun x : BitString (2 * m + 1) =>
          (runtimeSup
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
              (show 0 < 2 * m + 1 by omega)).transition
              (linearFitness (fun _ : Fin (2 * m + 1) => (1 : Real))))
            ({allOnes (2 * m + 1)} : Set (BitString (2 * m + 1))) x).toReal)) /
              (2 : Real) ^ (2 * m + 1)) -
          (((2 * m + 1 : Nat) : Real) * harmonicReal m))
      atTop (nhds (1 / 2 : Real)) := by
  have hDoublePlus : Tendsto (fun m : Nat => 2 * m + 1) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall
        (fun m : Nat => (show m <= 2 * m + 1 by omega)))
      tendsto_id
  have hsum : Tendsto
      (fun m : Nat =>
        (((2 * m + 1 : Nat) : Real) *
          (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) +
        (((2 * m + 1 : Nat) : Real) *
          (Real.log 2 - (Finset.Icc 1 (2 * m + 1)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))))
      atTop (nhds (1 / 2 : Real)) := by
    simpa only [Function.comp_def, add_zero] using
      (proposed_randomInitialStake_oddSharpHalfHarmonicCorrection.add
        (proposed_randomInitialStake_scaledBinomialCorrection_tendsto_zero.comp
          hDoublePlus))
  apply hsum.congr'
  filter_upwards [] with m
  have hn : 0 < 2 * m + 1 := by omega
  have hw : PositiveLinearWeights (fun _ : Fin (2 * m + 1) => (1 : Real)) := by
    intro i
    norm_num
  simpa only using
    (proposed_rlsLinear_uniformInitial_oddCentered_exact m hn
      (fun _ : Fin (2 * m + 1) => (1 : Real)) hw).symm

end ECRuntime
