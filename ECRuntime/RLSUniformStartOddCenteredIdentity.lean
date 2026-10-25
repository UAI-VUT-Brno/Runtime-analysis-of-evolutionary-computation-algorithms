import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import ECRuntime.RandomInitialStakeOddScaledTailBridge
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 207 (proposed; not approved or promoted).
Odd-dimensional exact decomposition of the random-initial-stake RLS runtime.
The centered term now has the certified parity bridge and will admit the
+1/2 sharp harmonic limit once Stage 186 is promoted. The geometric-binomial
remainder still requires a separate asymptotic estimate.
-/

/-- Exact odd-dimensional runtime decomposition relative to `H_m`.
Unlike the even version, its sharp harmonic correction tends to +1/2. -/
theorem proposed_rlsLinear_uniformInitial_oddCentered_exact
    (m : Nat) (hn : 0 < 2 * m + 1) (w : Fin (2 * m + 1) → Real)
    (hw : PositiveLinearWeights w) :
    ((Finset.univ.sum (fun x : BitString (2 * m + 1) =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes (2 * m + 1)} : Set (BitString (2 * m + 1))) x).toReal)) /
      (2 : Real) ^ (2 * m + 1)) -
        (((2 * m + 1 : Nat) : Real) * harmonicReal m) =
      (((2 * m + 1 : Nat) : Real) *
        (harmonicReal (2 * m + 1) - harmonicReal m - Real.log 2)) +
      (((2 * m + 1 : Nat) : Real) *
        (Real.log 2 -
          (Finset.Icc 1 (2 * m + 1)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))) := by
  have hmean := proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection hn w hw
  rw [hmean]
  ring

end ECRuntime
