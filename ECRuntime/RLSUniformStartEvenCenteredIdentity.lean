import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import ECRuntime.RandomInitialStakeEvenSharpCorrection
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 206 (proposed; not approved or promoted).
Even-dimensional exact decomposition of the random-initial-stake RLS runtime
into the half-dimension harmonic term, the now-certified sharp dyadic
correction, and the still-uncontrolled exponentially small binomial tail.
This is an algebraic identity, not the paper's sharp runtime asymptotic.
-/

/-- Exact even-dimensional runtime decomposition around the half-index harmonic
number. It isolates the sole remaining correction term needed for the
Doerr--Doerr sharp expected-runtime asymptotic. -/
theorem proposed_rlsLinear_uniformInitial_evenCentered_exact
    (m : Nat) (hn : 0 < 2 * m) (w : Fin (2 * m) → Real)
    (hw : PositiveLinearWeights w) :
    ((Finset.univ.sum (fun x : BitString (2 * m) =>
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes (2 * m)} : Set (BitString (2 * m))) x).toReal)) /
      (2 : Real) ^ (2 * m)) -
        (((2 * m : Nat) : Real) * harmonicReal m) =
      (((2 * m : Nat) : Real) *
        (harmonicReal (2 * m) - harmonicReal m - Real.log 2)) +
      (((2 * m : Nat) : Real) *
        (Real.log 2 -
          (Finset.Icc 1 (2 * m)).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))) := by
  have hmean := proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection hn w hw
  rw [hmean]
  ring

end ECRuntime
