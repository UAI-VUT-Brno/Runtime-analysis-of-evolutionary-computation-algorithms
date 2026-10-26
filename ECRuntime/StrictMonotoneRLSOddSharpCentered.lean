import ECRuntime.DoerrDoerrMonotoneUniformMean
import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import ECRuntime.RLSUniformStartOddSharpCentered
import Mathlib

open Filter
open scoped BigOperators

namespace ECRuntime

/-!
Stage 212: NEW proposed odd-dimensional counterpart to Stage 211.
This strengthens the objective class of the sharp Doerr--Doerr conclusion
from the canonical positive-linear objective to arbitrary dimension-indexed
strictly coordinate-monotone fitness functions, subject to the exact
formalized monotonicity predicate. Statement approval is recorded; Lean promotion checks remain mandatory.
-/

/-- The odd-dimensional sharp `+1/2` additive correction holds for any
strictly coordinate-monotone family of objective functions. -/
theorem proposed_strictMonotoneRLS_uniformInitial_oddSharpCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun m : Nat =>
        strictMonotoneRLSUniformInitialMean
            (show 0 < 2 * m + 1 by omega) (fitness (2 * m + 1)) -
          (((2 * m + 1 : Nat) : Real) * harmonicReal m))
      atTop (nhds (1 / 2 : Real)) := by
  apply proposed_rlsLinear_uniformInitial_oddSharpCentered.congr'
  filter_upwards [] with m
  have hn : 0 < 2 * m + 1 := by omega
  have hw : PositiveLinearWeights
      (fun _ : Fin (2 * m + 1) => (1 : Real)) := by
    intro i
    norm_num
  have hmon :=
    proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection
      hn (fitness (2 * m + 1)) (hf (2 * m + 1))
  have hlinear :=
    proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection
      hn (fun _ : Fin (2 * m + 1) => (1 : Real)) hw
  have heq := hmon.trans hlinear.symm
  simpa only using
    congrArg (fun z : Real =>
      z - (((2 * m + 1 : Nat) : Real) * harmonicReal m)) heq.symm

end ECRuntime
