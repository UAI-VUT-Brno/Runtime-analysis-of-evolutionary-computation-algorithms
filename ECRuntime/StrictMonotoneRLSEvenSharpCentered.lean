import ECRuntime.DoerrDoerrMonotoneUniformMean
import ECRuntime.RLSUniformInitialRuntimeFiniteCorrection
import ECRuntime.RLSUniformStartEvenSharpCentered
import Mathlib

open Filter
open scoped BigOperators

namespace ECRuntime

/-!
Stage 211: NEW proposed extension of Doerr--Doerr's sharp even-dimensional
uniform-start RLS runtime to *families* of strictly coordinate-monotone
fitness functions. Its theorem statement has now been approved; no promotion is claimed before gates.

The proof transfers the exact Stage 167 uniform-start identity via the
positive-linear finite identity, then invokes Stage 209. It requires no
additional asymptotic estimate and counts mutation iterations only.
-/

/-- The sharp additive correction for uniform-start one-bit RLS is independent
of the particular strictly coordinate-monotone objective at every dimension. -/
theorem proposed_strictMonotoneRLS_uniformInitial_evenSharpCentered
    (fitness : (n : Nat) → BitString n → Real)
    (hf : ∀ n : Nat, CandidateCoordinateStrictMonotonicity (fitness n)) :
    Tendsto
      (fun m : Nat =>
        if hn : 0 < 2 * m then
          strictMonotoneRLSUniformInitialMean hn (fitness (2 * m)) -
            (((2 * m : Nat) : Real) * harmonicReal m)
        else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  apply proposed_rlsLinear_uniformInitial_evenSharpCentered.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with m hm
  have hn : 0 < 2 * m := by omega
  have hw : PositiveLinearWeights
      (fun _ : Fin (2 * m) => (1 : Real)) := by
    intro i
    norm_num
  have hmon :=
    proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection
      hn (fitness (2 * m)) (hf (2 * m))
  have hlinear :=
    proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection
      hn (fun _ : Fin (2 * m) => (1 : Real)) hw
  have heq := hmon.trans hlinear.symm
  simpa only [dif_pos hn] using
    congrArg (fun z : Real =>
      z - (((2 * m : Nat) : Real) * harmonicReal m)) heq.symm

end ECRuntime
