import ECRuntime.DoerrDoerrMonotoneUniformMean
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! Stage 250 (P02, pending approval).
The source's half-harmonic centering is H_(n/2) = (H_floor + H_ceil)/2.
The *finite-n* representation is valid in both parity classes, for every
strictly coordinate-monotone fitness function. The joint all-n limit still
requires a parity-gluing theorem. -/

/-- Exact all-dimension RLS identity relative to the source-paper
half-harmonic center, with no asymptotic or parity assumption. -/
theorem proposed_strictMonotoneRLS_allDimensionPaperCentered_exact
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    strictMonotoneRLSUniformInitialMean hn fitness -
        (n : Real) *
          ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) =
      (n : Real) *
        (harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)) -
          (harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) := by
  rw [proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection hn fitness hf]
  ring

end ECRuntime
