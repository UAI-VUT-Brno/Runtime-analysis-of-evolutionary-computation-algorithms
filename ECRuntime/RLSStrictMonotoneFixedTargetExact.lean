import ECRuntime.RLSFixedTargetAllInitialStates
import ECRuntime.StrictMonotoneRLS
import Mathlib

namespace ECRuntime

/-!
Stage 272 (P07, new proposal). Extend the genuine fixed-target
truncated-harmonic runtime from positive linear functions to the
entire class of coordinatewise strictly increasing Boolean fitness
functions. This removes the linearity assumption on the objective.
-/

/-- The unrestricted one-bit RLS runtime to at most `r` zero bits,
started from any bitstring, has the same exact truncated-harmonic
formula for every strictly coordinate-monotone objective. -/
theorem proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (r : Nat) (x : BitString n) :
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      (rlsZeroAtMost (n := n) r) x).toReal =
        if zeroCount x ≤ r then 0
        else (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) := by
  have hones : PositiveLinearWeights (fun _ : Fin n => (1 : Real)) := by
    intro i
    exact zero_lt_one
  have h := proposed_rlsLinear_fixedTarget_runtimeReal_allInitialStates
    hn (fun _ : Fin n => (1 : Real)) hones r x
  rw [candidate_rls_linear_transition_eq_oneMax hn
    (fun _ : Fin n => (1 : Real)) hones] at h
  rw [candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf]
  exact h

end ECRuntime
