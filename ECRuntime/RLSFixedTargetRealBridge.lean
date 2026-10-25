import ECRuntime.RLSFixedTarget
import Mathlib

namespace ECRuntime

/-! Stage 251 (P07, pending approval).
The Stage-114 fixed-target RLS theorem returns an ENNReal expectation.
This real-valued corollary prepares uniform-initialization averaging for
one-bit RLS fixed-target analysis, which is algorithmically distinct from
the LeadingOnes fixed-target family. -/

/-- One-bit RLS fixed-target runtime in real arithmetic, when its initial
zero count is no smaller than the allowed number of remaining zeros. -/
theorem proposed_rlsLinear_fixedTarget_runtimeReal_eq_truncatedHarmonic
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (r : Nat) (x : BitString n) (hr : r ≤ zeroCount x) :
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal =
      (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) := by
  rw [rlsLinear_fixedTarget_runtimeSup_eq hn w hw r x hr]
  exact ENNReal.toReal_ofReal
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (harmonicReal_mono hr)))

end ECRuntime
