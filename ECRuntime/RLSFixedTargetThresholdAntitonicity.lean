import ECRuntime.RLSFixedTargetAllInitialStates
import Mathlib

namespace ECRuntime

/-! Stage 262 (P07, new proposed statement). Increasing the permitted
number of remaining zero bits can only decrease the exact fixed-target
runtime; this is proved with the certified all-start harmonic formula. -/

/-- Monotonicity of the exact pointwise RLS hitting-time expectation in
the fixed-target threshold, uniformly in the strictly positive weights. -/
theorem proposed_rlsLinear_fixedTarget_runtimeReal_antitone_threshold
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (r s : Nat) (hrs : r ≤ s)
    (x : BitString n) :
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) s) x).toReal ≤
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal := by
  rw [proposed_rlsLinear_fixedTarget_runtimeReal_allInitialStates hn w hw s x,
      proposed_rlsLinear_fixedTarget_runtimeReal_allInitialStates hn w hw r x]
  by_cases hr : zeroCount x ≤ r
  · have hs : zeroCount x ≤ s := le_trans hr hrs
    simp [hr, hs]
  · by_cases hs : zeroCount x ≤ s
    · simp only [if_pos hs, if_neg hr]
      have hrk : r ≤ zeroCount x := by omega
      exact mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (harmonicReal_mono hrk))
    · simp only [if_neg hr, if_neg hs]
      have hhar : harmonicReal r ≤ harmonicReal s := harmonicReal_mono hrs
      have hn0 : 0 ≤ (n : Real) := Nat.cast_nonneg _
      nlinarith

end ECRuntime
