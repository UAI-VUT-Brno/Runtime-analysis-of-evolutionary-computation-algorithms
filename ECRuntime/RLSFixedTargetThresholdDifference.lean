import ECRuntime.RLSFixedTargetRealBridge
import Mathlib

namespace ECRuntime

/-!
Stage 254 (P07): proposed, NOT yet approved. A target-level comparison
for the one-bit RLS runtime in a common initial state. This is useful for
constructing fixed-target marginal costs under uniform initialization.
It is a genuine difference of expected hitting times, not a surrogate.
-/

/-- The gain in the exact RLS fixed-target expectation when the allowed
zero count is raised from `r` to `s`, both below the initial zero count. -/
theorem proposed_rlsLinear_fixedTarget_thresholdDifference
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (r s : Nat) (x : BitString n)
    (hrs : r ≤ s) (hs : s ≤ zeroCount x) :
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal -
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) s) x).toReal =
      (n : Real) * (harmonicReal s - harmonicReal r) := by
  have hr : r ≤ zeroCount x := hrs.trans hs
  rw [proposed_rlsLinear_fixedTarget_runtimeReal_eq_truncatedHarmonic
        hn w hw r x hr,
      proposed_rlsLinear_fixedTarget_runtimeReal_eq_truncatedHarmonic
        hn w hw s x hs]
  ring

end ECRuntime
