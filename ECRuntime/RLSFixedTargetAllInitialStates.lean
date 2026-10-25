import ECRuntime.RLSFixedTargetRealBridge
import Mathlib

namespace ECRuntime

/-!
Stage 257 (P07, new proposal): complete the pointwise RLS fixed-target
identity for starts *already inside* the target as well as outside. This
is an exact genuine hitting-time result, and prepares the uniform-start
binomial average without introducing an initial-condition restriction.
-/

/-- Every finite-horizon runtime is zero when the start already belongs
to the target; consequently the unrestricted ENNReal runtime is zero. -/
private theorem stage257_runtimeSup_zero_of_mem
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun y => y ∈ target)]
    (x : alpha) (hx : x ∈ target) :
    runtimeSup P target x = 0 := by
  have hzero : ∀ t : Nat, finiteHorizonRuntime P target t x = 0 := by
    intro t
    cases t with
    | zero => exact finiteHorizonRuntime_zero P target x
    | succ t => exact finiteHorizonRuntime_succ_of_mem P target t x hx
  unfold runtimeSup
  simp only [hzero, ENNReal.ofReal_zero, iSup_const]

/-- Unrestricted RLS fixed-target expectation for every initial bit string:
zero inside the target and truncated harmonic cost above it. -/
theorem proposed_rlsLinear_fixedTarget_runtimeReal_allInitialStates
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (r : Nat) (x : BitString n) :
    (runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal =
      if zeroCount x ≤ r then 0
      else (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) := by
  by_cases htarget : zeroCount x ≤ r
  · have hx : x ∈ rlsZeroAtMost (n := n) r := htarget
    have hzero := stage257_runtimeSup_zero_of_mem
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x hx
    rw [hzero]
    simp [htarget]
  · have hr : r ≤ zeroCount x := by omega
    simpa only [if_neg htarget] using
      (proposed_rlsLinear_fixedTarget_runtimeReal_eq_truncatedHarmonic
        hn w hw r x hr)

end ECRuntime
