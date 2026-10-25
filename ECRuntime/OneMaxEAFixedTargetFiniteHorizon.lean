import ECRuntime.GenericTargetRuntimeAntitonicity
import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import Mathlib

namespace ECRuntime
/-! P07. Multi-bit (1+1)-EA OneMax fixed-target finite horizon
comparison, with the necessary stochastic-rate assumptions. -/
theorem proposed_oneMaxEA_finiteHorizonRuntime_antitone_threshold
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Nat) (hrs : r ≤ s) (horizon : Nat) (x : BitString n) :
    finiteHorizonRuntime (onePlusOneTransition p (oneMaxReal (n := n)))
      (oneMaxEAZeroAtMost (n := n) s) horizon x ≤
    finiteHorizonRuntime (onePlusOneTransition p (oneMaxReal (n := n)))
      (oneMaxEAZeroAtMost (n := n) r) horizon x := by
  exact proposed_finiteHorizonRuntime_antitone_target
    (onePlusOneTransition p (oneMaxReal (n := n)))
    (onePlusOneTransition_stochastic hp0 hp1 (oneMaxReal (n := n)))
    (oneMaxEAZeroAtMost (n := n) r) (oneMaxEAZeroAtMost (n := n) s)
    (by intro y hy; exact le_trans hy hrs) horizon x
end ECRuntime
