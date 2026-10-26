import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 293 (P07, proposed). The admissible-rate multi-bit-mutation EA
fixed-target comparison survives arbitrary nonnegative initial weights.
Extended nonnegative expectations allow infinite runtimes.
-/

/-- Weighted fixed-target dominance for the genuine OneMax (1+1)-EA. -/
theorem proposed_oneMaxEA_weightedRuntimeSup_antitone_threshold_admissible
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Nat) (hrs : r ≤ s) (w : BitString n → ENNReal) :
    (∑ x : BitString n, w x *
      runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
        (oneMaxEAZeroAtMost (n := n) s) x) ≤
    (∑ x : BitString n, w x *
      runtimeSup (onePlusOneTransition p (oneMaxReal (n := n)))
        (oneMaxEAZeroAtMost (n := n) r) x) := by
  apply Finset.sum_le_sum
  intro x _hx
  exact mul_le_mul_right
    (proposed_oneMaxEA_runtimeSup_antitone_threshold_admissible
      p hp0 hp1 r s hrs x) (w x)

end ECRuntime
