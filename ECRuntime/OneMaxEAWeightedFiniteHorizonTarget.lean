import ECRuntime.OneMaxEAFixedTargetFiniteHorizon
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! P07: lift the stochastic-rate fixed-target multi-bit-mutation EA
comparison to arbitrary nonnegative initial-state weights at a finite horizon. -/

/-- For admissible bit-mutation rates, enlargement of the OneMax target
weakly decreases every nonnegative-weighted finite-horizon runtime. -/
theorem proposed_oneMaxEA_weightedFiniteHorizonRuntime_antitone_threshold
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r s : Nat) (hrs : r ≤ s) (horizon : Nat)
    (weights : BitString n → Real)
    (hw : ∀ x, 0 ≤ weights x) :
    (∑ x : BitString n, weights x *
      finiteHorizonRuntime (onePlusOneTransition p (oneMaxReal (n := n)))
        (oneMaxEAZeroAtMost (n := n) s) horizon x) ≤
    (∑ x : BitString n, weights x *
      finiteHorizonRuntime (onePlusOneTransition p (oneMaxReal (n := n)))
        (oneMaxEAZeroAtMost (n := n) r) horizon x) := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left
    (proposed_oneMaxEA_finiteHorizonRuntime_antitone_threshold
      p hp0 hp1 r s hrs horizon x) (hw x)

end ECRuntime
