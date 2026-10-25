import ECRuntime.AdaptiveLeadingOnesRowScheduleLocal
import Mathlib

namespace ECRuntime

/-!
Stage 214 (NEW, unapproved): whole-kernel extensionality for two adaptive
LeadingOnes schedules that agree at every attainable score in dimension `n`.
The theorem is a direct reuse of the approved Stage 213 row-locality lemma.
It does not compare unequal schedules or imply optimal policy behavior.
-/

/-- In a fixed dimension, the adaptive transition matrix depends only on
mutation rates at scores `0,...,n`, including the terminal score `n`. -/
theorem proposed_leadingOnesAdaptive_kernel_scheduleExt
    {n : Nat} (rate rate' : Nat → Real)
    (hagree : ∀ i : Nat, i ≤ n → rate i = rate' i) :
    leadingOnesAdaptiveTransition (n := n) rate =
      leadingOnesAdaptiveTransition rate' := by
  funext x y
  exact proposed_leadingOnesAdaptive_transitionRow_scheduleLocal
    rate rate' x y (hagree (leadingOnes x) (leadingOnes_le x))

end ECRuntime
