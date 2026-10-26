import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 213: NEW proposed schedule-local transition-row equality, supporting
future adaptive LeadingOnes level-entry and suffix-distribution arguments.
It asserts only equality of the *current-state rows* when scheduled rates
agree at that state's score. It does not claim equal global trajectory laws
or a uniform distribution of visited levels. Approval remains pending.
-/

/-- Two adaptive mutation schedules choosing the same rate at the current
LeadingOnes score induce identical one-step distributions from that state. -/
theorem proposed_leadingOnesAdaptive_transitionRow_scheduleLocal
    {n : Nat} (rate rate' : Nat → Real) (x y : BitString n)
    (heq : rate (leadingOnes x) = rate' (leadingOnes x)) :
    leadingOnesAdaptiveTransition rate x y =
      leadingOnesAdaptiveTransition rate' x y := by
  change
    onePlusOneTransition (rate (leadingOnes x))
        (leadingOnesReal (n := n)) x y =
    onePlusOneTransition (rate' (leadingOnes x))
        (leadingOnesReal (n := n)) x y
  rw [heq]

end ECRuntime
