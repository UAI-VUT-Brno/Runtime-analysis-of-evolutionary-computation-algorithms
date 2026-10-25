import ECRuntime.AdaptiveLeadingOnesRowScheduleLocal
import Mathlib

namespace ECRuntime

section RuntimeDecidability
attribute [local instance] Classical.propDecidable

/-!
Stage 215 (NEW, unapproved): propagate kernel equality to the generic
extended-real first-hitting-time functional. No positivity or boundedness of
rates is required for this syntactic kernel-equality result. It does not
establish global optimality when schedules differ at reachable levels.
-/

/-- Adaptive schedules agreeing at every reachable score yield identical
`runtimeSup` values for any target and any initial state. -/
theorem proposed_leadingOnesAdaptive_runtimeSup_scheduleExt
    {n : Nat} (rate rate' : Nat → Real)
    (hagree : ∀ i : Nat, i ≤ n → rate i = rate' i)
    (target : Set (BitString n)) (x : BitString n) :
    runtimeSup (leadingOnesAdaptiveTransition rate) target x =
      runtimeSup (leadingOnesAdaptiveTransition rate') target x := by
  have hkernel :
      leadingOnesAdaptiveTransition (n := n) rate =
        leadingOnesAdaptiveTransition rate' := by
    funext y z
    exact proposed_leadingOnesAdaptive_transitionRow_scheduleLocal
      rate rate' y z (hagree (leadingOnes y) (leadingOnes_le y))
  rw [hkernel]

end RuntimeDecidability

end ECRuntime
