import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

namespace ECRuntime

/-!
Stage 190 (approved; full promotion pending): the levelwise locally optimal
mutation schedule defines a stochastic adaptive (1+1)-EA transition kernel.

This does not establish policy-level optimal expected runtime. In particular,
visitation probabilities across levels have not been proved invariant under
arbitrary fitness-dependent schedules.
-/

/-- The locally optimal schedule `p_i = 1/(i+1)` gives a stochastic kernel in
    every finite dimension, including the absorbing score `n`. -/
theorem proposed_leadingOnesAdaptive_optimalSchedule_stochastic
    {n : Nat} :
    IsStochastic (leadingOnesAdaptiveTransition (n := n)
      leadingOnesLocallyOptimalSchedule) := by
  apply proposed_leadingOnesAdaptive_transition_stochastic
    leadingOnesLocallyOptimalSchedule
  intro j _hj
  obtain ⟨hpos, hle⟩ := proposed_leadingOnesAdaptive_localSchedule_admissible j
  exact ⟨hpos.le, hle⟩

end ECRuntime
