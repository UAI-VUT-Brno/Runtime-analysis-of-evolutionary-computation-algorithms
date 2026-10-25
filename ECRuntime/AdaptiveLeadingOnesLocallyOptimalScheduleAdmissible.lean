import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 187 pending: admissibility of the levelwise candidate schedule from
Böttcher--Doerr--Neumann. This elementary local statement is a necessary
input for instantiating the adaptive stochastic kernel; it does not establish
an optimal expected runtime or a level-visitation theorem.
-/

/-- Candidate rate schedule p_i = 1/(i+1), defined also for i=n. -/
noncomputable def leadingOnesLocallyOptimalSchedule (i : Nat) : Real :=
  (((i + 1 : Nat) : Real))⁻¹

/-- Every prescribed rate lies in (0,1], even at the terminal level. -/
theorem proposed_leadingOnesAdaptive_localSchedule_admissible
    (i : Nat) :
    0 < leadingOnesLocallyOptimalSchedule i ∧
      leadingOnesLocallyOptimalSchedule i ≤ 1 := by
  unfold leadingOnesLocallyOptimalSchedule
  constructor
  · positivity
  · have hpos : (0 : Real) < ((i + 1 : Nat) : Real) := by positivity
    have hone : (1 : Real) ≤ ((i + 1 : Nat) : Real) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i))
    rw [← one_div]
    exact (div_le_iff₀ hpos).2 (by simpa only [one_mul] using hone)

end ECRuntime
