import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

namespace ECRuntime

/-! Stage 242 (new, pending approval).
The levelwise optimum p_i = 1/(i+1) is *not* strictly interior at
level zero. It is interior at every positive score. Distinguishing
these cases is necessary before invoking the certified visitation
law (which assumes strictly interior rates at all scores). -/

/-- The locally optimal adaptive LeadingOnes rate lies strictly between
zero and one on each strictly positive level. -/
theorem proposed_leadingOnesAdaptive_optimalPositiveLevelRate_strict
    (i : Nat) (hi : 0 < i) :
    0 < leadingOnesLocallyOptimalSchedule i ∧
      leadingOnesLocallyOptimalSchedule i < 1 := by
  constructor
  · exact (proposed_leadingOnesAdaptive_localSchedule_admissible i).1
  · unfold leadingOnesLocallyOptimalSchedule
    have hden : (1 : Real) < ((i + 1 : Nat) : Real) := by
      have hn : 1 < i + 1 := by omega
      exact_mod_cast hn
    have hpos : (0 : Real) < ((i + 1 : Nat) : Real) := by positivity
    rw [← one_div]
    exact (div_lt_iff₀ hpos).2 (by linarith)

end ECRuntime
