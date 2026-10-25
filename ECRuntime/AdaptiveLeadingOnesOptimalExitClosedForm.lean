import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

namespace ECRuntime

/-!
Stage 198 (PROPOSED, unapproved): an explicit algebraic expression for the
optimal level-exit mass of fitness-dependent LeadingOnes mutation. This
supports quantitative global-runtime comparisons, but alone does not prove
that level entry probabilities are schedule independent.
-/

/-- At level `i`, the locally optimal scheduled exit mass is
`i^i/(i+1)^(i+1)` (with the usual convention `0^0 = 1`). -/
theorem proposed_leadingOnesAdaptive_optimalExitMass_closedForm (i : Nat) :
    leadingOnesLocallyOptimalSchedule i *
        (1 - leadingOnesLocallyOptimalSchedule i)^i =
      (i : Real)^i / ((i + 1 : Nat) : Real)^(i+1) := by
  unfold leadingOnesLocallyOptimalSchedule
  simp only [← one_div]
  have hd : (((i + 1 : Nat) : Real)) ≠ 0 := by positivity
  have hdcast : (((i + 1 : Nat) : Real)) = (i : Real) + 1 := by
    push_cast
    ring
  have hsub : 1 - 1 / (((i + 1 : Nat) : Real)) =
      (i : Real) / (((i + 1 : Nat) : Real)) := by
    rw [hdcast]
    have hne : (i : Real) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hsub, div_pow]
  field_simp [pow_succ, hd]
  ring

end ECRuntime
