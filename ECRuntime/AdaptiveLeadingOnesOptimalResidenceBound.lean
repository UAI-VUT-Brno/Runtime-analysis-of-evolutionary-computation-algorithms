import ECRuntime.AdaptiveLeadingOnesLocalOptimalRate
import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import Mathlib

namespace ECRuntime

/-!
Stage 192: new statement, not yet approved.

Bottcher--Doerr--Neumann local-rate track. Stage 178 maximizes one-step
LeadingOnes exit mass at rate p_i = 1/(i+1). Since the conditional mean
residence is the reciprocal of the exit mass, that gives the *minimum
conditional residence* at a visited level. This does not imply global
policy optimality without a policy-invariant visitation law.
-/

/-- The reciprocal exit mass under the locally optimal schedule is no
larger than under any admissible positive rate at the same level. -/
theorem proposed_leadingOnesAdaptive_optimalLocalResidenceBound
    (i : Nat) (p : Real) (hp : 0 < p) (hplt : p < 1) :
    (leadingOnesLocallyOptimalSchedule i *
        (1 - leadingOnesLocallyOptimalSchedule i) ^ i)⁻¹ ≤
      (p * (1-p)^i)⁻¹ := by
  have hbasep : 0 < 1-p := by linarith
  have hq : 0 < p * (1-p)^i :=
    mul_pos hp (pow_pos hbasep _)
  have hopt0 : 0 < leadingOnesLocallyOptimalSchedule i :=
    (proposed_leadingOnesAdaptive_localSchedule_admissible i).1
  have hopt1 : 0 ≤ 1-leadingOnesLocallyOptimalSchedule i := by
    linarith [(proposed_leadingOnesAdaptive_localSchedule_admissible i).2]
  have hoptq : 0 < leadingOnesLocallyOptimalSchedule i *
      (1-leadingOnesLocallyOptimalSchedule i)^i := by
    by_cases hi : i = 0
    · subst i
      simpa using hopt0
    · have hip : 0 < i := Nat.pos_of_ne_zero hi
      have hstrict : leadingOnesLocallyOptimalSchedule i < 1 := by
        unfold leadingOnesLocallyOptimalSchedule
        have hden : (1 : Real) < ((i+1 : Nat) : Real) := by
          have : 1 < i+1 := by omega
          exact_mod_cast this
        have hposden : (0 : Real) < ((i+1 : Nat) : Real) := by positivity
        rw [← one_div]
        exact (div_lt_iff₀ hposden).2 (by linarith)
      exact mul_pos hopt0 (pow_pos (by linarith) _)
  have hqle : p * (1-p)^i ≤
      leadingOnesLocallyOptimalSchedule i *
        (1-leadingOnesLocallyOptimalSchedule i)^i := by
    simpa only [leadingOnesLocallyOptimalSchedule] using
      proposed_leadingOnesAdaptive_localExitOptimality i p hp.le hplt.le
  have hInv :
      1 / (leadingOnesLocallyOptimalSchedule i *
        (1 - leadingOnesLocallyOptimalSchedule i)^i) ≤
      1 / (p * (1-p)^i) := by
    apply (div_le_div_iff₀ hoptq hq).2
    simpa only [one_mul] using hqle
  simpa only [one_div] using hInv

end ECRuntime
