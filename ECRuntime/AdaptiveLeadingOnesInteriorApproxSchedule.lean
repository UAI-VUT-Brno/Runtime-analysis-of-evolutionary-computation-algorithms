import ECRuntime.AdaptiveLeadingOnesOptimalPositiveLevelRate
import Mathlib

namespace ECRuntime

/-! Stage 243 (new, pending approval).
An explicitly interior epsilon perturbation of the score-wise optimal
schedule. This removes the p_0 = 1 boundary obstruction for applying
the certified adaptive visitation theorem. The limit eps -> 0 and
the genuine expected-runtime identity are separate obligations. -/

/-- An interior approximation to the boundary-optimal adaptive mutation schedule. -/
noncomputable def leadingOnesInteriorApproxSchedule (eps : Real) (i : Nat) : Real :=
  if i = 0 then 1 - eps else leadingOnesLocallyOptimalSchedule i

/-- For 0 < eps < 1 the perturbed optimal schedule is strictly admissible
on *all* scores, including score zero. -/
theorem proposed_leadingOnesAdaptive_interiorApproxSchedule_admissible
    (eps : Real) (heps0 : 0 < eps) (heps1 : eps < 1)
    (i : Nat) :
    0 < leadingOnesInteriorApproxSchedule eps i ∧
      leadingOnesInteriorApproxSchedule eps i < 1 := by
  by_cases hi : i = 0
  · subst i
    simp only [leadingOnesInteriorApproxSchedule, ↓reduceIte]
    constructor <;> linarith
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    simpa only [leadingOnesInteriorApproxSchedule, if_neg hi] using
      proposed_leadingOnesAdaptive_optimalPositiveLevelRate_strict i hip

end ECRuntime
