import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesLocallyOptimalScheduleAdmissible
import ECRuntime.AdaptiveLeadingOnesOptimalExitClosedForm
import Mathlib

namespace ECRuntime

/-!
Stage 202 (new, awaiting human statement approval).
A direct instantiation of the *certified* level-residence survival law at the
locally optimal adaptive schedule. This says nothing about the chance that a
trajectory visits the level in the first place.
-/

/-- When a level is already occupied, the locally optimal schedule gives the
exact geometric survival law with exit mass `i^i/(i+1)^(i+1)`. -/
theorem proposed_leadingOnesAdaptive_optimalSchedule_levelSurvival
    {n : Nat} (i : Fin n) (t : Nat) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    finiteLevelSurvival
        (leadingOnesAdaptiveTransition leadingOnesLocallyOptimalSchedule)
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) t x =
      (1 - (i.val : Real)^i.val / (((i.val + 1 : Nat) : Real)^(i.val+1)))^t := by
  have hrate : ∀ j : Nat, j ≤ n →
      0 ≤ leadingOnesLocallyOptimalSchedule j ∧
      leadingOnesLocallyOptimalSchedule j ≤ 1 := by
    intro j _hj
    obtain ⟨hpos, hle⟩ :=
      proposed_leadingOnesAdaptive_localSchedule_admissible j
    exact ⟨hpos.le, hle⟩
  rw [proposed_leadingOnesAdaptive_exactLevel_survival
      leadingOnesLocallyOptimalSchedule hrate i t x hlevel,
      proposed_leadingOnesAdaptive_optimalExitMass_closedForm]

end ECRuntime
