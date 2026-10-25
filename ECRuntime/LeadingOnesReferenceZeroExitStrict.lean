import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import Mathlib

namespace ECRuntime

/-! P01: the strict level-zero component of boundary improvement.
Unlike the full-runtime comparison, this requires no ENNReal limit. -/

/-- Increasing the reference rate strictly increases its level-zero exit mass. -/
theorem proposed_leadingOnes_referenceZeroExit_strict
    (base1 base2 : Real) (h : base1 < base2) :
    proposed_leadingOnes_referenceOptimalRate base1 0 *
      (1 - proposed_leadingOnes_referenceOptimalRate base1 0) ^ 0 <
    proposed_leadingOnes_referenceOptimalRate base2 0 *
      (1 - proposed_leadingOnes_referenceOptimalRate base2 0) ^ 0 := by
  simpa [proposed_leadingOnes_referenceOptimalRate] using h

end ECRuntime
