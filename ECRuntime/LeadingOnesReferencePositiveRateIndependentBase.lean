import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import Mathlib

namespace ECRuntime

/-! P01: positive-level optimal rates are independent of the level-zero
boundary parameter. This is the algebraic independence needed for a
rigorous decomposition of the full-runtime boundary limit. -/

/-- Every strictly positive reference level has the same exit-optimal rate,
independently of the reference schedule's initial mutation parameter. -/
theorem proposed_leadingOnes_referencePositiveRate_independentBase
    (a b : Real) (j : Nat) (hj : 0 < j) :
    proposed_leadingOnes_referenceOptimalRate a j =
      proposed_leadingOnes_referenceOptimalRate b j := by
  have hj0 : j ≠ 0 := Nat.ne_of_gt hj
  simp [proposed_leadingOnes_referenceOptimalRate, hj0]

end ECRuntime
