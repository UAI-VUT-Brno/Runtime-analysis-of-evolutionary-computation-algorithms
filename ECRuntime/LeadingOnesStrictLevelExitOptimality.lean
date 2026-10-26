import ECRuntime.LeadingOnesPerLevelExitOptimality
import ECRuntime.AdaptiveLeadingOnesUniquePositiveLevelOptimizer
import Mathlib

namespace ECRuntime

/-! P01: a strict local exit-rate inequality off the unique optimizer.
This is a genuine downstream consequence of Stage 411. -/

/-- Every nonoptimal positive-level rate has strictly smaller exit mass. -/
theorem proposed_leadingOnes_positiveLevelExit_lt_optimal_of_ne
    (j : Nat) (hj : 0 < j) (p : Real)
    (hp0 : 0 <= p) (hp1 : p <= 1)
    (hne : p ≠ 1 / ((j + 1 : Nat) : Real)) :
    p * (1 - p) ^ j <
      (1 / ((j + 1 : Nat) : Real)) *
        (1 - 1 / ((j + 1 : Nat) : Real)) ^ j := by
  have hle := proposed_leadingOnes_levelExitMass_le_optimal j hj p hp0 hp1
  have hneMass : p * (1 - p) ^ j ≠
      (1 / ((j + 1 : Nat) : Real)) *
        (1 - 1 / ((j + 1 : Nat) : Real)) ^ j := by
    intro h
    exact hne (proposed_leadingOnes_positiveLevelExit_uniqueMaximizer
      j hj p hp0 hp1 h)
  exact lt_of_le_of_ne hle hneMass

end ECRuntime
