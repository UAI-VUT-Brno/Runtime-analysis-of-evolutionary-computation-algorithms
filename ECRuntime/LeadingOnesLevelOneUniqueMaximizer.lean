import Mathlib

namespace ECRuntime

/-! P01: the first genuinely nonlinear local exit mass has a provable
strict equality case. This is a base case for Stage 411, not a replacement
for its all-level uniqueness assertion. -/

/-- If the level-one exit mass attains its optimum, the rate is one-half. -/
theorem proposed_leadingOnes_levelOne_exit_uniqueMaximizer
    (p : Real) (heq : p * (1 - p) = (1 / (2 : Real)) * (1 - 1 / (2 : Real))) :
    p = 1 / (2 : Real) := by
  have hsq : (p - (1 / 2 : Real)) * (p - (1 / 2 : Real)) = 0 := by
    nlinarith [heq]
  rcases mul_eq_zero.mp hsq with hz | hz
  · linarith
  · linarith

end ECRuntime
