import ECRuntime.LeadingOnesFixedTargetCurvatureFormula
import Mathlib

namespace ECRuntime

/-! Stage 240, proposed, NOT APPROVED.
An independent fixed-target corollary: the exact second difference from
Stage 236 is strictly positive for every interior mutation probability. -/

/-- The uniformly initialized LeadingOnes fixed-target mean has positive
second finite differences wherever they are defined. -/
theorem proposed_leadingOnes_uniformFixedTarget_positiveCurvature
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k + 2 ≤ n) :
    0 < (leadingOnesUniformFixedTargetMean n p (k + 2) -
          leadingOnesUniformFixedTargetMean n p (k + 1)) -
        (leadingOnesUniformFixedTargetMean n p (k + 1) -
          leadingOnesUniformFixedTargetMean n p k) := by
  rw [proposed_leadingOnes_uniformFixedTarget_curvatureFormula hp0 hp1 k hk]
  exact mul_pos (by norm_num : (0 : Real) < 1 / 2)
    (inv_pos.mpr (pow_pos (by linarith : 0 < 1 - p) (k + 1)))

end ECRuntime
