import ECRuntime.LeadingOnesFixedTargetIncrement
import Mathlib

namespace ECRuntime

/-! Stage 248 (P07, approved statement; proof-33 algebraic repair).
The marginal expected cost of increasing a fixed LeadingOnes target
by one fitness level grows by the exact factor 1/(1-p). It follows
from the promoted first-increment law and complements the certified
curvature ratio, without extending the result to other algorithms. -/

/-- Consecutive marginal increments of the uniform-start fixed-target
LeadingOnes expectation form a geometric sequence. -/
theorem proposed_leadingOnes_uniformFixedTarget_marginalGeometricRatio
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k + 2 ≤ n) :
    (leadingOnesUniformFixedTargetMean n p (k + 2) -
        leadingOnesUniformFixedTargetMean n p (k + 1)) =
      (1 - p)⁻¹ *
        (leadingOnesUniformFixedTargetMean n p (k + 1) -
          leadingOnesUniformFixedTargetMean n p k) := by
  have hk0 : k < n := by omega
  have hk1 : k + 1 < n := by omega
  have h0 := proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 k hk0
  have h1 := proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 (k + 1) hk1
  -- Separate the two marginal increments before simplifying the inverse.
  -- The previous `ring` proof left an inverse-power goal unsolved.
  have hfirst :
      leadingOnesUniformFixedTargetMean n p (k + 1) -
        leadingOnesUniformFixedTargetMean n p k =
          (1 / 2 : Real) * (p * (1 - p) ^ k)⁻¹ := by
    rw [h0]
    ring
  have hsecond :
      leadingOnesUniformFixedTargetMean n p (k + 2) -
        leadingOnesUniformFixedTargetMean n p (k + 1) =
          (1 / 2 : Real) * (p * (1 - p) ^ (k + 1))⁻¹ := by
    rw [show k + 2 = k + 1 + 1 by omega, h1]
    ring
  have hratio :
      (p * (1 - p) ^ (k + 1))⁻¹ =
        (1 - p)⁻¹ * (p * (1 - p) ^ k)⁻¹ := by
    calc
      (p * (1 - p) ^ (k + 1))⁻¹ =
          ((p * (1 - p) ^ k) * (1 - p))⁻¹ := by
        rw [pow_succ]
        congr 1
        ring
      _ = (1 - p)⁻¹ * (p * (1 - p) ^ k)⁻¹ := mul_inv_rev _ _
  rw [hfirst, hsecond, hratio]
  ring

end ECRuntime
