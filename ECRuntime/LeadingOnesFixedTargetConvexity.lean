import ECRuntime.LeadingOnesFixedTargetIncrement
import Mathlib

namespace ECRuntime

/-!
Stage 230 (NEW, pending approval): discrete convexity of the
LeadingOnes fixed-target mean as the target rises. This belongs to the
Buzdalov--Doerr--Doerr--Vinokurov track and is independent of the
adaptive first-crossing proof chain.
-/

/-- Successive target increments are nondecreasing for an interior
mutation rate under uniform initialization. -/
theorem proposed_leadingOnes_uniformFixedTarget_discreteConvex
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k + 2 <= n) :
    leadingOnesUniformFixedTargetMean n p (k + 1) -
        leadingOnesUniformFixedTargetMean n p k <=
      leadingOnesUniformFixedTargetMean n p (k + 2) -
        leadingOnesUniformFixedTargetMean n p (k + 1) := by
  have hk0 : k < n := by omega
  have hk1 : k + 1 < n := by omega
  have hinc0 := proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 k hk0
  have hinc1 := proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 (k + 1) hk1
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hleft : 0 < p * (1 - p) ^ k :=
    mul_pos hp0 (pow_pos hq0 k)
  have hright : 0 < p * (1 - p) ^ (k + 1) :=
    mul_pos hp0 (pow_pos hq0 (k + 1))
  have hmass : p * (1 - p) ^ (k + 1) ≤ p * (1 - p) ^ k := by
    rw [pow_succ]
    calc
      p * ((1 - p) ^ k * (1 - p)) ≤ p * ((1 - p) ^ k * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hq1 (pow_nonneg hq0.le k)) hp0.le
      _ = p * (1 - p) ^ k := by ring
  have hinv : (p * (1 - p) ^ k)⁻¹ ≤
      (p * (1 - p) ^ (k + 1))⁻¹ := by
    have hdiv : (1 : Real) / (p * (1 - p) ^ k) ≤
        (1 : Real) / (p * (1 - p) ^ (k + 1)) :=
      (div_le_div_iff₀ hleft hright).2
        (by simpa only [one_mul] using hmass)
    simpa only [one_div] using hdiv
  have hfirst :
      leadingOnesUniformFixedTargetMean n p (k + 1) -
        leadingOnesUniformFixedTargetMean n p k =
      (1 / 2 : Real) * (p * (1 - p) ^ k)⁻¹ := by
    rw [hinc0]
    ring
  have hsecond :
      leadingOnesUniformFixedTargetMean n p (k + 2) -
        leadingOnesUniformFixedTargetMean n p (k + 1) =
      (1 / 2 : Real) * (p * (1 - p) ^ (k + 1))⁻¹ := by
    rw [hinc1]
    ring
  rw [hfirst, hsecond]
  exact mul_le_mul_of_nonneg_left hinv (by norm_num)

end ECRuntime
