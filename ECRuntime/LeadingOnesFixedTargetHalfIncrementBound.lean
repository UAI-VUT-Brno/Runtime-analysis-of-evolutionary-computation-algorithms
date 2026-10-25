import ECRuntime.LeadingOnesFixedTargetIncrement
import Mathlib

namespace ECRuntime

/-!
# Stage 185 proposal: dimension-free lower bound on a fixed-target increment

Source direction: Buzdalov--Doerr--Doerr--Vinokurov, fixed-target runtime.
The Stage 177 exact increment is at least 1/2 for every interior mutation
probability, regardless of dimension or target. This claim is independent of
Stage 183's strict monotonicity statement. The theorem header is unapproved.
-/

/-- Each additional LeadingOnes target level costs at least one half expected
iteration under the uniformly initialized (1+1)-EA, for `0 < p < 1`. -/
theorem proposed_leadingOnes_uniformFixedTarget_increment_atLeastHalf
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k < n) :
    leadingOnesUniformFixedTargetMean n p k + (1 / 2 : Real) ≤
      leadingOnesUniformFixedTargetMean n p (k + 1) := by
  have hnonneg : 0 ≤ 1 - p := by linarith
  have hle : 1 - p ≤ (1 : Real) := by linarith
  have hpow : (1 - p) ^ k ≤ (1 : Real) := by
    simpa using (pow_le_pow_left₀ hnonneg hle k)
  have hpowpos : 0 < (1 - p) ^ k := pow_pos (by linarith) k
  have hqpos : 0 < p * (1 - p) ^ k := mul_pos hp0 hpowpos
  have hqle : p * (1 - p) ^ k ≤ 1 := by
    have hpbound := mul_le_mul_of_nonneg_left hpow hp0.le
    nlinarith
  have hinv : (1 : Real) ≤ (p * (1 - p) ^ k)⁻¹ := by
    have h : (1 : Real) ≤ 1 / (p * (1 - p) ^ k) := by
      apply (le_div_iff₀ hqpos).2
      simpa only [one_mul] using hqle
    simpa only [one_div] using h
  rw [proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 k hk]
  nlinarith

end ECRuntime
