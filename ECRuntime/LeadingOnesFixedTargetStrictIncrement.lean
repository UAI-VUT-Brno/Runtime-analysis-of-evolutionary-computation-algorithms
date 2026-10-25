import ECRuntime.LeadingOnesFixedTargetIncrement
import Mathlib

namespace ECRuntime

/-!
# Stage 183 pending: strict mean-runtime growth at a fixed target

Source: Buzdalov--Doerr--Doerr--Vinokurov, fixed-target runtime.
The certified exact target increment is strictly positive for every
nondegenerate mutation probability and every admissible target below n.
This strengthens the certified non-strict target monotonicity and is
restricted to the already-formalized uniformly initialized (1+1)-EA.

The user approved this theorem header in the proof-9 follow-up; promotion still requires all official checks.
-/

/-- For p in (0,1), increasing an attainable LeadingOnes target by one
strictly increases its uniformly initialized expected hitting time. -/
theorem proposed_leadingOnes_uniformFixedTarget_mean_strictIncrement
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k < n) :
    leadingOnesUniformFixedTargetMean n p k <
      leadingOnesUniformFixedTargetMean n p (k + 1) := by
  rw [proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 k hk]
  have hbase : 0 < 1 - p := by linarith
  have hq : 0 < p * (1 - p) ^ k :=
    mul_pos hp0 (pow_pos hbase k)
  have hpos : 0 < (1 / 2 : Real) * (p * (1 - p) ^ k)⁻¹ :=
    mul_pos (by norm_num) (inv_pos.mpr hq)
  linarith

end ECRuntime
