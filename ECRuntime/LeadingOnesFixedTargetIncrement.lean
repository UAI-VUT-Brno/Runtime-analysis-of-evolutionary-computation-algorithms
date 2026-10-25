import ECRuntime.LeadingOnesFixedTargetCandidate
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 177 (P07): exact marginal cost of a higher LeadingOnes target

The theorem header is approved in proof-7.  The proof uses only the certified Stage
169 full intermediate-target formula, not a new assumption on suffix bits.
It is a target-to-target marginal law for the same (1+1)-EA model, not a
claim about arbitrary EA mutation operators or initial distributions.
This file stays isolated until the official promotion gates pass.
-/

/-- Raising the LeadingOnes target from `k` to `k+1` adds precisely the
expected contribution from score level `k` under uniform initialization. -/
theorem proposed_leadingOnes_uniformFixedTarget_increment
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k < n) :
    leadingOnesUniformFixedTargetMean n p (k + 1) =
      leadingOnesUniformFixedTargetMean n p k +
        (1 / 2 : Real) * (p * (1 - p) ^ k)⁻¹ := by
  have hk' : k ≤ n := Nat.le_of_lt hk
  have hks : k + 1 ≤ n := by omega
  rw [proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 (k + 1) hks,
    proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 k hk',
    Finset.sum_range_succ]
  ring

end ECRuntime
