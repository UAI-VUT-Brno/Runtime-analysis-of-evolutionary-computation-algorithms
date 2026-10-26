import ECRuntime.LeadingOnesFixedTargetCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 188 pending: explicit first positive fixed-target expectation, under
uniform initialization and independent-bit mutation. This is a boundary
specialization of the certified general finite-level mean formula.
-/

/-- In positive dimension, time to first leading one has mean 1/(2p). -/
theorem proposed_leadingOnes_uniformFixedTarget_oneMean
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) :
    leadingOnesUniformFixedTargetMean n p 1 = (1 / 2 : Real) * p⁻¹ := by
  rw [proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 1 hn]
  simp

end ECRuntime
