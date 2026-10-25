import ECRuntime.LeadingOnesFixedTargetMeanMonotone
import ECRuntime.LeadingOnesFixedTargetOneMean
import Mathlib

namespace ECRuntime

/-!
Stage 201 (human-approved in proof-16 follow-up): extend the exact first-target expectation to a
uniform lower bound at every strictly positive fixed target. Uses existing
certified monotonicity and exact boundary formula; no new stochastic
assumption, no general-algorithm claim.
-/

/-- Every positive LeadingOnes target requires at least the initial
one-level expected waiting time under uniform initialization. -/
theorem proposed_leadingOnes_uniformFixedTarget_atLeastFirstLevel
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : 1 <= k) (hkn : k <= n) :
    (1 / 2 : Real) * p⁻¹ <= leadingOnesUniformFixedTargetMean n p k := by
  calc
    (1 / 2 : Real) * p⁻¹ = leadingOnesUniformFixedTargetMean n p 1 :=
      (proposed_leadingOnes_uniformFixedTarget_oneMean hp0 hp1
        (hk.trans hkn)).symm
    _ <= leadingOnesUniformFixedTargetMean n p k :=
      proposed_leadingOnes_uniformFixedTarget_mean_monotoneTarget
        hp0 hp1 1 k hk hkn

end ECRuntime
