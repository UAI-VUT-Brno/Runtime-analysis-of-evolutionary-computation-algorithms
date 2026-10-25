import ECRuntime.LeadingOnesFixedTargetCandidate
import Mathlib

namespace ECRuntime

/-!
# Stage 181 pending: dimension invariance below a fixed LeadingOnes target

Source direction: Buzdalov--Doerr--Doerr--Vinokurov, fixed-target runtime.
For target k and mutation probability p, once n >= k, the exact
uniform-start expected time of the fixed-rate (1+1)-EA does not depend
on the number of suffix coordinates beyond that target. This is specific
to the certified LeadingOnes model and its uniform initialization.

The statement is new and requires separate human approval.
-/

/-- For dimensions n and m that both admit threshold k, the certified
uniform-start fixed-target expectations agree. -/
theorem proposed_leadingOnes_uniformFixedTarget_mean_dimensionInvariant
    {n m k : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (hkn : k <= n) (hkm : k <= m) :
    leadingOnesUniformFixedTargetMean n p k =
      leadingOnesUniformFixedTargetMean m p k := by
  rw [proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 k hkn,
      proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 k hkm]

end ECRuntime
