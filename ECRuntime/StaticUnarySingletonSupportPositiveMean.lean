import ECRuntime.StaticUnarySingletonSupportMeanRadius
import Mathlib

namespace ECRuntime

/-! P07: the singleton support reduction also propagates the precise
positivity required for lower-drift theorems. -/

/-- A positive one-bit mass gives positive mean radius under singleton support. -/
theorem proposed_staticUnary_singletonSupport_meanRadius_pos
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hone : 0 < law.oneBitMass)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1) :
    0 < law.meanRadius := by
  rw [proposed_staticUnary_singletonSupport_meanRadius_eq_oneBitMass law hsmall]
  exact hone

end ECRuntime
