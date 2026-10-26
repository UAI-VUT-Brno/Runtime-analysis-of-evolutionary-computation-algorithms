import ECRuntime.GenericSelfLoopSurvivalPower
import ECRuntime.GenericEASelfLoopFromEmptyMask
import Mathlib

attribute [local instance] Classical.propDecidable

namespace ECRuntime

/-! P07. Once the generic finite-state theorem is promoted, a general
objective-independent fixed-target result follows by instantiation. -/

/-- For any target and any elitist standard-bit-mutation objective, the
no-mutation path gives a geometric lower bound on target survival. -/
theorem proposed_onePlusOne_genericAnyTargetSurvival_ge_noFlipPower
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fitness : BitString n → Real) (target : Set (BitString n))
    (x : BitString n) (hx : x ∉ target) (t : Nat) :
    ((1 - p) ^ n) ^ t ≤
      finiteLevelSurvival (onePlusOneTransition p fitness) targetᶜ t x := by
  classical
  exact proposed_finiteLevelSurvival_ge_selfLoopPower
    (onePlusOneTransition p fitness)
    (onePlusOneTransition_stochastic hp0 hp1 fitness)
    targetᶜ x hx ((1 - p) ^ n)
    (pow_nonneg (sub_nonneg.mpr hp1) n)
    (proposed_onePlusOne_selfTransition_ge_emptyMask p hp0 hp1 fitness x) t

end ECRuntime
