import ECRuntime.AdaptiveLeadingOnesFirstCrossingTotalMass
import Mathlib

namespace ECRuntime

/-! Stage 232: conditional normalization-to-one-half bridge.
This does not assume normalization and cannot replace Stage 225. -/

/-- If eventual first-crossing mass is one, the exact-entry branch has half mass. -/
theorem proposed_leadingOnesAdaptive_exactEntryHalf_of_total_one
    {n : Nat} (rate : Nat → Real) (i : Fin n)
    (hnorm : leadingOnesAdaptiveEventualFirstCrossingTotalMass rate i = 1) :
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate i = (1 / 2 : ENNReal) := by
  rw [proposed_leadingOnesAdaptive_eventualFirstCrossingTotal_eq_twiceExact] at hnorm
  have hcancel : (2 : ENNReal)⁻¹ * (2 : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate i =
        (1 : ENNReal) * leadingOnesAdaptiveEventualFirstCrossingExactMass rate i := by
      simp
    _ = (2 : ENNReal)⁻¹ *
        ((2 : ENNReal) * leadingOnesAdaptiveEventualFirstCrossingExactMass rate i) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ = (2 : ENNReal)⁻¹ * 1 := by rw [hnorm]
    _ = (1 / 2 : ENNReal) := by simp [one_div]

end ECRuntime
