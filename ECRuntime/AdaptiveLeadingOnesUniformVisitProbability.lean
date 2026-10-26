import ECRuntime.AdaptiveLeadingOnesFirstCrossingTotalMass
import ECRuntime.AdaptiveLeadingOnesNormalizedExactEntryHalf
import ECRuntime.AdaptiveLeadingOnesFirstCrossingNormalization
import Mathlib

namespace ECRuntime

/-! Stage 234: global adaptive level-entry probability.
This is *not* implied solely by conditional residence optimality. -/

/-- Uniform-start probability mass of visiting a particular nonterminal LeadingOnes level. -/
theorem proposed_leadingOnesAdaptive_eventualExactEntry_half
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate i = (1 / 2 : ENNReal) := by
  exact proposed_leadingOnesAdaptive_exactEntryHalf_of_total_one rate i
    (proposed_leadingOnesAdaptive_firstCrossingTotal_eq_one rate hrate i)

end ECRuntime
