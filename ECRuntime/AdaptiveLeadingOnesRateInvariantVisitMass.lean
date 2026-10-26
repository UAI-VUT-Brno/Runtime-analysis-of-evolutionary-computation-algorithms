import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import Mathlib

namespace ECRuntime

/-! Stage 241, proposed, NOT APPROVED.
The uniform-initialization exact-entry mass at a fixed nonterminal level
is invariant under a change between any two strictly interior fitness-
dependent mutation schedules. The result follows from Stage 234, if and
only if that normalization theorem has been certified. -/

/-- Two strictly interior adaptive schedules have the same total mass of
first exact entries at a specified LeadingOnes level. -/
theorem proposed_leadingOnesAdaptive_exactEntryRateInvariant
    {n : Nat} (rate₁ rate₂ : Nat → Real)
    (h₁ : ∀ j : Nat, j ≤ n → 0 < rate₁ j ∧ rate₁ j < 1)
    (h₂ : ∀ j : Nat, j ≤ n → 0 < rate₂ j ∧ rate₂ j < 1)
    (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate₁ i =
      leadingOnesAdaptiveEventualFirstCrossingExactMass rate₂ i := by
  rw [proposed_leadingOnesAdaptive_eventualExactEntry_half rate₁ h₁ i,
      proposed_leadingOnesAdaptive_eventualExactEntry_half rate₂ h₂ i]

end ECRuntime
