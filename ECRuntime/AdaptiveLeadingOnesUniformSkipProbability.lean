import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import ECRuntime.AdaptiveLeadingOnesEventualCrossingParity
import Mathlib

namespace ECRuntime

/-! Stage 238 (pending statement approval): the complementary strict-skip
half mass under uniform initialization and a strictly interior adaptive
mutation schedule. This completes the two-branch entry distribution. -/

/-- Under a strictly interior adaptive mutation schedule, a fixed
nonterminal LeadingOnes level is strictly skipped with probability one half. -/
theorem proposed_leadingOnesAdaptive_eventualStrictSkip_half
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingSkipMass rate i = (1 / 2 : ENNReal) := by
  rw [← proposed_leadingOnesAdaptive_eventualFirstCrossingExactMass_eq_skipMass
    rate i]
  exact proposed_leadingOnesAdaptive_eventualExactEntry_half rate hrate i

end ECRuntime
