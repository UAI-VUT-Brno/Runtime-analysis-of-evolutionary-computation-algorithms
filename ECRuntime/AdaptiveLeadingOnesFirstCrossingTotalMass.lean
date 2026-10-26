import ECRuntime.AdaptiveLeadingOnesEventualCrossingParity
import Mathlib

namespace ECRuntime

/-!
Stage 221 (NEW, unapproved): algebraic splitting of the aggregate adaptive
first-crossing mass into two equal branches. This theorem is meaningful
without asserting that the aggregate mass is one. In particular, its
statement is valid even for degenerate schedules whose process never
reaches a given boundary from some initial states.
-/

/-- Aggregated mass of all adaptive first crossings (including time zero). -/
noncomputable def leadingOnesAdaptiveEventualFirstCrossingTotalMass
    {n : Nat} (rate : Nat -> Real) (i : Fin n) : ENNReal :=
  leadingOnesAdaptiveEventualFirstCrossingExactMass rate i +
    leadingOnesAdaptiveEventualFirstCrossingSkipMass rate i

/-- Each exact-entry branch contributes one of two equal aggregate masses. -/
theorem proposed_leadingOnesAdaptive_eventualFirstCrossingTotal_eq_twiceExact
    {n : Nat} (rate : Nat -> Real) (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingTotalMass rate i =
      2 * leadingOnesAdaptiveEventualFirstCrossingExactMass rate i := by
  unfold leadingOnesAdaptiveEventualFirstCrossingTotalMass
  rw [← proposed_leadingOnesAdaptive_eventualFirstCrossingExactMass_eq_skipMass rate i]
  ring

end ECRuntime
