import ECRuntime.AdaptiveLeadingOnesFiniteCrossingParity
import Mathlib

namespace ECRuntime

/-!
Stage 220 (NEW, awaiting statement approval): aggregate the adaptive
finite-time first-crossing equalities over all crossing times. This is an
identity between nonnegative extended-real sums, but is NOT the assertion
that the total crossing mass is one. Eventual crossing under a uniformly
positive admissible rate schedule is a separate theorem to be developed.
-/

/-- Aggregated mass of adaptive first crossings which land exactly at i. -/
noncomputable def leadingOnesAdaptiveEventualFirstCrossingExactMass
    {n : Nat} (rate : Nat -> Real) (i : Fin n) : ENNReal :=
  ∑' t : Nat,
    ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i)

/-- Aggregated mass of adaptive first crossings which skip level i. -/
noncomputable def leadingOnesAdaptiveEventualFirstCrossingSkipMass
    {n : Nat} (rate : Nat -> Real) (i : Fin n) : ENNReal :=
  ∑' t : Nat,
    ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingSkipMass (t := t) rate i)

/-- The exact-versus-skip mass equality is preserved by countable
aggregation over all possible first-crossing times. -/
theorem proposed_leadingOnesAdaptive_eventualFirstCrossingExactMass_eq_skipMass
    {n : Nat} (rate : Nat -> Real) (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate i =
      leadingOnesAdaptiveEventualFirstCrossingSkipMass rate i := by
  unfold leadingOnesAdaptiveEventualFirstCrossingExactMass
    leadingOnesAdaptiveEventualFirstCrossingSkipMass
  apply tsum_congr
  intro t
  rw [proposed_leadingOnesAdaptive_firstCrossingExactMass_eq_skipMass (t := t) rate i]

end ECRuntime
