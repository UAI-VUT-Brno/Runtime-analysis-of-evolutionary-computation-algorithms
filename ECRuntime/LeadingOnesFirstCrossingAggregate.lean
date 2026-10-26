import ECRuntime.LeadingOnesFirstCrossingMass
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 27 fix 6: countable first-crossing mass aggregation for LeadingOnes

Stage 27 fix 5 fix 1 compiler-verifies that, at every fixed finite crossing time `t`,
uniformly initialized LeadingOnes histories which first cross boundary `i` at exact
level `i` have the same total mass as histories which first cross strictly above `i`.

This file performs only the countable aggregation step.  The real-valued finite-time
masses are embedded into `ENNReal` with `ENNReal.ofReal` and summed over all crossing
times.  Since the finite-time equality is pointwise in `t`, `tsum_congr` immediately
lifts it to the full countable sums.

No normalization claim is made here.  In particular, this file does not yet prove that
the total first-crossing mass is one.  That eventual-crossing statement is the final
probabilistic obligation needed to turn the equality of the two aggregate branches
into the classical `1/2` visit probability.
-/

/-- Countable aggregate of exact first-crossing masses over all finite crossing times. -/
noncomputable def leadingOnesEventualFirstCrossingExactMass
    {n : ℕ} (p : ℝ) (i : Fin n) : ENNReal :=
  ∑' t : ℕ,
    ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i)

/-- Countable aggregate of strict-skip first-crossing masses over all finite crossing times. -/
noncomputable def leadingOnesEventualFirstCrossingSkipMass
    {n : ℕ} (p : ℝ) (i : Fin n) : ENNReal :=
  ∑' t : ℕ,
    ENNReal.ofReal (leadingOnesFirstCrossingSkipMass (t := t) p i)

/-- Exact-entry and strict-skip masses remain equal after summing over every finite
first-crossing time. -/
theorem leadingOnesEventualFirstCrossingExactMass_eq_skipMass
    {n : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesEventualFirstCrossingExactMass p i =
      leadingOnesEventualFirstCrossingSkipMass p i := by
  unfold leadingOnesEventualFirstCrossingExactMass
    leadingOnesEventualFirstCrossingSkipMass
  apply tsum_congr
  intro t
  rw [leadingOnesFirstCrossingExactMass_eq_skipMass (t := t) p i]

/-- Total countable first-crossing mass, split into exact-entry and strict-skip branches. -/
noncomputable def leadingOnesEventualFirstCrossingMass
    {n : ℕ} (p : ℝ) (i : Fin n) : ENNReal :=
  leadingOnesEventualFirstCrossingExactMass p i +
    leadingOnesEventualFirstCrossingSkipMass p i

/-- The aggregate first-crossing mass is twice the aggregate exact-entry mass. -/
theorem leadingOnesEventualFirstCrossingMass_eq_two_mul_exactMass
    {n : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesEventualFirstCrossingMass p i =
      2 * leadingOnesEventualFirstCrossingExactMass p i := by
  unfold leadingOnesEventualFirstCrossingMass
  rw [← leadingOnesEventualFirstCrossingExactMass_eq_skipMass p i]
  rw [two_mul]

/-- Symmetrically, the aggregate first-crossing mass is twice the aggregate skip mass. -/
theorem leadingOnesEventualFirstCrossingMass_eq_two_mul_skipMass
    {n : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesEventualFirstCrossingMass p i =
      2 * leadingOnesEventualFirstCrossingSkipMass p i := by
  unfold leadingOnesEventualFirstCrossingMass
  rw [leadingOnesEventualFirstCrossingExactMass_eq_skipMass p i]
  rw [two_mul]

end ECRuntime
