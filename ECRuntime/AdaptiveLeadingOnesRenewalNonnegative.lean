import ECRuntime.AdaptiveLeadingOnesScalarRenewalSolution
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 278 (P01, proposed). Establish the positivity and finite-prefix
monotonicity needed before applying monotone convergence to the genuine
adaptive occupancy sequence. These facts are algebraic and do *not* identify
an infinite-path expectation or evaluate a geometric residence sum.
-/

/-- A nonnegative entry stream and nonnegative stay coefficient generate
nonnegative finite-time occupation masses under the scalar renewal law. -/
theorem proposed_finiteOccupationRenewalSolution_nonneg
    (q initial : Real) (entry : Nat → Real)
    (hq : 0 ≤ q) (hinit : 0 ≤ initial)
    (hentry : ∀ t : Nat, 0 ≤ entry t) (t : Nat) :
    0 ≤ finiteOccupationRenewalSolution q initial entry t := by
  induction t with
  | zero =>
      simpa only [finiteOccupationRenewalSolution] using hinit
  | succ t ih =>
      change 0 ≤ entry t + q * finiteOccupationRenewalSolution q initial entry t
      exact add_nonneg (hentry t) (mul_nonneg hq ih)

/-- Cumulative occupation mass increases with the observation horizon.
This is the finitary monotonicity required for a countable-sum limit. -/
theorem proposed_finiteOccupationRenewalSolution_prefix_mono
    (q initial : Real) (entry : Nat → Real)
    (hq : 0 ≤ q) (hinit : 0 ≤ initial)
    (hentry : ∀ t : Nat, 0 ≤ entry t) (T : Nat) :
    (∑ t ∈ Finset.range T,
      finiteOccupationRenewalSolution q initial entry t) ≤
    (∑ t ∈ Finset.range (T + 1),
      finiteOccupationRenewalSolution q initial entry t) := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (proposed_finiteOccupationRenewalSolution_nonneg q initial entry hq hinit hentry T)

end ECRuntime
