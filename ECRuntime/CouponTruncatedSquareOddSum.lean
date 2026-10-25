import Mathlib

namespace ECRuntime

/-! P02: elementary pathwise component of the second-moment identity.
For any integer stopped time m, the square is the sum of the first m odd
integers. The next step identifies the indicator events with trajectory
survival to obtain a certified truncated second hitting-time moment. -/

/-- The truncated square of an integer time admits a finite survival-tail
weight expansion by odd numbers. -/
theorem proposed_coupon_truncatedTimeSquare_eq_oddSum
    (horizon hittingTime : Nat) :
    (min horizon hittingTime) * (min horizon hittingTime) =
      ∑ t ∈ Finset.range (min horizon hittingTime), (2 * t + 1) := by
  let m := min horizon hittingTime
  change m * m = ∑ t ∈ Finset.range m, (2 * t + 1)
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

end ECRuntime
