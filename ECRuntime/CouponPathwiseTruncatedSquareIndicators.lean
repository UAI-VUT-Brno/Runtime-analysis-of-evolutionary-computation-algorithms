import ECRuntime.CouponTruncatedSquareOddSum
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P02: purely pathwise conversion of the truncated squared waiting
time to survival indicators. No stochastic assumptions or exchanges of
infinite sums are hidden in this combinatorial identity. -/

/-- The square of min(T,H) is the odd-weighted sum of survival indicators. -/
theorem proposed_coupon_truncatedSquare_eq_survivalIndicators
    (horizon hittingTime : Nat) :
    (min horizon hittingTime) * (min horizon hittingTime) =
      ∑ k ∈ Finset.range horizon,
        if k < hittingTime then 2 * k + 1 else 0 := by
  rw [proposed_coupon_truncatedTimeSquare_eq_oddSum]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

end ECRuntime
