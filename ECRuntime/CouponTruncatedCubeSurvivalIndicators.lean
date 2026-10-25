import Mathlib

namespace ECRuntime

/-! P02: the deterministic cubic stopped-time identity. This is a
pathwise statement, not yet a statement about a Markov hitting time. -/

/-- The cube of a truncated integer time is a survival-indicator sum. -/
theorem proposed_coupon_truncatedCube_eq_survivalIndicators
    (horizon hittingTime : Nat) :
    (min horizon hittingTime) ^ 3 =
      Finset.sum (Finset.range horizon)
        (fun k => if k < hittingTime then 3 * k * k + 3 * k + 1 else 0) := by
  have hCube (m : Nat) :
      m ^ 3 = Finset.sum (Finset.range m)
        (fun k => 3 * k * k + 3 * k + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ← ih]
        ring
  rw [hCube (min horizon hittingTime)]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

end ECRuntime
