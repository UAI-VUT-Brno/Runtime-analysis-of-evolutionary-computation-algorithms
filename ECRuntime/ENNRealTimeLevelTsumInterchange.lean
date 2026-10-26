import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: a reusable finite-level/countable-time interchange. The finite level
index carries no convergence burden because all summands are nonnegative
extended reals. This is the analytic step needed after Stages 304 and 308. -/

/-- Interchange a countable time sum and a finite fitness-level sum in `ENNReal`. -/
theorem proposed_ennreal_timeLevel_sum_swap
    {n : Nat} (f : Nat → Fin n → ENNReal) :
    (∑' t : Nat, ∑ i : Fin n, f t i) =
      ∑ i : Fin n, ∑' t : Nat, f t i := by
  classical
  -- Use Mathlib's finite-type `tsum` conversion before Tonelli,
  -- exactly as in the certified LeadingOnes visit-probability bridge.
  calc
    (∑' t : Nat, ∑ i : Fin n, f t i) =
        ∑' t : Nat, ∑' i : Fin n, f t i := by
      apply tsum_congr
      intro t
      rw [tsum_fintype]
    _ = ∑' i : Fin n, ∑' t : Nat, f t i := by
      exact ENNReal.tsum_comm
    _ = ∑ i : Fin n, ∑' t : Nat, f t i := by
      rw [tsum_fintype]

end ECRuntime
