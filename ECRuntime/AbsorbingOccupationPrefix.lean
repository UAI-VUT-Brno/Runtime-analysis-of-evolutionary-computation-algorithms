import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 291 (P01, proposed). Mathlib's monotone finite-range sums form the
countable occupation series needed for nonnegative monotone convergence.
These identities are pathwise and do not assert any probability law.
-/

/-- Finite prefix count of times when an arbitrary path is outside a target. -/
noncomputable def proposed_nonTargetOccupationPrefix
    {α : Type*} (target : Set α)
    [DecidablePred (fun y => y ∈ target)]
    (state : Nat → α) (T : Nat) : ENNReal :=
  ∑ t ∈ Finset.range T, if state t ∈ target then (0 : ENNReal) else 1

/-- Every added time step contributes a nonnegative occupation indicator. -/
theorem proposed_nonTargetOccupationPrefix_le_succ
    {α : Type*} (target : Set α)
    [DecidablePred (fun y => y ∈ target)]
    (state : Nat → α) (T : Nat) :
    proposed_nonTargetOccupationPrefix target state T ≤
      proposed_nonTargetOccupationPrefix target state (T + 1) := by
  unfold proposed_nonTargetOccupationPrefix
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right bot_le

/-- The countable non-target occupation is the supremum of finite prefixes.
This uses `ENNReal.tsum_eq_iSup_nat`, not a generic summability assumption. -/
theorem proposed_nonTargetOccupationTsum_eq_iSup_prefix
    {α : Type*} (target : Set α)
    [DecidablePred (fun y => y ∈ target)]
    (state : Nat → α) :
    (∑' t : Nat, if state t ∈ target then (0 : ENNReal) else 1) =
      ⨆ T : Nat, proposed_nonTargetOccupationPrefix target state T := by
  exact ENNReal.tsum_eq_iSup_nat

end ECRuntime
