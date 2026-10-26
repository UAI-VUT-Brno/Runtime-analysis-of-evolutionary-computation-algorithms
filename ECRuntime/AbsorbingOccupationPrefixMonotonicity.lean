import ECRuntime.AbsorbingOccupationPrefix
import Mathlib

open scoped ENNReal
namespace ECRuntime

/-! P01. Generic finite-prefix and countable-occupation monotonicity,
using Mathlib's Nat.le_induction and iSup order lemmas. -/

/-- Nonnegative occupation prefixes are monotone in the horizon. -/
theorem proposed_nonTargetOccupationPrefix_mono
    {α : Type*} (target : Set α)
    [DecidablePred (fun y => y ∈ target)]
    (state : Nat → α) (T U : Nat) (hTU : T ≤ U) :
    proposed_nonTargetOccupationPrefix target state T ≤
      proposed_nonTargetOccupationPrefix target state U := by
  induction U, hTU using Nat.le_induction with
  | base => exact le_rfl
  | succ u _ ih =>
      exact ih.trans (proposed_nonTargetOccupationPrefix_le_succ target state u)

/-- Every occupation prefix is bounded by the countable occupation sum. -/
theorem proposed_nonTargetOccupationPrefix_le_total
    {α : Type*} (target : Set α)
    [DecidablePred (fun y => y ∈ target)]
    (state : Nat → α) (T : Nat) :
    proposed_nonTargetOccupationPrefix target state T ≤
      ∑' t : Nat, if state t ∈ target then (0 : ENNReal) else 1 := by
  rw [proposed_nonTargetOccupationTsum_eq_iSup_prefix]
  exact le_iSup (fun U : Nat => proposed_nonTargetOccupationPrefix target state U) T

end ECRuntime
