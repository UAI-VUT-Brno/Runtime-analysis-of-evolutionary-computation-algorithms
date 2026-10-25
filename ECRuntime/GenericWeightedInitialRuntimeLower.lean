import ECRuntime.GenericRuntimeSelfLoopLower
import Mathlib

attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
namespace ECRuntime

/-! P07. Generic self-loop expected runtime bound, now for arbitrary
countable mixtures of non-target starting states and nonnegative weights. -/

/-- Any countable nonnegative weighted initialization obeys the
corresponding sum of genuine self-loop expected-runtime lower bounds. -/
theorem proposed_genericWeightedInitialRuntime_ge_selfLoopGeometric
    {α : Type*} [Fintype α] {ι : Type*} [Countable ι]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (target : Set α) (start : ι → α)
    (hstart : ∀ j : ι, start j ∉ target)
    (q : ι → Real) (hq : ∀ j, 0 ≤ q j)
    (hself : ∀ j, q j ≤ P (start j) (start j))
    (weight : ι → ENNReal) :
    (∑' j : ι, weight j *
      ∑' t : Nat, ENNReal.ofReal ((q j) ^ t)) ≤
    (∑' j : ι, weight j * runtimeSup P target (start j)) := by
  classical
  apply ENNReal.tsum_le_tsum
  intro j
  exact mul_le_mul_of_nonneg_left
    (proposed_genericRuntimeSup_ge_selfLoopGeometric
      P hP target (start j) (hstart j) (q j) (hq j) (hself j))
    (by exact bot_le)

end ECRuntime
