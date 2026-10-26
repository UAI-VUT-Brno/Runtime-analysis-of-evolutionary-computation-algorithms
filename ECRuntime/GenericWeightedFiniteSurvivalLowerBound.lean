import ECRuntime.GenericSelfLoopSurvivalPower
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P07. A nonnegative weighted fixed-budget survival lower bound for a
finite stochastic kernel. This is an algorithm-independent consequence of
the certified geometric self-loop survival inequality. -/

/-- The no-move geometric path lower bounds any finite nonnegative
weighted sum of target survival probabilities. -/
theorem proposed_genericWeightedSurvival_ge_selfLoopGeometric
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (level : Set α) [DecidablePred (fun y : α => y ∈ level)]
    (x : α) (hx : x ∈ level)
    (q : Real) (hq : 0 ≤ q) (hself : q ≤ P x x)
    (weight : Nat → Real) (hweight : ∀ t, 0 ≤ weight t) (horizon : Nat) :
    (∑ t ∈ Finset.range horizon, weight t * q ^ t) ≤
      ∑ t ∈ Finset.range horizon,
        weight t * finiteLevelSurvival P level t x := by
  classical
  apply Finset.sum_le_sum
  intro t _ht
  exact mul_le_mul_of_nonneg_left
    (proposed_finiteLevelSurvival_ge_selfLoopPower
      P hP level x hx q hq hself t) (hweight t)

end ECRuntime
