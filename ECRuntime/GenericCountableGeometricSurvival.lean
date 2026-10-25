import ECRuntime.GenericSelfLoopSurvivalPower
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P07. A genuine infinite-horizon consequence: the sum of target-survival
probabilities dominates the geometric self-loop contribution. This supplies
a lower bound on extended expected target hitting time once the certified
hitting-time/survival representation is instantiated. -/

/-- Nonnegative infinite-horizon target survival dominates the self-loop
geometric series for any finite stochastic kernel and initial non-target. -/
theorem proposed_genericTotalSurvival_ge_selfLoopGeometric
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (level : Set α) [DecidablePred (fun y : α => y ∈ level)]
    (x : α) (hx : x ∈ level)
    (q : Real) (hq : 0 ≤ q) (hself : q ≤ P x x) :
    (∑' t : Nat, ENNReal.ofReal (q ^ t)) ≤
      ∑' t : Nat, ENNReal.ofReal (finiteLevelSurvival P level t x) := by
  classical
  apply ENNReal.tsum_le_tsum
  intro t
  exact ENNReal.ofReal_le_ofReal
    (proposed_finiteLevelSurvival_ge_selfLoopPower P hP level x hx q hq hself t)

end ECRuntime
