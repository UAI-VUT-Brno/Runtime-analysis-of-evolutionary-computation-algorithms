import ECRuntime.GenericTargetRuntimeAntitonicity
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 290 (P07). An arbitrary nonnegative initial weight function
preserves the generic target-set runtime comparison; no finite expected
runtime is assumed, and ENNReal correctly handles infinite expectations.
-/

/-- Enlarging a target weakly decreases weighted extended runtime. -/
theorem proposed_weightedRuntimeSup_antitone_target
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (s t : Set α)
    [DecidablePred (fun x => x ∈ s)]
    [DecidablePred (fun x => x ∈ t)]
    (hst : s ⊆ t) (w : α → ENNReal) :
    (∑ x : α, w x * runtimeSup P t x) ≤
      ∑ x : α, w x * runtimeSup P s x := by
  apply Finset.sum_le_sum
  intro x _hx
  exact mul_le_mul_right (proposed_runtimeSup_antitone_target P hP s t hst x) (w x)

end ECRuntime
