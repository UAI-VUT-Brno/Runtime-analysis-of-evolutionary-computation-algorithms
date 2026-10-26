import ECRuntime.EAGenericTargetRuntimeNoFlipLower
import Mathlib

attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
namespace ECRuntime

/-! P07. Averaging the genuine runtime bound over a finite set of
non-target starts yields a fixed-target expected-runtime lower bound
with arbitrary nonnegative initialization weights. -/

/-- Under admissible bit mutation, every non-target initial state
contributes at least the empty-mask geometric series to expected time. -/
theorem proposed_onePlusOne_weightedAnyTargetRuntime_ge_noFlipGeometric
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fitness : BitString n → Real) (target : Set (BitString n))
    (weight : BitString n → ENNReal) :
    (∑ x ∈ (Finset.univ.filter (fun x : BitString n => x ∉ target)),
      weight x * ∑' t : Nat, ENNReal.ofReal (((1 - p) ^ n) ^ t)) ≤
    (∑ x ∈ (Finset.univ.filter (fun x : BitString n => x ∉ target)),
      weight x * runtimeSup (onePlusOneTransition p fitness) target x) := by
  classical
  apply Finset.sum_le_sum
  intro x hx
  have hnot : x ∉ target := (Finset.mem_filter.mp hx).2
  exact mul_le_mul_of_nonneg_left
    (proposed_onePlusOne_anyTarget_runtimeSup_ge_noFlipGeometric
      p hp0 hp1 fitness target x hnot) (by exact bot_le)

end ECRuntime
