import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: isolate the only base-dependent summand in the certified
uniform-initial LeadingOnes runtime formula. -/

/-- The reference schedule's finite exit-cost sum consists of the
level-zero reciprocal contribution and fixed higher-level contributions. -/
theorem proposed_leadingOnes_referenceExitCost_sum_decomposition
    (n : Nat) (base : Real) :
    (∑ i : Fin n, (1 / 2 : ENNReal) *
      ENNReal.ofReal
        ((proposed_leadingOnes_referenceOptimalRate base i.val *
          (1 - proposed_leadingOnes_referenceOptimalRate base i.val) ^ i.val)⁻¹)) =
    ∑ i : Fin n, if i.val = 0 then
      (1 / 2 : ENNReal) * ENNReal.ofReal (base⁻¹)
    else
      (1 / 2 : ENNReal) * ENNReal.ofReal
        ((1 / ((i.val + 1 : Nat) : Real) *
          (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val)⁻¹) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val = 0
  · simp [hi, proposed_leadingOnes_referenceOptimalRate]
  · simp [hi, proposed_leadingOnes_referenceOptimalRate]

end ECRuntime
