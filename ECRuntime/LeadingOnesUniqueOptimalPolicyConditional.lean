import ECRuntime.AdaptiveLeadingOnesUniquePositiveLevelOptimizer
import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import Mathlib

namespace ECRuntime

/-! P01: once the general weighted-AM--GM equality case (Stage 411)
is available, the componentwise unique positive-level adaptive policy
follows without a separate optimization argument. -/

/-- Equality of the exit probabilities forces the optimal positive-level rate. -/
theorem proposed_leadingOnes_exitEquality_forces_referenceRate
    (n : Nat) (base : Real) (rate : Nat → Real)
    (hvalid : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (heq : ∀ i : Fin n,
      rate i.val * (1 - rate i.val) ^ i.val =
        proposed_leadingOnes_referenceOptimalRate base i.val *
          (1 - proposed_leadingOnes_referenceOptimalRate base i.val) ^ i.val)
    (i : Fin n) (hi : 0 < i.val) :
    rate i.val = proposed_leadingOnes_referenceOptimalRate base i.val := by
  have h := proposed_leadingOnes_positiveLevelExit_uniqueMaximizer
    i.val hi (rate i.val)
    (hvalid i.val i.isLt.le).1 (hvalid i.val i.isLt.le).2
  have hEq : rate i.val * (1 - rate i.val) ^ i.val =
      (1 / ((i.val + 1 : Nat) : Real)) *
        (1 - 1 / ((i.val + 1 : Nat) : Real)) ^ i.val := by
    simpa [proposed_leadingOnes_referenceOptimalRate, Nat.ne_of_gt hi] using heq i
  simpa [proposed_leadingOnes_referenceOptimalRate, Nat.ne_of_gt hi] using h hEq

end ECRuntime
