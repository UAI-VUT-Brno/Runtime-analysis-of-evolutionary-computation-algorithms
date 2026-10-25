import ECRuntime.StaticUnaryUnbiasedMutation
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P07: a normalization bound for the mean mutation radius of any
static unary-unbiased mutation law; no independence is needed. -/

/-- The expected number of flipped coordinates does not exceed n. -/
theorem proposed_staticUnary_meanRadius_le_dimension
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) :
    law.meanRadius ≤ (n : Real) := by
  have hrad (k : Nat) (hk : k ∈ Finset.range (n + 1)) :
      (k : Real) ≤ (n : Real) := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  unfold StaticUnaryUnbiasedMutation.meanRadius
  calc
    (∑ k ∈ Finset.range (n + 1), (k : Real) * law.radiusMass k) ≤
        ∑ k ∈ Finset.range (n + 1), (n : Real) * law.radiusMass k := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right (hrad k hk)
            (law.radiusMass_nonneg k)
    _ = (n : Real) * (∑ k ∈ Finset.range (n + 1), law.radiusMass k) := by
          rw [Finset.mul_sum]
    _ = (n : Real) := by
          rw [law.sum_radiusMass_eq_one]
          ring

end ECRuntime
