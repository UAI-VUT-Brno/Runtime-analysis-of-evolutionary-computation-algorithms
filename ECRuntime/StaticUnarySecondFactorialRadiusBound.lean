import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import Mathlib

open scoped BigOperators
namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-! P07: pair-flip arguments require second factorial radius moments.
This dimension-dependent estimate holds for *every* static unary-unbiased
mask law. It avoids the false replacement of a conditional size-biased
radius distribution by its unconditional law. -/

/-- E[K(K-1)] ≤ (n-1)E[K], with the second factor in Nat subtraction
so the zero-dimensional case is included without an artificial hypothesis. -/
theorem proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) :
    law.secondFactorialRadiusMoment ≤
      ((n - 1 : Nat) : Real) * law.meanRadius := by
  unfold secondFactorialRadiusMoment meanRadius
  calc
    (∑ k ∈ Finset.range (n + 1),
       (k : Real) * ((k - 1 : Nat) : Real) * law.radiusMass k) ≤
       ∑ k ∈ Finset.range (n + 1),
         ((n - 1 : Nat) : Real) * ((k : Real) * law.radiusMass k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpred : ((k - 1 : Nat) : Real) ≤ ((n - 1 : Nat) : Real) := by
        exact_mod_cast Nat.sub_le_sub_right hkn 1
      have hk_nonneg : (0 : Real) ≤ (k : Real) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hpred hk_nonneg
      have hweighted := mul_le_mul_of_nonneg_right hscaled
        (law.radiusMass_nonneg k)
      calc
        (k : Real) * ((k - 1 : Nat) : Real) * law.radiusMass k ≤
          ((k : Real) * ((n - 1 : Nat) : Real)) * law.radiusMass k :=
            hweighted
        _ = ((n - 1 : Nat) : Real) * ((k : Real) * law.radiusMass k) := by ring
    _ = ((n - 1 : Nat) : Real) *
        (∑ k ∈ Finset.range (n + 1), (k : Real) * law.radiusMass k) := by
      rw [Finset.mul_sum]

end StaticUnaryUnbiasedMutation
end ECRuntime
