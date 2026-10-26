import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import ECRuntime.OneMaxEAMutationMaskZeroBoundResearch
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-!
P07: genuinely distribution-level first moment of flipped zero coordinates.
The proof uses finite double counting and the certified marginal law, not an
independence assumption. Together with Stage 366 it reduces expected OneMax
progress to the coordinate marginal task of Stage 368.
-/

/-- The expected number of flipped initially-zero bits is exactly the sum of
marginal flip probabilities over the initially-zero coordinates. -/
theorem proposed_unaryMask_expectedFlippedZeroCount_eq_sumMarginals
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (x : BitString n) :
    (∑ mask : MutationMask n,
      law.weight mask * ((zeroPositions x ∩ mask).card : Real)) =
    ∑ i ∈ zeroPositions x, law.coordinateFlipMass i := by
  classical
  calc
    (∑ mask : MutationMask n,
        law.weight mask * ((zeroPositions x ∩ mask).card : Real)) =
      ∑ mask : MutationMask n,
        ∑ i ∈ zeroPositions x ∩ mask, law.weight mask := by
          apply Finset.sum_congr rfl
          intro mask _
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    _ = ∑ mask : MutationMask n,
          ∑ i ∈ zeroPositions x,
            if i ∈ mask then law.weight mask else 0 := by
          apply Finset.sum_congr rfl
          intro mask _
          rw [← Finset.sum_filter]
          congr 1
    _ = ∑ i ∈ zeroPositions x, law.coordinateFlipMass i := by
          rw [Finset.sum_comm]
          rfl

/-- For static unary-unbiased mutation this first moment is `d * χ / n`;
no independent-bit model is assumed. -/
theorem proposed_unaryMask_expectedFlippedZeroCount_eq_meanRadius
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n) (x : BitString n) :
    (∑ mask : MutationMask n,
      law.weight mask * ((zeroPositions x ∩ mask).card : Real)) =
    (zeroCount x : Real) * (law.meanRadius / (n : Real)) := by
  rw [proposed_unaryMask_expectedFlippedZeroCount_eq_sumMarginals]
  simp_rw [law.coordinateFlipMass_eq_meanRadius_div hn]
  rw [Finset.sum_const, nsmul_eq_mul, zeroPositions_card]

end ECRuntime
