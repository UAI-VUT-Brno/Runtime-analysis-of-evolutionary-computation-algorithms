import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.StaticUnaryUnbiasedLinearDrift
import ECRuntime.OneMaxEAMutationMaskZeroBoundResearch
import ECRuntime.StaticUnaryZeroFlipExpectationDoubleCount
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P07: a distribution-free first-moment OneMax bound valid for every
static unary-unbiased mutation distribution, including non-independent
multi-bit masks. It is the natural generalization of the independent-bit
stage 357 and requires only the certified coordinate-marginal identity. -/

/-- Expected accepted OneMax zero-count progress under *any* static
unary-unbiased law is at most `d * meanRadius / n` for positive dimension. -/
theorem proposed_unaryOneMax_expectedZeroDecrease_le_meanRadius
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n) (x : BitString n) :
    (∑ y : BitString n,
      law.transition (oneMaxReal (n := n)) x y *
        ((zeroCount x : Real) - (zeroCount y : Real))) ≤
      (zeroCount x : Real) * (law.meanRadius / (n : Real)) := by
  classical
  let V : BitString n → Real := fun y => (zeroCount y : Real)
  have hP : IsStochastic (law.transition oneMaxReal) :=
    law.transition_stochastic _
  have hrewrite :
      (∑ y : BitString n,
        (law.transition oneMaxReal) x y * (V x - V y)) =
      driftAt (law.transition oneMaxReal) V x := by
    unfold driftAt
    calc
      (∑ y : BitString n,
          (law.transition oneMaxReal) x y * (V x - V y)) =
        (∑ y : BitString n, (law.transition oneMaxReal) x y) * V x -
          ∑ y : BitString n, (law.transition oneMaxReal) x y * V y := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = V x - expectedValueAfter (law.transition oneMaxReal) V x := by
            rw [hP.2 x, one_mul]
            rfl
  have hmask :
      (∑ mask : MutationMask n,
        law.weight mask *
          (V x - V (selectedAfterMask oneMaxReal x mask))) ≤
      ∑ mask : MutationMask n,
        law.weight mask * ((zeroPositions x ∩ mask).card : Real) := by
    apply Finset.sum_le_sum
    intro mask _
    exact mul_le_mul_of_nonneg_left
      (proposed_oneMax_selectedZeroDecrease_le_flippedZeroCount x mask)
      (law.weight_nonneg mask)
  calc
    (∑ y : BitString n,
        law.transition oneMaxReal x y *
          ((zeroCount x : Real) - (zeroCount y : Real))) =
      driftAt (law.transition oneMaxReal) V x := hrewrite
    _ = ∑ mask : MutationMask n,
          law.weight mask *
            (V x - V (selectedAfterMask oneMaxReal x mask)) :=
          law.drift_eq_mask_sum oneMaxReal V x
    _ ≤ ∑ mask : MutationMask n,
          law.weight mask * ((zeroPositions x ∩ mask).card : Real) := hmask
    _ = (zeroCount x : Real) * (law.meanRadius / (n : Real)) :=
          proposed_unaryMask_expectedFlippedZeroCount_eq_meanRadius hn law x

end ECRuntime
