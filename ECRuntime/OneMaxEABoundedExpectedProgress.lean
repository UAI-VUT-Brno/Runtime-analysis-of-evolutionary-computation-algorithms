import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import ECRuntime.OneMax
import ECRuntime.StaticUnaryUnbiasedLinearDrift
import ECRuntime.OneMaxEAMutationMaskZeroBoundResearch
import ECRuntime.IndependentBitCoordinateFlipMarginalResearch
import ECRuntime.StaticUnaryZeroFlipExpectationDoubleCount
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P07: a substantive missing ingredient for a fixed-target *lower* bound.
The current certified self-loop bounds do not control positive progress
from other offspring states. For elitist OneMax selection, the accepted
zero-count decrease cannot exceed the number of previously zero coordinates
flipped by independent bit mutation. That coupling should yield a per-step
expected progress bound d*p, where d is the current zero count. The
proof requires a weighted mutation-mask marginal inequality and is left
admitted until developed and Lean-verified. -/

/-- For a genuine stochastic (1+1)-EA OneMax mutation with probability p,
expected one-step decrease of the zero count is at most d*p. -/
theorem proposed_oneMaxEA_expectedZeroDecrease_le_zeroCount_mul_p
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) :
    (∑ y : BitString n,
      onePlusOneTransition p (oneMaxReal (n := n)) x y *
        ((zeroCount x : Real) - (zeroCount y : Real))) ≤
      (zeroCount x : Real) * p := by
  classical
  let law : StaticUnaryUnbiasedMutation n :=
    StaticUnaryUnbiasedMutation.independentBitLaw (n := n) p hp0 hp1
  let V : BitString n → Real := fun y => (zeroCount y : Real)
  have hP : IsStochastic (law.transition oneMaxReal) := law.transition_stochastic _
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
  have hmean :
      (∑ mask : MutationMask n,
          law.weight mask * ((zeroPositions x ∩ mask).card : Real)) =
        (zeroCount x : Real) * p := by
    rw [proposed_unaryMask_expectedFlippedZeroCount_eq_sumMarginals]
    change (∑ i ∈ zeroPositions x,
      (StaticUnaryUnbiasedMutation.independentBitLaw (n := n) p hp0 hp1).coordinateFlipMass i) =
        (zeroCount x : Real) * p
    simp_rw [proposed_independentBitLaw_coordinateFlipMass_eq_p p hp0 hp1]
    rw [Finset.sum_const, nsmul_eq_mul, zeroPositions_card]
  calc
    (∑ y : BitString n,
      onePlusOneTransition p (oneMaxReal (n := n)) x y *
        ((zeroCount x : Real) - (zeroCount y : Real))) =
      driftAt (law.transition oneMaxReal) V x := by
        rw [← hrewrite]
        rw [StaticUnaryUnbiasedMutation.independentBitLaw_transition_eq_onePlusOneTransition]
    _ = ∑ mask : MutationMask n,
          law.weight mask *
            (V x - V (selectedAfterMask oneMaxReal x mask)) :=
        law.drift_eq_mask_sum oneMaxReal V x
    _ ≤ ∑ mask : MutationMask n,
          law.weight mask * ((zeroPositions x ∩ mask).card : Real) := hmask
    _ = (zeroCount x : Real) * p := hmean

end ECRuntime
