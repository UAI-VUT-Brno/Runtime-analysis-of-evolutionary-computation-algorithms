import ECRuntime.RLSCouponExactUniformMean
import ECRuntime.RLSAllDimensionPaperCenteredExact
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P02: the source-paper finite-dimensional centered formula, expressed
for the explicit coupon-collection kernel rather than through its RLS alias. -/

/-- Finite-n exact centered coupon-runtime formula. Its right-hand side is
valid in both parities, without invoking an asymptotic approximation. -/
theorem proposed_randomStakeCoupon_finitePaperCenteredExact
    {n : Nat} (hn : 0 < n) :
    (Finset.univ.sum (fun x : BitString n =>
      (runtimeSup (randomStakeCouponTransition hn)
        ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n -
      (n : Real) *
        ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) =
    (n : Real) *
      (harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) -
        (harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2) := by
  have hf : CandidateCoordinateStrictMonotonicity (oneMaxReal (n := n)) := by
    intro x i hi
    change (oneMax x : Real) <
      (oneMax (mutateWithMask x {i}) : Real)
    exact_mod_cast (oneMax_single_zero_flip_improves x i hi)
  rw [proposed_couponUniformRuntime_eq_strictMonotoneRLSUniformInitialMean hn]
  exact proposed_strictMonotoneRLS_allDimensionPaperCentered_exact hn oneMaxReal hf

end ECRuntime
