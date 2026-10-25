import ECRuntime.RLSCouponExactUniformMean
import ECRuntime.RLSAllDimensionPaperSharpCentered
import Mathlib

open Filter
open scoped BigOperators
namespace ECRuntime

/-! P02: transfer the already certified parity-glued sharp RLS limit to
the **direct coupon process** with its own stochastic kernel. This is
stronger than a mere fixed-dimension renaming: it establishes the source's
second-order full-sequence correction for the explicit coupon semantics. -/

/-- The uniform-start coupon process has the paper's half-harmonic
second-order correction `-1/2` along all positive dimensions. -/
theorem proposed_randomStakeCoupon_allDimensionPaperSharpCentered :
    Tendsto
      (fun n : Nat =>
        if hn : 0 < n then
          ((Finset.univ.sum (fun x : BitString n =>
            (runtimeSup (randomStakeCouponTransition hn)
              ({allOnes n} : Set (BitString n)) x).toReal)) /
            (2 : Real) ^ n) -
            (n : Real) *
              ((harmonicReal (n / 2) + harmonicReal ((n + 1) / 2)) / 2)
        else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  have hf : ∀ n : Nat,
      CandidateCoordinateStrictMonotonicity (oneMaxReal (n := n)) := by
    intro n x i hi
    change (oneMax x : Real) <
      (oneMax (mutateWithMask x {i}) : Real)
    exact_mod_cast (oneMax_single_zero_flip_improves x i hi)
  apply (proposed_strictMonotoneRLS_allDimensionPaperSharpCentered
    (fun n => oneMaxReal (n := n)) hf).congr'
  filter_upwards [] with n
  by_cases hn : 0 < n
  · simp only [dif_pos hn]
    rw [proposed_couponUniformRuntime_eq_strictMonotoneRLSUniformInitialMean hn]
  · simp only [dif_neg hn]

end ECRuntime
