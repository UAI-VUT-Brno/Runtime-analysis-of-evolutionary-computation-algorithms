import ECRuntime.RandomStakeCouponStatewiseSurvivalCorrespondence
import ECRuntime.UnrestrictedRuntime
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: the direct coupon/RLS identity holds for arbitrary stopping
targets, including non-monotone subsets; this is kernel equality, not a
fitness-level ordering argument. -/

/-- All extended expected hitting times agree pointwise for any target. -/
theorem proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (x : BitString n) :
    runtimeSup (randomStakeCouponTransition hn) target x =
      runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        target x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
