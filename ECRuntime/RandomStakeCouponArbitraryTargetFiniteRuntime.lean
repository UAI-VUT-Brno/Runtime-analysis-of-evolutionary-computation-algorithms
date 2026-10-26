import ECRuntime.RandomStakeCouponStatewiseSurvivalCorrespondence
import ECRuntime.HittingTime
import Mathlib

attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: the kernel identity extends beyond survival at fixed horizons.
This also works for non-monotone target sets and any initial state. -/

/-- Finite-horizon expected hitting times agree for any target set. -/
theorem proposed_couponProcess_arbitraryTarget_finiteRuntime_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (t : Nat) (x : BitString n) :
    finiteHorizonRuntime (randomStakeCouponTransition hn) target t x =
      finiteHorizonRuntime
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        target t x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
