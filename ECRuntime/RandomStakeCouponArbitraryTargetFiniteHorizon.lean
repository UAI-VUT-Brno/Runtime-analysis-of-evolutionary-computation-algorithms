import ECRuntime.RandomStakeCouponStatewiseSurvivalCorrespondence
import ECRuntime.FiniteRuntimeSurvivalSupport
import Mathlib

namespace ECRuntime

/-! P02: extend the coupon/RLS kernel equivalence to arbitrary finite
horizons and arbitrary targets, not just the optimum singleton. -/

/-- Every finite-time survival mass is invariant under replacing the
direct coupon process by RLS for a coordinatewise strictly monotone fitness. -/
theorem proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n))
    [DecidablePred (fun x : BitString n => x ∈ target)]
    (t : Nat) (x : BitString n) :
    finiteLevelSurvival
      (randomStakeCouponTransition hn) targetᶜ t x =
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
