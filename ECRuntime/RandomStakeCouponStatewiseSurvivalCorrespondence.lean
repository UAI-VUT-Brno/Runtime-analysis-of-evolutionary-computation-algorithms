import ECRuntime.RLSCouponProcessKernelCorrespondence
import ECRuntime.RLSFixedTarget
import ECRuntime.UnrestrictedRuntime
import Mathlib

namespace ECRuntime

/-! P02. The coupon-process kernel correspondence is stronger than the
previously certified *uniform-mean* equality: it identifies the entire
finite-horizon hitting-time survival law and every fixed-start expected
runtime, for any coordinatewise strictly monotone fitness. -/

/-- The direct coupon and strict-monotone RLS kernels have identical
finite-time nonoptimal survival probabilities for every fixed start. -/
theorem proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (t : Nat) (x : BitString n) :
    finiteLevelSurvival
      (randomStakeCouponTransition hn)
      ({allOnes n} : Set (BitString n))ᶜ t x =
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n))ᶜ t x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

/-- The correspondence holds pointwise for extended expected runtimes,
including without separately assuming finite mean. -/
theorem proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (x : BitString n) :
    runtimeSup
      (randomStakeCouponTransition hn)
      ({allOnes n} : Set (BitString n)) x =
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
      ({allOnes n} : Set (BitString n)) x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
