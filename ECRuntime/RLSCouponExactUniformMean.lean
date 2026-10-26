import ECRuntime.RLSCouponProcessKernelCorrespondence
import ECRuntime.DoerrDoerrMonotoneUniformMean
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P02 / 2013 preprint: an exact finite-dimensional coupon-process
counterpart, without any asymptotic or uniform integrability arguments. -/

/-- The direct coupon process, from independently uniform initial coupons,
has the same exact mean as uniformly initialized one-bit RLS on OneMax. -/
theorem proposed_couponUniformRuntime_eq_strictMonotoneRLSUniformInitialMean
    {n : Nat} (hn : 0 < n) :
    (Finset.univ.sum (fun x : BitString n =>
      (runtimeSup (randomStakeCouponTransition hn)
        ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n =
      strictMonotoneRLSUniformInitialMean hn (oneMaxReal (n := n)) := by
  rfl

end ECRuntime
