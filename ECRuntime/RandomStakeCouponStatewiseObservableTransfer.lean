import ECRuntime.RLSCouponProcessKernelCorrespondence
import ECRuntime.RLSOneBitExpectationSupport
import Mathlib

namespace ECRuntime

/-! P02: transfer arbitrary observables at one step, not only expected
runtime or survival. The proof uses genuine equality of kernels. -/

/-- Every real-valued observable has the same next-state expectation under
the direct coupon kernel and strict-monotone RLS, at every initial state. -/
theorem proposed_couponProcess_statewiseObservableExpectation_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (F : BitString n → Real) (x : BitString n) :
    expectedValueAfter (randomStakeCouponTransition hn) F x =
      expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness) F x := by
  rw [proposed_couponProcess_transition_eq_strictMonotoneRLS hn fitness hf]

end ECRuntime
