import ECRuntime.StrictMonotoneRLS
import ECRuntime.DoerrDoerrMonotoneUniformMean
import Mathlib

namespace ECRuntime

/-! P02 / Doerr--Doerr (2013): paper-specific coupon process interface.
A direct coupon collector is a Boolean vector of collected coupon types;
when choosing one type uniformly, an already-collected type is retained.
The RLS transition is known to be the OneMax one-bit elitist transition.
This result is the remaining explicit semantic identification required to
name the preprint's coupon-collector theorem independently of RLS. -/

/-- Explicit one-coupon sampling kernel. -/
noncomputable def randomStakeCouponTransition
    {n : Nat} (hn : 0 < n) : TransitionMatrix (BitString n) :=
  (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal

/-- Sampling one previously uncollected coupon and one-bit elitist OneMax
RLS agree as Markov kernels. -/
theorem proposed_couponProcess_transition_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n) (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness) :
    randomStakeCouponTransition hn =
      (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness := by
  exact (candidateStrictMonotoneRLS_transition_eq_oneMax hn fitness hf).symm

end ECRuntime
