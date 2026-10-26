import ECRuntime.RLSFiniteSurvivalCouponBound
import ECRuntime.RLSOneBitSupport
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LinearPotential
import ECRuntime.LevelExitTail
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-! Stage 130: APPROVED, provisional public theorem for promotion verification.
A positive-weight linear RLS coupon-collector tail bound, obtained from the
uniform one-bit kernel equivalence and Stage 129's survival estimate.
This is a finite-horizon statement and makes no independence assumption.
Source context: Doerr--Doerr (2013), Collecting Coupons with Random Initial Stake.
The theorem declaration is unchanged from the approved Stage 130 proposal.
-/

/-- For a strictly positive linear pseudo-Boolean function, one-bit RLS
has the same worst-case coupon-survival estimate as RLS on OneMax. -/
theorem proposed_rlsLinear_finiteSurvival_couponBound
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (x : BitString n) (t : Nat) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w))
      ({allOnes n} : Set (BitString n))ᶜ t x ≤
    (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t := by
  classical
  have htail := proposed_rlsOneMax_finiteSurvival_couponBound hn x t
  -- One-bit elitist selection depends only on whether the flipped bit is zero.
  -- Identical kernels yield identical killed survival recursions.
  simpa only [candidate_rls_linear_transition_eq_oneMax hn w hw,
    ← oneMaxTarget_eq_singleton n] using htail

end ECRuntime
