import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: finite polynomial-moment survival invariance, uniform over all
integer powers. This is a direct specialization of the certified arbitrary
signed-weight transfer, not an assumption of stochastic independence. -/

/-- Every finite power-weighted survival functional is objective invariant. -/
theorem proposed_couponProcess_powerWeightedSurvival_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n -> Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon exponent : Nat)
    (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      ((t : Real) ^ exponent) * finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x)) =
    (Finset.sum (Finset.range horizon) (fun t =>
      ((t : Real) ^ exponent) * finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x)) := by
  exact proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon (fun t => (t : Real) ^ exponent) x

end ECRuntime
