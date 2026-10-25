import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: a third-moment analogue of the certified Stage 407 weighted
survival functional. The increment (t+1)^3-t^3 = 3t²+3t+1 is used here;
identification with literal E[min(T,H)^3] remains a separate task. -/

/-- Third-moment survival-weighted finite sums agree for coupon and RLS. -/
theorem proposed_couponProcess_thirdMomentSurvival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (x : BitString n) :
    (∑ t ∈ Finset.range horizon,
      ((3 * t * t + 3 * t + 1 : Nat) : Real) *
        finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x) =
    (∑ t ∈ Finset.range horizon,
      ((3 * t * t + 3 * t + 1 : Nat) : Real) *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x) := by
  exact proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon
    (fun t => ((3 * t * t + 3 * t + 1 : Nat) : Real)) x

end ECRuntime
