import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: all finite polynomial moment tails of the coupon process and
strictly monotone RLS agree, using the *certified* signed-weight transfer.
This is a finite-time result; no infinite-series interchange is asserted. -/

/-- Every finite survival sum weighted by successive power increments
transfers exactly from direct coupon sampling to strict-monotone RLS. -/
theorem proposed_couponProcess_arbitraryPowerIncrementSurvival_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon exponent : Nat)
    (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      (((t + 1 : Nat) : Real) ^ (exponent + 1) -
          (t : Real) ^ (exponent + 1)) *
        finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x)) =
    (Finset.sum (Finset.range horizon) (fun t =>
      (((t + 1 : Nat) : Real) ^ (exponent + 1) -
          (t : Real) ^ (exponent + 1)) *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x)) := by
  exact proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon
    (fun t => (((t + 1 : Nat) : Real) ^ (exponent + 1) -
      (t : Real) ^ (exponent + 1))) x

end ECRuntime
