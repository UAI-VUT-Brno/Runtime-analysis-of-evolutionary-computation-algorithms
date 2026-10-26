import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: arbitrary real discount factors (including signed factors)
transfer finite generating-polynomial survival functionals. -/

/-- Finite survival-generating polynomials agree between coupon and RLS. -/
theorem proposed_couponProcess_discountedSurvival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n -> Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (discount : Real) (x : BitString n) :
    (∑ t ∈ Finset.range horizon,
      discount ^ t * finiteLevelSurvival
        (randomStakeCouponTransition hn) targetᶜ t x) =
    (∑ t ∈ Finset.range horizon,
      discount ^ t * finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
        targetᶜ t x) := by
  exact proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon (fun t => discount ^ t) x

end ECRuntime
