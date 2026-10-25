import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: a discrete second-moment precursor. For nonnegative integer
hitting time T, E[min(T,H)^2] is the sum of (2t+1) times survival to t,
for t=0..H-1. The separate pathwise identity is a future target. -/

/-- Direct coupon and strict-monotone RLS have identical finite
second-moment survival functionals for arbitrary targets. -/
theorem proposed_couponProcess_arbitraryTarget_secondMomentSurvival_eq_strictMonotoneRLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat)
    (x : BitString n) :
    (∑ t ∈ Finset.range horizon,
      (((2 * t + 1 : Nat) : Real)) *
        finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x) =
    (∑ t ∈ Finset.range horizon,
      (((2 * t + 1 : Nat) : Real)) *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x) := by
  exact proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon (fun t => ((2 * t + 1 : Nat) : Real)) x

end ECRuntime
