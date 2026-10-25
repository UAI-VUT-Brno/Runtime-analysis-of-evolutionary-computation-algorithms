import ECRuntime.RandomStakeCouponWeightedSurvivalTransfer
import Mathlib

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P02: finite algebraic central-second-moment functional.  The expression
is *defined* by survival masses.  Identifying it with the variance of a
stopping time requires the separate absorbing-target first-hitting theorem;
we do not silently impose such an identification for arbitrary targets. -/

/-- A central second-moment *survival functional* is invariant between
coupon sampling and strictly monotone RLS at every finite horizon. -/
theorem proposed_couponProcess_finiteSurvivalCentralSecond_eq_RLS
    {n : Nat} (hn : 0 < n)
    (fitness : BitString n → Real)
    (hf : CandidateCoordinateStrictMonotonicity fitness)
    (target : Set (BitString n)) (horizon : Nat) (x : BitString n) :
    (Finset.sum (Finset.range horizon) (fun t =>
      ((2 * t + 1 : Nat) : Real) *
        finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x) -
      (Finset.sum (Finset.range horizon) (fun t =>
        finiteLevelSurvival (randomStakeCouponTransition hn) targetᶜ t x)) ^ 2) =
    (Finset.sum (Finset.range horizon) (fun t =>
      ((2 * t + 1 : Nat) : Real) *
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x) -
      (Finset.sum (Finset.range horizon) (fun t =>
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition fitness)
          targetᶜ t x)) ^ 2) := by
  have hfirst := proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon (fun _ => (1 : Real)) x
  have hsecond := proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS
    hn fitness hf target horizon (fun t => ((2 * t + 1 : Nat) : Real)) x
  simp only [one_mul] at hfirst
  rw [hfirst, hsecond]

end ECRuntime
